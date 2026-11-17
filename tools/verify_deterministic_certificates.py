"""Audit rational certificate soundness and check actual toolkit outputs in Lean."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
from fractions import Fraction as F
import json
from pathlib import Path
import subprocess
import sys

from verify_blind_upper_components import (
    FORBIDDEN, LEAN, ROOT, project_dependencies, registered_names, sha,
    strip_comments, validate_reports,
)

PREFIX = "ThresholdHC.DeterministicCertificates."
SOURCES = LEAN / "ThresholdHC/DeterministicCertificates"
LOCK = SOURCES / "SPECIFICATION.json"
MODULES = ("Intervals", "Logarithm", "Checker", "Entropy")
EXACT_COUNT = 8
EXACT = """
example {input output : Interval} {x : ℝ}
    (h : sqrtCheck input output = true) (hi : Contains input x) :
    (output.lower:ℝ) ≤ Real.sqrt x ∧ Real.sqrt x ≤ (output.upper:ℝ) := sqrtCheck_sound h hi

example {x tolerance : ℚ} {output : Interval}
    (h : sqrtPrecisionCheck x tolerance output = true) (hx : 0 ≤ x) :
    (output.upper-output.lower:ℝ) ≤ (tolerance:ℝ)*min 1 (Real.sqrt (x:ℝ)) :=
  sqrtPrecisionCheck_sound h hx

example {x : ℚ} (hx : 1 ≤ x) (n : ℕ) :
    ((unitLog x n).lower:ℝ) ≤ Real.log (x:ℝ) ∧
      Real.log (x:ℝ) ≤ ((unitLog x n).upper:ℝ) := unitLog_sound hx n

example {input output : Interval} {lower upper : LogWitness} {x : ℝ}
    (h : logCheck input output lower upper = true) (hi : Contains input x) :
    (output.lower:ℝ) ≤ Real.log x ∧ Real.log x ≤ (output.upper:ℝ) := logCheck_sound h hi

example (e : Expr) (c : Evidence) (h : check e c = true) :
    (c.bounds.lower:ℝ) ≤ e.eval ∧ e.eval ≤ (c.bounds.upper:ℝ) := check_sound e c h

example {e : Expr} {claimed : Interval} {c : Evidence}
    (h : accepted e claimed c = true) :
    (claimed.lower:ℝ) ≤ e.eval ∧ e.eval ≤ (claimed.upper:ℝ) := accepted_sound h

example {n : ℕ} (a : Fin n → ℚ) (ha : ∀ i, 0 ≤ a i) :
    (entropyExpr a).eval =
      ThresholdHC.EntropyTailQuantile.costEntropy (fun i => (a i:ℝ)) := entropyExpr_eval a ha

example {n : ℕ} (a : Fin n → ℚ) (ha : ∀ i, 0 ≤ a i)
    {claimed : Interval} {c : Evidence} (h : accepted (entropyExpr a) claimed c = true) :
    (claimed.lower:ℝ) ≤ ThresholdHC.EntropyTailQuantile.costEntropy (fun i => (a i:ℝ)) ∧
      ThresholdHC.EntropyTailQuantile.costEntropy (fun i => (a i:ℝ)) ≤ (claimed.upper:ℝ) :=
  entropy_accepted_sound a ha h
"""


def protected_sources() -> set[Path]:
    return project_dependencies([SOURCES / "Entropy.lean"]) | {
        LEAN / "lean-toolchain", LEAN / "lake-manifest.json", LEAN / "lakefile.toml",
    }


def audit_inputs() -> set[Path]:
    return protected_sources() | {LOCK, Path(__file__).resolve(),
        ROOT / "tools/verify_blind_upper_components.py", ROOT / "tools/verify_tier6.py",
        ROOT / "tools/test_deterministic_certificates_audit.py",
        ROOT / "toolkit/tests/test_deterministic_certificates.py"} | set(
            (ROOT / "toolkit/threshold_toolkit").glob("*.py"))


def input_hashes() -> dict[str, str]:
    return {p.relative_to(ROOT).as_posix(): sha(p) for p in sorted(audit_inputs())}


def audit_input() -> tuple[str, set[str]]:
    lock = json.loads(LOCK.read_text(encoding="utf-8"))
    actual = {p.relative_to(ROOT).as_posix(): sha(p) for p in sorted(protected_sources())}
    if lock.get("sha256") != actual:
        raise ValueError("Changed deterministic-checker specification or dependency")
    if {p.stem for p in SOURCES.glob("*.lean")} != set(MODULES):
        raise ValueError("Unregistered or missing deterministic-checker module")
    roots = set()
    for path in project_dependencies([SOURCES / "Entropy.lean"]):
        source = strip_comments(path.read_text(encoding="utf-8"))
        if FORBIDDEN.search(source):
            raise ValueError("Forbidden proof escape in " + str(path))
        if path.parent == SOURCES:
            for name in registered_names(source):
                root = PREFIX+name
                if root in roots:
                    raise ValueError("Duplicate declaration root: " + root)
                roots.add(root)
    required = {"sqrtCheck_sound", "sqrtPrecisionCheck_sound", "unitLog_sound", "logCheck_sound",
                "check_sound", "accepted_sound", "entropyExpr_eval", "entropy_accepted_sound"}
    if not {PREFIX+n for n in required} <= roots:
        raise ValueError("Missing deterministic-checker audit target")
    source = "\n".join(["import "+PREFIX+"Entropy", "open "+PREFIX[:-1], EXACT.strip(),
                        *["#print axioms "+r for r in sorted(roots)]])+"\n"
    if FORBIDDEN.search(strip_comments(source)):
        raise ValueError("Forbidden proof escape in generated audit")
    return source, roots


def concrete_checks(out: Path) -> dict:
    sys.path.insert(0, str(ROOT / "toolkit"))
    from threshold_toolkit.deterministic_certificates import Request, produce, verify, proof_source, VerificationError
    samples = [Request("sqrt", (F(0),)), Request("sqrt", (F(3, 10**80),)),
               Request("sqrt", (F(9, 16),)), Request("log", (F(1, 8),), log_terms=4),
               Request("log", (F(3),)), Request("entropy", ()),
               Request("entropy", (F(0), F(0))),
               Request("entropy", (F(1), F(0), F(2)), log_terms=4)]
    accepted = []
    for i, req in enumerate(samples):
        certificate = produce(req)
        result = verify(req, certificate, lean_dir=LEAN, timeout=180)
        (out / f"sample-{i}.json").write_text(json.dumps(certificate, indent=2)+"\n", encoding="utf-8")
        (out / f"sample-{i}.lean").write_text(result.pop("proof_source"), encoding="utf-8")
        (out / f"sample-{i}.log").write_text(result.pop("kernel_report"), encoding="utf-8")
        accepted.append(result)
        print("Kernel accepted sample", i, req.operation, flush=True)
    rejected = []
    for op, vals, endpoints in [("sqrt", (F(2),), ("3", "3")),
                                ("sqrt", (F(2),), ("0", "2")),
                                ("log", (F(1, 8),), ("-4", "-3")),
                                ("entropy", (F(1), F(2)), ("0", "0"))]:
        req = Request(op, vals, bits=16, log_terms=4)
        cert = produce(req)
        cert["output"] = dict(zip(("lower", "upper"), endpoints))
        try:
            verify(req, cert, lean_dir=LEAN, timeout=180)
        except VerificationError as exc:
            # Timeout/unavailable Lean is not evidence that the bad bound failed.
            if str(exc) != "Lean rejected the certificate proof.":
                raise
            report = exc.kernel_report
            if "unsolved goals" not in report or "⊢ False" not in report:
                raise ValueError("Rejection did not reduce the invalid bound to False") from exc
            i = len(rejected)
            (out / f"rejected-{i}.lean").write_text(proof_source(req, cert), encoding="utf-8")
            (out / f"rejected-{i}.log").write_text(report, encoding="utf-8")
            rejected.append(dict(operation=op, output=cert["output"]))
        else:
            raise ValueError("Unsound concrete certificate accepted")
    return dict(accepted=accepted, rejected=rejected,
                regression_scope="finite execution evidence, not universal producer correctness")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--no-build", action="store_true", help="Use only after a complete current build")
    parser.add_argument("--output-dir", type=Path)
    args = parser.parse_args()
    source, roots = audit_input()
    initial_hashes = input_hashes()
    def command(*cmd: str) -> str:
        return subprocess.check_output(cmd, cwd=ROOT, text=True, encoding="utf-8").strip()
    initial_commit = command("git", "rev-parse", "HEAD")
    out = (args.output_dir or ROOT / ".runtime/deterministic-certificates" /
           datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")).resolve()
    out.mkdir(parents=True, exist_ok=False)
    (out / "audit.lean").write_text(source, encoding="utf-8")
    if not args.no_build:
        with (out / "build.log").open("w", encoding="utf-8") as log:
            subprocess.run(["lake", "build", PREFIX+"Entropy"], cwd=LEAN, check=True,
                           stdout=log, stderr=subprocess.STDOUT)
    run = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=LEAN, input=source,
                         text=True, encoding="utf-8", capture_output=True)
    report = run.stdout+run.stderr
    (out / "audit.log").write_text(report, encoding="utf-8")
    validate_reports(report, run.returncode, roots)
    # Resolve the toolchain directly: the older shared helper assumes Unix
    # printenv and an extensionless executable. This also works on Windows.
    sysroot = Path(subprocess.check_output(["lake", "env", "lean", "--print-prefix"],
                                          cwd=LEAN, text=True, encoding="utf-8").strip())
    checker = sysroot / "bin" / ("leanchecker.exe" if (sysroot / "bin/leanchecker.exe").exists()
                                else "leanchecker")
    with (out / "kernel-replay.log").open("w", encoding="utf-8") as log:
        for module in MODULES:
            log.write(PREFIX+module+"\n")
            log.flush()
            subprocess.run(["lake", "env", str(checker), PREFIX+module], cwd=LEAN, check=True,
                           stdout=log, stderr=subprocess.STDOUT)
    samples = concrete_checks(out)
    (out / "samples.json").write_text(json.dumps(samples, indent=2)+"\n", encoding="utf-8")
    compiler_version = subprocess.check_output(["lake", "env", "lean", "--version"],
                                              cwd=LEAN, text=True, encoding="utf-8").strip()
    compiler_prefix = Path(subprocess.check_output(["lake", "env", "lean", "--print-prefix"],
                                                  cwd=LEAN, text=True, encoding="utf-8").strip())
    compiler = compiler_prefix / "bin" / ("lean.exe" if (compiler_prefix / "bin/lean.exe").exists() else "lean")
    pinned = (LEAN / "lean-toolchain").read_text(encoding="utf-8").strip().split(":v")[-1]
    if "version "+pinned+"," not in compiler_version:
        raise ValueError("Compiler differs from pinned toolchain")
    if input_hashes() != initial_hashes or command("git", "rev-parse", "HEAD") != initial_commit:
        raise ValueError("Audit inputs or checkpoint changed during verification")
    status = dict(valid=True, proof_commit=initial_commit,
                  worktree_status=command("git", "status", "--porcelain"),
                  exact_statements=EXACT_COUNT, transitive_reports=len(roots),
                  independent_kernel_replay_modules=[PREFIX+m for m in MODULES],
                  allowed_axioms=["propext", "Classical.choice", "Quot.sound"],
                  checker_soundness_verified=True, entropy_semantics_verified=True,
                  concrete_output_certificates=len(samples["accepted"]), adversarial_rejections=len(samples["rejected"]),
                  all_producer_inputs_verified=False, python_execution_verified=False,
                  global_selection_and_planners_verified=False, bit_complexity_verified=False,
                  build_skipped=args.no_build, external_compiled_cache_trusted=True,
                  compiler=dict(version=compiler_version, path=str(compiler), sha256=sha(compiler)),
                  source_sha256=initial_hashes,
                  kernel_checker_sha256=sha(checker),
                  artifact_sha256={p.name: sha(p) for p in sorted(out.iterdir()) if p.is_file()})
    (out / "status.json").write_text(json.dumps(status, indent=2)+"\n", encoding="utf-8")
    print(f"Verified {EXACT_COUNT} exact statements and {len(roots)} transitive axiom reports")
    print("Evidence:", out)


if __name__ == "__main__":
    main()
