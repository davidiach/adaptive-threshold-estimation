"""Audit bounded global menu/DP/approximation output certificates and pruning primitives."""
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

PREFIX = "ThresholdHC.GlobalSelectionCertificates."
SOURCES = LEAN / "ThresholdHC/GlobalSelectionCertificates"
LOCK = SOURCES / "SPECIFICATION.json"
MODULES = ("Menu", "Trace")
EXACT_COUNT = 11
EXACT = """
open MeasureTheory
open scoped ENNReal BigOperators
open ThresholdHC.Tier6 ThresholdHC.FiniteLawCertificates
open ThresholdHC.DeterministicCertificates ThresholdHC.EntropyTail

example {n : ℕ} (d : Fin n → Gap) (w : Fin n → ℚ)
    (hw : ∀ i, 0 < w i) : (atomicMeasure d w).support = Set.range d :=
  atomic_support d w hw

example {n : ℕ} (s : Fin n → Bool) :
    ∀ i, 0 ≤ fractions s i ∧ fractions s i ≤ 1 :=
  fractions_valid s

example {n m : ℕ} (g w : Fin n → ℚ) (labels : Fin m → ℕ)
    (bands : Fin n → ℕ) (ρ B : ℚ) (hg : ∀ i, 0 < g i ∧ g i ≤ 1/2)
    (hw : ∀ i, 0 < w i) (hsum : ∑ i, w i = 1)
    (hl : Function.Injective labels) (hc : ∀ i, ∃ j, inBand (g i) (labels j) = true)
    (hb : ∀ i, inBand (g i) (bands i) = true)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4) (hB : 0 < B) :
    ∃ s : Fin n → Bool, suffixCheck g bands s = true ∧
      (selection (atomicMeasure (points g hg) w) (ρ:ℝ) (B:ℝ)).toReal =
        (objectiveExpr g w (fractions s) labels ρ B).eval :=
  suffix_attains g w labels bands ρ B hg hw hsum hl hc hb hρ hρ1 hB

example {n m : ℕ} (g w s : Fin n → ℚ) (labels : Fin m → ℕ)
    (ρ B : ℚ) (hg : ∀ i, 0 < g i ∧ g i ≤ 1/2) (hw : ∀ i, 0 ≤ w i)
    (hs : ∀ i, 0 ≤ s i ∧ s i ≤ 1) (hρ : 0 ≤ ρ) (hB : 0 < B)
    (hl : Function.Injective labels) (hc : ∀ i, ∃ j, inBand (g i) (labels j) = true) :
    (selection (atomicMeasure (points g hg) w) (ρ:ℝ) (B:ℝ)).toReal ≤
      (objectiveExpr g w s labels ρ B).eval :=
  selection_le_expr g w s labels ρ B hg hw hs hρ hB hl hc

example {α : Type*} (valid : α → Prop) (J : α → ℝ) (K : ℝ)
    (candidates : List α) (witness : α) (lower upper : ℚ)
    (hattains : ∃ s, valid s ∧ K = J s)
    (hcomplete : ∀ s, valid s → s ∈ candidates)
    (hlower : ∀ s ∈ candidates, (lower:ℝ) ≤ J s)
    (hfeasible : K ≤ J witness) (hupper : J witness ≤ (upper:ℝ)) :
    (lower:ℝ) ≤ K ∧ K ≤ J witness ∧ J witness ≤ (upper:ℝ) :=
  global_enclosure valid J K candidates witness lower upper hattains hcomplete hlower hfeasible hupper

example {α : Type*} (valid : α → Prop) (J : α → ℝ) (K : ℝ)
    (candidates : List α) (witness : α)
    (hattains : ∃ s, valid s ∧ K = J s)
    (hcomplete : ∀ s, valid s → s ∈ candidates)
    (hminimal : ∀ s ∈ candidates, J witness ≤ J s) (hfeasible : K ≤ J witness) :
    J witness = K :=
  global_optimality valid J K candidates witness hattains hcomplete hminimal hfeasible

example {K J : ℝ} {lo hi ε : ℚ}
    (hε : 0 ≤ ε) (h : (lo:ℝ) ≤ K ∧ K ≤ J ∧ J ≤ (hi:ℝ))
    (hstop : hi ≤ (1+ε)*lo) : J ≤ (1+(ε:ℝ))*K :=
  relative_certificate hε h hstop

example {f s g t B : ℚ} (hB : 0 < B) (h : savingLE f s g t B = true) :
    (f:ℝ)+(s:ℝ)/Real.sqrt (B:ℝ) ≤ (g:ℝ)+(t:ℝ)/Real.sqrt (B:ℝ) :=
  savingLE_sound hB h

example {n : ℕ} {κ : Type*} [DecidableEq κ]
    (key : (Fin n → Bool) → κ) (f t : (Fin n → Bool) → ℚ) (B : ℚ) (hB : 0 < B)
    (previous options kept : List (Fin n → Bool))
    (h : stageCheck key f t B previous options kept = true) :
    kept.Nodup ∧ (kept.map key).Nodup ∧
    (∀ s ∈ kept, s ∈ extendMasks previous options) ∧
    ∀ s ∈ extendMasks previous options, ∃ u ∈ kept,
      key s = key u ∧ (f s:ℝ)+(t s:ℝ)/Real.sqrt (B:ℝ) ≤
        (f u:ℝ)+(t u:ℝ)/Real.sqrt (B:ℝ) :=
  stageCheck_sound key f t B hB previous options kept h

example {n : ℕ} {κ : Type*} [DecidableEq κ]
    (key : (Fin n → Bool) → κ) (f t : (Fin n → Bool) → ℚ) (B : ℚ)
    (previous : List (Fin n → Bool)) (menus stages : List (List (Fin n → Bool)))
    (h : runCheck key f t B previous menus stages = true) : menus.length = stages.length :=
  runCheck_lengths key f t B previous menus stages h

example {r x y : ℚ} {M : ℕ} (hr : 0 < r) (hM : 0 < M)
    (hx : 0 ≤ x) (hy : 0 ≤ y)
    (he : ThresholdHC.FiniteSelectionApproximation.rationalKey r M x =
      ThresholdHC.FiniteSelectionApproximation.rationalKey r M y) :
    ThresholdHC.SelectionApproximation.Close (1+1/(M:ℝ)) (x:ℝ) (y:ℝ) :=
  rational_same_cell hr hM hx hy he

"""


def protected_sources() -> set[Path]:
    return project_dependencies([SOURCES / "Trace.lean"]) | {
        LEAN / "lean-toolchain", LEAN / "lake-manifest.json", LEAN / "lakefile.toml",
    }


def audit_inputs() -> set[Path]:
    return protected_sources() | {LOCK, Path(__file__).resolve(),
        ROOT / "tools/verify_blind_upper_components.py", ROOT / "tools/verify_tier6.py",
        ROOT / "tools/test_global_selection_certificates_audit.py",
        ROOT / "toolkit/tests/test_global_selection_certificates.py"} | set(
            (ROOT / "toolkit/threshold_toolkit").glob("*.py"))


def input_hashes() -> dict[str, str]:
    return {p.relative_to(ROOT).as_posix(): sha(p) for p in sorted(audit_inputs())}


def audit_input() -> tuple[str, set[str]]:
    lock = json.loads(LOCK.read_text(encoding="utf-8"))
    actual = {p.relative_to(ROOT).as_posix(): sha(p) for p in sorted(protected_sources())}
    if lock.get("sha256") != actual:
        raise ValueError("Changed global selection specification or dependency")
    if {p.stem for p in SOURCES.glob("*.lean")} != set(MODULES):
        raise ValueError("Unregistered or missing global selection module")
    roots = set()
    for path in project_dependencies([SOURCES / "Trace.lean"]):
        source = strip_comments(path.read_text(encoding="utf-8"))
        if FORBIDDEN.search(source):
            raise ValueError("Forbidden proof escape in " + str(path))
        if path.parent == SOURCES:
            for name in registered_names(source):
                root = PREFIX+name
                if root in roots:
                    raise ValueError("Duplicate declaration root: " + root)
                roots.add(root)
    required = {'selection_le_expr', 'global_optimality', 'savingLE_sound', 'relative_certificate', 'stageCheck_sound', 'rational_same_cell', 'fractions_valid', 'global_enclosure', 'atomic_support', 'suffix_attains', 'runCheck_lengths'}
    if not {PREFIX+n for n in required} <= roots:
        raise ValueError("Missing global selection audit target")
    source = "\n".join(["import "+PREFIX+"Trace", "open "+PREFIX[:-1], EXACT.strip(),
                        *["#print axioms "+r for r in sorted(roots)]])+"\n"
    if FORBIDDEN.search(strip_comments(source)):
        raise ValueError("Forbidden proof escape in generated audit")
    return source, roots


def sample_requests():
    sys.path.insert(0, str(ROOT / "toolkit"))
    from threshold_toolkit.global_selection_certificates import Request
    single = ((F(1,2),F(1)),)
    same = ((F(1,3),F(1,2)),(F(3,8),F(1,2)))
    mixed = ((F(1,64),F(1,128)),(F(1,8),F(1,4)),(F(1,2),F(95,128)))
    def req(op, atoms=single, **kw):
        return Request(op, atoms, bits=16, log_terms=4, **kw)
    return [req("exhaustive", budget=F(1)), req("exhaustive", budget=F(1024)),
            req("dp", budget=F(1024)), req("approximate", budget=F(1024)),
            req("exhaustive", same, budget=F(256)), req("dp", same, budget=F(256)),
            req("approximate", same, budget=F(256), epsilon=F(1,2)),
            req("exhaustive", mixed, budget=F(1024)), req("dp", mixed, budget=F(1024)),
            req("approximate", mixed, budget=F(1024), epsilon=F(1,4)),
            req("dp", same, budget=F(1))]


def concrete_checks(out: Path) -> dict:
    import copy
    sys.path.insert(0, str(ROOT / "toolkit"))
    from threshold_toolkit.global_selection_certificates import produce, verify, proof_source, VerificationError
    samples = sample_requests()
    accepted = []
    for i, req in enumerate(samples):
        certificate = produce(req)
        result = verify(req, certificate, lean_dir=LEAN, timeout=600)
        (out / f"sample-{i}.json").write_text(json.dumps(certificate, indent=2)+"\n", encoding="utf-8")
        (out / f"sample-{i}.lean").write_text(result.pop("proof_source"), encoding="utf-8")
        (out / f"sample-{i}.log").write_text(result.pop("kernel_report"), encoding="utf-8")
        accepted.append(result)
        print("Kernel accepted sample", i, req.operation, flush=True)
    bad = [(1, "upper", "0"), (1, "lower", "1/4"),
           (2, "selected", [False]), (3, "epsilon", "1/2"),
           (3, "witness_value", dict(lower="0",upper="0")),
           (4, "menu", [0,3]), (4, "menu", [0,2,2]),
           (4, "suffix_count", 2),
           (2, "output", dict(value=dict(lower="0",upper="1/4"), selected=[False],
                              suffix_count=2, optimality_proved=True)),
           (3, "value", dict(lower="0",upper="1/4")),
           (10, "selected", [True,False])]
    rejected = []
    for idx, key, value in bad:
        req = samples[idx]
        cert = copy.deepcopy(produce(req))
        if key == "menu":
            cert[key] = value
            cert["output"]["suffix_count"] = len(value)
        elif key == "output":
            cert[key] = value
        elif key in ("lower", "upper"):
            cert["output"]["value"][key] = value
            if key == "upper":
                cert["output"]["value"]["lower"] = "0"
            else:
                cert["output"]["value"]["upper"] = "1/4"
        else:
            cert["output"][key] = value
        try:
            verify(req, cert, lean_dir=LEAN, timeout=600)
        except VerificationError as exc:
            if str(exc) != "Lean rejected the certificate proof.":
                raise
            report = exc.kernel_report
            if "error:" not in report or not any(s in report for s in ("unsolved goals", "decide", "False")):
                raise ValueError("Rejection did not identify a false mathematical obligation") from exc
            i = len(rejected)
            (out / f"rejected-{i}.lean").write_text(proof_source(req, cert), encoding="utf-8")
            (out / f"rejected-{i}.log").write_text(report, encoding="utf-8")
            rejected.append(dict(operation=req.operation, changed_field=key, certificate=cert))
            print("Kernel rejected", i, key, flush=True)
        else:
            raise ValueError("Unsound concrete certificate accepted")
    return dict(accepted=accepted, rejected=rejected,
                regression_scope="bounded actual output evidence, not universal producer correctness")


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
    out = (args.output_dir or ROOT / ".runtime/global-selection-certificates" /
           datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")).resolve()
    out.mkdir(parents=True, exist_ok=False)
    (out / "audit.lean").write_text(source, encoding="utf-8")
    if not args.no_build:
        with (out / "build.log").open("w", encoding="utf-8") as log:
            subprocess.run(["lake", "build", PREFIX+"Trace"], cwd=LEAN, check=True,
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
                  bounded_global_output_contracts_verified=True, exact_optimality_claims_verified=True,
                  relative_approximation_claims_verified=True, pruning_primitives_verified=True,
                  concrete_output_certificates=len(samples["accepted"]), adversarial_rejections=len(samples["rejected"]),
                  all_producer_inputs_verified=False, python_execution_verified=False,
                  internal_solver_traces_verified=False, concrete_planners_verified=False,
                  polynomial_verification_cost_verified=False, bit_complexity_verified=False,
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
