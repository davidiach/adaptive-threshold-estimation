"""Audit finite-law measure bridges and actual objective/oracle output certificates."""
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

PREFIX = "ThresholdHC.FiniteLawCertificates."
SOURCES = LEAN / "ThresholdHC/FiniteLawCertificates"
LOCK = SOURCES / "SPECIFICATION.json"
MODULES = ("Atomic", "Quantile", "Data", "Objective", "Oracles")
EXACT_COUNT = 10
EXACT = """
open MeasureTheory
open scoped ENNReal BigOperators
open ThresholdHC.Tier6 ThresholdHC.DeterministicCertificates

example {n : ℕ} (d : Fin n → Gap) (w : Fin n → ℚ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) : IsProbabilityMeasure (atomicMeasure d w) :=
  atomicMeasure_probability d w hw hs

example {n : ℕ} (d : Fin n → Gap) (w : Fin n → ℚ) (hw : ∀ i, 0 ≤ w i) (f : Gap → ℝ) :
    (∫ x, f x ∂atomicMeasure d w) = ∑ i, (w i:ℝ)*f (d i) := integral_atomic d w hw f

example {n : ℕ} (d : Fin n → Gap) (w s : Fin n → ℚ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) {ρ t : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (r : ℚ) (hr : r ≤ 1)
    (hbelow : (∑ i, if (d i:ℝ) < t then (w i:ℝ) else 0) < ρ)
    (habove : ρ ≤ ∑ i, if (d i:ℝ) ≤ t then (w i:ℝ) else 0)
    (hb : (r:ℝ) = (ρ-(∑ i, if (d i:ℝ) < t then (w i:ℝ) else 0)) /
      (∑ i, if (d i:ℝ) = t then (w i:ℝ) else 0))
    (hs : ∀ i, s i = if (d i:ℝ) < t then 0 else if (d i:ℝ) = t then 1-r else 1) :
    ThresholdHC.EntropyTailQuantile.quantileCore (atomicMeasure d w) ρ =
      atomicMeasure d (fun i => w i*s i) :=
  quantileCore_atomic d w s hw hsum hρ hρ1 r hr hbelow habove hb hs

example {n m : ℕ} (g w s : Fin n → ℚ) (labels : Fin m → ℕ) (ρ B : ℚ)
    (hg : ∀ i, 0 < g i ∧ g i ≤ 1/2) (hw : ∀ i, 0 ≤ w i)
    (hs : ∀ i, 0 ≤ s i ∧ s i ≤ 1) (hρ : 0 ≤ ρ) (hB : 0 < B)
    (hi : Function.Injective labels) (hc : ∀ i, ∃ j, inBand (g i) (labels j) = true) :
    min (ENNReal.ofReal (ρ:ℝ)) (ThresholdHC.EntropyTail.selectionObjective
      (atomicMeasure (points g hg) w) (ρ:ℝ) (B:ℝ)
      (atomicMeasure (points g hg) (fun i => w i*s i))) =
      ENNReal.ofReal (objectiveExpr g w s labels ρ B).eval :=
  capped_objective_eq g w s labels ρ B hg hw hs hρ hB hi hc

example {n m : ℕ} (g w s : Fin n → ℚ) (labels : Fin m → ℕ) (ρ B : ℚ)
    (hg : ∀ i, 0 < g i ∧ g i ≤ 1/2) (hw : ∀ i, 0 ≤ w i)
    (hs : ∀ i, 0 ≤ s i ∧ s i ≤ 1) (hρ : 0 ≤ ρ) (hB : 0 < B)
    (hi : Function.Injective labels) (hc : ∀ i, ∃ j, inBand (g i) (labels j) = true)
    {claimed : Interval} {c : Evidence}
    (h : accepted (objectiveExpr g w s labels ρ B) claimed c = true) :
    Contains claimed (min (ENNReal.ofReal (ρ:ℝ)) (ThresholdHC.EntropyTail.selectionObjective
      (atomicMeasure (points g hg) w) (ρ:ℝ) (B:ℝ)
      (atomicMeasure (points g hg) (fun i => w i*s i)))).toReal :=
  objective_accepted_sound g w s labels ρ B hg hw hs hρ hB hi hc h

example {n m : ℕ} (g w s : Fin n → ℚ) (labels : Fin m → ℕ) (ρ B : ℚ)
    (hg : ∀ i, 0 < g i ∧ g i ≤ 1/2) (hw : ∀ i, 0 ≤ w i)
    (hs : ∀ i, 0 ≤ s i ∧ s i ≤ 1) (hρ : 0 ≤ ρ) (hB : 0 < B)
    (hi : Function.Injective labels) (hc : ∀ i, ∃ j, inBand (g i) (labels j) = true)
    {claimed : Interval} {c : Evidence}
    (h : accepted (objectiveExpr g w s labels ρ B) claimed c = true) :
    (ThresholdHC.EntropyTail.selection (atomicMeasure (points g hg) w) (ρ:ℝ) (B:ℝ)).toReal ≤
      (claimed.upper:ℝ) := selection_upper g w s labels ρ B hg hw hs hρ hB hi hc h

example {n : ℕ} (g w s : Fin n → ℚ) (B : ℚ)
    (hg : ∀ i, 0 < g i ∧ g i ≤ 1/2) (hw : ∀ i, 0 ≤ w i)
    (hs : ∀ i, 0 ≤ s i ∧ s i ≤ 1) :
    (atomicMeasure (points g hg) w-atomicMeasure (points g hg) (fun i => w i*s i)).restrict
      {x : Gap | 1 ≤ (B:ℝ)*(x:ℝ)^2} = atomicMeasure (points g hg) (tailWeights g w s B) :=
  tailMeasure_eq g w s B hg hw hs

example {n : ℕ} (g w : Fin n → ℚ) (hg : ∀ i, 0 < g i ∧ g i ≤ 1/2)
    (hw : ∀ i, 0 ≤ w i) (heads tails : ℕ) :
    nullPrefixIntegral (atomicMeasure (points g hg) w) heads tails =
      (nullPrefixValue g w heads tails:ℝ) := nullPrefix_eq g w hg hw heads tails

example {n : ℕ} (g v : Fin n → ℚ) (M : ℚ) (hg : ∀ i, 0 < g i ∧ g i ≤ 1/2)
    (hv : ∀ i, 0 ≤ v i) :
    (∫ x : Gap, min 1 (1/((M:ℝ)*(x:ℝ)^2)^2) ∂atomicMeasure (points g hg) v) =
      (errorValue g v M:ℝ) := errorIntegral_eq g v M hg hv

example {n : ℕ} (g v : Fin n → ℚ) (M : ℚ) (hg : ∀ i, 0 < g i ∧ g i ≤ 1/2)
    (hv : ∀ i, 0 ≤ v i) {claimed : Interval} {c : Evidence}
    (h : accepted (tailWorkExpr g v M) claimed c = true) :
    Contains claimed (tailWorkIntegral (atomicMeasure (points g hg) v) (M:ℝ)) :=
  tailWork_accepted_sound g v M hg hv h
"""


def protected_sources() -> set[Path]:
    return project_dependencies([SOURCES / "Oracles.lean"]) | {
        LEAN / "lean-toolchain", LEAN / "lake-manifest.json", LEAN / "lakefile.toml",
    }


def audit_inputs() -> set[Path]:
    return protected_sources() | {LOCK, Path(__file__).resolve(),
        ROOT / "tools/verify_blind_upper_components.py", ROOT / "tools/verify_tier6.py",
        ROOT / "tools/test_finite_law_certificates_audit.py",
        ROOT / "toolkit/tests/test_finite_law_certificates.py"} | set(
            (ROOT / "toolkit/threshold_toolkit").glob("*.py"))


def input_hashes() -> dict[str, str]:
    return {p.relative_to(ROOT).as_posix(): sha(p) for p in sorted(audit_inputs())}


def audit_input() -> tuple[str, set[str]]:
    lock = json.loads(LOCK.read_text(encoding="utf-8"))
    actual = {p.relative_to(ROOT).as_posix(): sha(p) for p in sorted(protected_sources())}
    if lock.get("sha256") != actual:
        raise ValueError("Changed finite-law specification or dependency")
    if {p.stem for p in SOURCES.glob("*.lean")} != set(MODULES):
        raise ValueError("Unregistered or missing finite-law module")
    roots = set()
    for path in project_dependencies([SOURCES / "Oracles.lean"]):
        source = strip_comments(path.read_text(encoding="utf-8"))
        if FORBIDDEN.search(source):
            raise ValueError("Forbidden proof escape in " + str(path))
        if path.parent == SOURCES:
            for name in registered_names(source):
                root = PREFIX+name
                if root in roots:
                    raise ValueError("Duplicate declaration root: " + root)
                roots.add(root)
    required = {"atomicMeasure_probability", "integral_atomic", "quantileCore_atomic", "gamma_rational",
                "capped_objective_eq", "objective_accepted_sound", "selection_upper", "tailMeasure_eq",
                "unresolvedMeasure_eq", "resolvedMeasure_eq", "nullPrefix_eq", "inverseIntegral_eq",
                "errorIntegral_eq", "tailWork_accepted_sound"}
    if not {PREFIX+n for n in required} <= roots:
        raise ValueError("Missing finite-law audit target")
    source = "\n".join(["import "+PREFIX+"Oracles", "open "+PREFIX[:-1], EXACT.strip(),
                        *["#print axioms "+r for r in sorted(roots)]])+"\n"
    if FORBIDDEN.search(strip_comments(source)):
        raise ValueError("Forbidden proof escape in generated audit")
    return source, roots


def concrete_checks(out: Path) -> dict:
    import copy
    sys.path.insert(0, str(ROOT / "toolkit"))
    from threshold_toolkit.finite_law_certificates import Request, produce, verify, proof_source, VerificationError
    single = ((F(1,2), F(1)),)
    mixed = ((F(1,8),F(1,3)),(F(1,2),F(2,3)))
    crossing = ((F(1,16),F(1,8)),(F(1,8),F(1,8)),(F(1,2),F(3,4)))
    samples = [Request("objective", single, selected=(F(0),), budget=F(1024), bits=16, log_terms=4),
               Request("objective", single, selected=(F(1),), budget=F(4096), bits=16, log_terms=4),
               Request("objective", mixed, selected=(F(1,2),F(1,4)), budget=F(256), bits=16, log_terms=4),
               Request("prefix", single),
               Request("prefix", mixed, heads=2, tails=3),
               Request("oracle", mixed, budget=F(256), cap=1024, bits=16, log_terms=4),
               Request("oracle", crossing, budget=F(64), cap=1, bits=16, log_terms=4),
               Request("oracle", crossing, budget=F(64), cap=1024, bits=16, log_terms=4)]
    accepted = []
    for i, req in enumerate(samples):
        certificate = produce(req)
        result = verify(req, certificate, lean_dir=LEAN, timeout=240)
        (out / f"sample-{i}.json").write_text(json.dumps(certificate, indent=2)+"\n", encoding="utf-8")
        (out / f"sample-{i}.lean").write_text(result.pop("proof_source"), encoding="utf-8")
        (out / f"sample-{i}.log").write_text(result.pop("kernel_report"), encoding="utf-8")
        accepted.append(result)
        print("Kernel accepted sample", i, req.operation, flush=True)
    bad = [(samples[2], "output", dict(lower="0",upper="0")),
           (samples[4], "output", dict(lower="0",upper="0")),
           (samples[5], "core", ["1","1"]),
           (samples[5], "band_costs", {"0":"0","2":"0"}),
           (samples[7], "unresolved_mass", "0"),
           (samples[7], "tail_inverse", "0"),
           (samples[7], "resolved_error", "0"),
           (samples[7], "tail_work", "0")]
    rejected = []
    for req, key, value in bad:
        cert = copy.deepcopy(produce(req))
        if key == "output":
            cert[key] = value
        else:
            cert["output"][key] = value
        try:
            verify(req, cert, lean_dir=LEAN, timeout=240)
        except VerificationError as exc:
            if str(exc) != "Lean rejected the certificate proof.":
                raise
            report = exc.kernel_report
            if "unsolved goals" not in report or "⊢ False" not in report:
                raise ValueError("Rejection did not reduce an invalid numerical claim to False") from exc
            i = len(rejected)
            (out / f"rejected-{i}.lean").write_text(proof_source(req, cert), encoding="utf-8")
            (out / f"rejected-{i}.log").write_text(report, encoding="utf-8")
            rejected.append(dict(operation=req.operation, changed_field=key, output=cert["output"]))
            print("Kernel rejected", i, key, flush=True)
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
    out = (args.output_dir or ROOT / ".runtime/finite-law-certificates" /
           datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")).resolve()
    out.mkdir(parents=True, exist_ok=False)
    (out / "audit.lean").write_text(source, encoding="utf-8")
    if not args.no_build:
        with (out / "build.log").open("w", encoding="utf-8") as log:
            subprocess.run(["lake", "build", PREFIX+"Oracles"], cwd=LEAN, check=True,
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
                  finite_measure_bridges_verified=True, feasible_objective_semantics_verified=True,
                  finite_oracle_output_contracts_verified=True,
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
