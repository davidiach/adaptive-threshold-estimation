"""Audit zero-residual envelopes, rounding and conditional transfer output certificates."""
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

PREFIX = "ThresholdHC.EnvelopeTransferCertificates."
SOURCES = LEAN / "ThresholdHC/EnvelopeTransferCertificates"
LOCK = SOURCES / "SPECIFICATION.json"
MODULES = ("Envelope", "Rounding", "Transfer")
EXACT_COUNT = 12
EXACT = """
open MeasureTheory
open scoped ENNReal BigOperators
open ThresholdHC.Tier6 ThresholdHC.FiniteLawCertificates
open ThresholdHC.DeterministicCertificates ThresholdHC.ArbitraryLawAdaptation ThresholdHC.EntropyTail

example {n : ℕ} (z : ℚ) (d : Fin n → Gap) (w : Fin n → ℚ)
    (hz : 0 ≤ z) (hw : ∀ i, 0 ≤ w i) (hs : z+∑ i,w i=1) :
    IsProbabilityMeasure (extendedAtomic z d w) :=
  extendedAtomic_probability z d w hz hw hs

example {n : ℕ} (z : ℚ) (d : Fin n → Gap) (w : Fin n → ℚ) :
    extendedAtomic z d w {0} = ENNReal.ofReal (z:ℝ) :=
  extendedAtomic_zero z d w

example {n : ℕ} (z : ℚ) (d : Fin n → Gap) (w : Fin n → ℚ)
    (hz : 0 ≤ z) (hw : ∀ i, 0 ≤ w i) (f : ℝ → ℝ) :
    (∫ x, f x ∂extendedAtomic z d w) = (z:ℝ)*f 0 + ∑ i, (w i:ℝ)*f (d i) :=
  extended_integral z d w hz hw f

example {n : ℕ} (z : ℚ) (d : Fin n → Gap) (w : Fin n → ℚ)
    {ρ B : ℝ} (hρ : 0 < ρ) (hB : 0 < B) (hz : ρ ≤ (z:ℝ)) :
    zeroSelection (extendedAtomic z d w) ρ B = ENNReal.ofReal ρ :=
  fallback_selection z d w hρ hB hz

example {n : ℕ} (z : ℚ) (d : Fin n → Gap) (w : Fin n → ℚ)
    (hz : z < 1) :
    extendedAtomic z d w = zeroAtomLaw (z:ℝ) (atomicMeasure d (fun i => w i/(1-z))) :=
  normalized_identity z d w hz

example {n : ℕ} (z : ℚ) (d : Fin n → Gap) (w s : Fin n → ℚ)
    (hz : z < 1) {ρ : ℝ}
    (hcore : ThresholdHC.EntropyTailQuantile.quantileCore
      (atomicMeasure d (fun i => w i/(1-z))) ρ =
        atomicMeasure d (fun i => (w i/(1-z))*s i)) :
    ENNReal.ofReal (1-(z:ℝ)) • ThresholdHC.EntropyTailQuantile.quantileCore
      (atomicMeasure d (fun i => w i/(1-z))) ρ = atomicMeasure d (fun i => w i*s i) :=
  scaled_core z d w s hz hcore

example {n : ℕ} (c : Fin (n+1) → ℚ) (hc : Antitone c) :
    Antitone (extendCDF c) :=
  extendCDF_antitone c hc

example (pairs : List (Gap × Gap)) : Measurable (pointMap pairs) :=
  pointMap_measurable pairs

example (pairs : List (Gap × Gap)) {r : ℝ} (hr : 1 ≤ r)
    (hp : ∀ p ∈ pairs, (p.1:ℝ) ≤ (p.2:ℝ) ∧ (p.2:ℝ) ≤ r*(p.1:ℝ)) :
    ∀ x : Gap, (x:ℝ) ≤ (pointMap pairs x:ℝ) ∧ (pointMap pairs x:ℝ) ≤ r*(x:ℝ) :=
  pointMap_bounds pairs hr hp

example (pairs : List (Gap × Gap))
    (hp : ∀ p ∈ pairs, ∃ j, p.1 ∈ ThresholdHC.EntropyTail.band j ∧ p.2 ∈ ThresholdHC.EntropyTail.band j) :
    ∀ j, pointMap pairs ⁻¹' ThresholdHC.EntropyTail.band j = ThresholdHC.EntropyTail.band j :=
  pointMap_bands pairs hp

example {n m : ℕ} (e : Fin m → Gap) (w : Fin n → ℚ)
    (hw : ∀ i, 0 ≤ w i) (route : Fin n → Fin m) :
    atomicMeasure (fun i => e (route i)) w =
      atomicMeasure e (fun j => ∑ i, if route i=j then w i else 0) :=
  atomic_group e w hw route

example (μ μ₀ : Measure Gap) [IsProbabilityMeasure μ] [IsProbabilityMeasure μ₀]
    (T : Gap → Gap) (hm : Measurable T) (r η ρ B : ℚ) (hr : 1 ≤ r)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4) (hB : 0 < B)
    (hη : tvDist μ μ₀ / 2 ≤ (η:ℝ))
    (hd : ∀ d : Gap, (d:ℝ) ≤ (T d:ℝ) ∧ (T d:ℝ) ≤ (r:ℝ)*(d:ℝ))
    (hb : ∀ j, T ⁻¹' band j = band j)
    (input output : Interval) (hi : Contains input (selection (μ₀.map T) (ρ:ℝ) (B:ℝ)).toReal)
    (hc : transferCheck input output r η ρ = true) :
    Contains output (selection μ (ρ:ℝ) (B:ℝ)).toReal :=
  transfer_original μ μ₀ T hm r η ρ B hr hρ hρ1 hB hη hd hb input output hi hc

"""


def protected_sources() -> set[Path]:
    return project_dependencies([SOURCES / "Transfer.lean"]) | {
        LEAN / "lean-toolchain", LEAN / "lake-manifest.json", LEAN / "lakefile.toml",
    }


def audit_inputs() -> set[Path]:
    return protected_sources() | {LOCK, Path(__file__).resolve(),
        ROOT / "tools/verify_blind_upper_components.py", ROOT / "tools/verify_tier6.py",
        ROOT / "tools/test_envelope_transfer_certificates_audit.py",
        ROOT / "toolkit/tests/test_envelope_transfer_certificates.py"} | set(
            (ROOT / "toolkit/threshold_toolkit").glob("*.py"))


def input_hashes() -> dict[str, str]:
    return {p.relative_to(ROOT).as_posix(): sha(p) for p in sorted(audit_inputs())}


def audit_input() -> tuple[str, set[str]]:
    lock = json.loads(LOCK.read_text(encoding="utf-8"))
    actual = {p.relative_to(ROOT).as_posix(): sha(p) for p in sorted(protected_sources())}
    if lock.get("sha256") != actual:
        raise ValueError("Changed envelope/transfer specification or dependency")
    if {p.stem for p in SOURCES.glob("*.lean")} != set(MODULES):
        raise ValueError("Unregistered or missing envelope/transfer module")
    roots = set()
    for path in project_dependencies([SOURCES / "Transfer.lean"]):
        source = strip_comments(path.read_text(encoding="utf-8"))
        if FORBIDDEN.search(source):
            raise ValueError("Forbidden proof escape in " + str(path))
        if path.parent == SOURCES:
            for name in registered_names(source):
                root = PREFIX+name
                if root in roots:
                    raise ValueError("Duplicate declaration root: " + root)
                roots.add(root)
    required = {'transfer_original', 'normalized_identity', 'atomic_group', 'extended_integral', 'extendedAtomic_zero', 'extendedAtomic_probability', 'pointMap_bounds', 'pointMap_bands', 'extendCDF_antitone', 'scaled_core', 'pointMap_measurable', 'fallback_selection'}
    if not {PREFIX+n for n in required} <= roots:
        raise ValueError("Missing envelope/transfer audit target")
    source = "\n".join(["import "+PREFIX+"Transfer", "open "+PREFIX[:-1], EXACT.strip(),
                        *["#print axioms "+r for r in sorted(roots)]])+"\n"
    if FORBIDDEN.search(strip_comments(source)):
        raise ValueError("Forbidden proof escape in generated audit")
    return source, roots


def sample_requests():
    sys.path.insert(0, str(ROOT / "toolkit"))
    from threshold_toolkit.envelope_transfer_certificates import EnvelopeRequest as E, RoundingRequest as R, TransferRequest as T
    def envelope(cdf, **kw):
        return E(tuple(map(F, cdf)), bits=16, log_terms=4, **kw)
    return [envelope((1,)),
            envelope((1, 1, 1), heads=2, tails=3),
            envelope((1, F(1,4)), heads=1),
            envelope((1, F(1,2))),
            envelope((1, F(1,2), F(1,8)), budget=F(64), cap=1),
            envelope((1, F(1,2), F(1,8)), budget=F(64), cap=1024, heads=2, tails=3),
            envelope((1, F(3,4), F(3,4), 0), budget=F(256)),
            envelope((1, 0)),
            R(((F(1,2),F(1)),)),
            R(((F(1,3),F(1,2)),(F(3,8),F(1,2))), subdivisions=1),
            R(((F(1,8),F(1,3)),(F(1,4),F(1,3)),(F(1,3),F(1,3)))),
            T(F(1,32),F(1,16)),
            T(F(1,32),F(1,16),F(3,2),F(1,128)),
            T(F(1,16),F(1,8),F(2),F(1,8)),
            T(F(0),F(0)),
            R(((F(1,4),F(1)),), subdivisions=1)]


def concrete_checks(out: Path) -> dict:
    import copy
    sys.path.insert(0, str(ROOT / "toolkit"))
    from threshold_toolkit.envelope_transfer_certificates import produce, verify, proof_source, VerificationError
    samples = sample_requests()
    accepted = []
    for i, req in enumerate(samples):
        certificate = produce(req)
        result = verify(req, certificate, lean_dir=LEAN, timeout=240)
        (out / f"sample-{i}.json").write_text(json.dumps(certificate, indent=2)+"\n", encoding="utf-8")
        (out / f"sample-{i}.lean").write_text(result.pop("proof_source"), encoding="utf-8")
        (out / f"sample-{i}.log").write_text(result.pop("kernel_report"), encoding="utf-8")
        accepted.append(result)
        print("Kernel accepted sample", i, req.as_dict()["operation"], flush=True)
    bad = [(samples[2], "tail_inverse", "1"),
           (samples[5], "prefix", dict(lower="0",upper="0")),
           (samples[5], "conditional_rho", "1/4"),
           (samples[5], "core", ["1","1"]),
           (samples[5], "band_costs", {"1":"0","2":"0"}),
           (samples[5], "unresolved_mass", "0"),
           (samples[5], "tail_inverse", "0"),
           (samples[5], "resolved_error", "0"),
           (samples[5], "tail_work", "0"),
           (samples[9], "factor", "1"),
           (samples[9], "atoms", [["1/2","1/2"]]),
           (samples[12], "lower", "1/32"),
           (samples[12], "upper", "1/32"),
           (samples[8], "output", dict(atoms=[["1/4","1"]],factor="1",destinations=["1/4"])),
           (samples[15], "output", dict(atoms=[["5/16","1"]],factor="5/4",destinations=["5/16"]))]
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
            rejected.append(dict(operation=req.as_dict()["operation"], changed_field=key, output=cert["output"]))
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
    out = (args.output_dir or ROOT / ".runtime/envelope-transfer-certificates" /
           datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")).resolve()
    out.mkdir(parents=True, exist_ok=False)
    (out / "audit.lean").write_text(source, encoding="utf-8")
    if not args.no_build:
        with (out / "build.log").open("w", encoding="utf-8") as log:
            subprocess.run(["lake", "build", PREFIX+"Transfer"], cwd=LEAN, check=True,
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
                  zero_residual_envelope_contracts_verified=True, rounding_output_contracts_verified=True,
                  conditional_transfer_output_contracts_verified=True, transfer_premises_verified=False,
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
