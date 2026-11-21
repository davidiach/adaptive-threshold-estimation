"""Audit the Bernoulli-subfamily time-uniform lower bound.

The unknown-law confidence note proves that no online interval can have a
deterministic half-width envelope below sqrt(3 (1 - delta) rho / 64) times
sqrt(log log n / n) at all large n, by restricting to constant sign laws in
[rho/2, rho] and bounding their observable KL by chi-square units. The group
states this bound in the original hidden-gap online experiment for every gap
law, without monotonicity of the envelope, together with the observable
prefix KL bound of two constant sign laws that it rests on.

The audit

1. requires the directory to hold exactly the registered modules and scans
   each for proof escapes;
2. pins the specification;
3. restates the two targets and three components with their types written out;
4. reports the transitive axioms of every public declaration in the directory.

With --replay the registered modules also go through the toolchain's
independent kernel checker. The statements were written before the proofs
and reviewed before the pin; they are pinned from this audit onward.
"""

from __future__ import annotations

import argparse
import re
import subprocess

from verify_blind_upper_components import FORBIDDEN, LEAN, sha, strip_comments, validate_reports
from verify_sharp_rms import public_names

GROUP = "BernoulliTimeUniform"
NAMES = ("Specification", "TranscriptKL", "PrefixKL", "Testing", "Schedule", "Full")
SOURCE = LEAN / f"ThresholdHC/{GROUP}"
SPEC = SOURCE / "Specification.lean"
SPEC_HASH = "cbf4a07dfbf950346c3443f6ecec44291051509e541b70ce637eda315d16e5fb"
TARGETS = {
    "BernoulliTimeUniform.constant_prior_prefix_kl": "BernoulliTimeUniform.ConstantPriorPrefixKLStatement",
    "BernoulliTimeUniform.bernoulli_time_uniform_lower": "BernoulliTimeUniform.BernoulliTimeUniformLowerStatement",
}
COMPONENTS = (
    "BernoulliTimeUniform.constant_transcript_kl",
    "BernoulliTimeUniform.baseVar_lower",
    "BernoulliTimeUniform.scheduleBudget_loglog_upper",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example :
  ∀ (R : Type) [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (θ θ' : ℝ) (hθ : 0 < θ ∧ θ < 1) (hθ' : 0 < θ' ∧ θ' < 1) (n : ℕ),
    klDiv (observablePrefixLaw μ A
        (ThresholdHC.StoppingProgram.constantPrior θ' ⟨hθ'.1.le, hθ'.2.le⟩) n)
      (observablePrefixLaw μ A
        (ThresholdHC.StoppingProgram.constantPrior θ ⟨hθ.1.le, hθ.2.le⟩) n) ≤
      ENNReal.ofReal ((n:ℝ) * (θ' - θ)^2 / (θ * (1 - θ))) :=
  BernoulliTimeUniform.constant_prior_prefix_kl

example :
  ∀ (R : Type) [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ δ : ℝ),
    0 < ρ → ρ ≤ 1/4 → 0 < δ → δ < 1 →
    ∀ (A : AdaptiveEstimator R) (L U : ∀ n, R × Prefix n → ℝ),
      (∀ n, Measurable (L n)) → (∀ n, Measurable (U n)) →
      ∀ t : ℕ → ℝ, OnlineIntervalCoverage μ A L U ρ δ t →
      ∀ M : ℕ, ∃ n : ℕ, max M 3 ≤ n ∧
        Real.sqrt (3*(1-δ)*ρ/64) * Real.sqrt (Real.log (Real.log (n:ℝ)) / (n:ℝ)) ≤ t n :=
  BernoulliTimeUniform.bernoulli_time_uniform_lower

example : ∀ {m : ℕ} (n : ℕ) (pol : List Bool → Option (Fin m)) (d : Fin m → ℝ), (∀ i, 0 ≤ d i ∧ d i ≤ 1/2) → ∀ {θ θ' : ℝ}, 0 < θ ∧ θ < 1 → 0 < θ' ∧ θ' < 1 → klFT (transcriptLaw (n:=n) pol d (fun _ => θ')) (transcriptLaw pol d (fun _ => θ)) ≤ n*((θ'-θ)^2/(θ*(1-θ))) :=
  @BernoulliTimeUniform.constant_transcript_kl

example : ∀ {ρ : ℝ}, 0 < ρ → ρ ≤ 1/4 → 39*ρ/64 ≤ BernoulliTimeUniform.baseVar ρ :=
  @BernoulliTimeUniform.baseVar_lower

example : ∀ {ρ δ : ℝ}, 0 < ρ → ρ ≤ 1/4 → δ < 1 → ∀ (k : ℕ), 2 ≤ BernoulliTimeUniform.scheduleBudget ρ δ k → Real.log (Real.log (BernoulliTimeUniform.scheduleBudget ρ δ k:ℝ)) ≤ Real.log (|Real.log (16*(1-δ)*BernoulliTimeUniform.baseVar ρ/ρ^2)|+5)+Real.log ((k:ℝ)+2) :=
  @BernoulliTimeUniform.scheduleBudget_loglog_upper
"""


def modules() -> list[str]:
    return [f"{GROUP}.{name}" for name in NAMES]


def declared_roots() -> set[str]:
    found = {p.stem for p in SOURCE.glob("*.lean")}
    if found != set(NAMES) or len(NAMES) != len(set(NAMES)):
        raise ValueError(f"Unregistered or missing {GROUP} module")
    roots: list[str] = []
    for name in NAMES:
        source = strip_comments((SOURCE / f"{name}.lean").read_text(encoding="utf-8"))
        if FORBIDDEN.search(source):
            raise ValueError(f"Forbidden proof escape in {GROUP}/{name}.lean")
        names_here = public_names(source, f"{GROUP}/{name}.lean")
        if any(not root.startswith(f"ThresholdHC.{GROUP}.") for root in names_here):
            raise ValueError(f"{GROUP}/{name}.lean must declare in ThresholdHC.{GROUP}")
        roots.extend(names_here)
    if len(roots) != len(set(roots)):
        raise ValueError("Duplicate bernoulli-time-uniform declaration")
    required = {"ThresholdHC." + name for pair in TARGETS.items() for name in pair}
    required |= {"ThresholdHC." + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing bernoulli-time-uniform target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SPEC) != SPEC_HASH:
        raise ValueError("Changed bernoulli-time-uniform specification")
    roots = declared_roots()
    source = "\n".join([
        *[f"import ThresholdHC.{module}" for module in modules()],
        "open MeasureTheory ProbabilityTheory",
        "open scoped ENNReal",
        "open InformationTheory open ThresholdHC ThresholdHC.Proofs ThresholdHC.Tier5 ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.AnytimeLower",
        *[f"example : {statement} := {theorem}" for theorem, statement in sorted(TARGETS.items())],
        EXACT.strip("\n"),
        *["#print axioms " + root for root in sorted(roots)],
    ]) + "\n"
    if ("\n" + EXACT).count("\nexample") != EXACT_COUNT:
        raise ValueError("Each target and component needs exactly one restated statement")
    for name in list(TARGETS) + list(COMPONENTS):
        if len(re.findall(rf":=\s*@?{re.escape(name)}\n", EXACT)) != 1:
            raise ValueError("Each target and component needs exactly one restated statement")
    return source, roots


def replay_modules() -> list[str]:
    return ["ThresholdHC." + module for module in modules()]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--replay", action="store_true",
                        help="also replay the registered modules through leanchecker")
    parser.add_argument("--jobs", type=int, default=3, help="parallel kernel replays")
    args = parser.parse_args()
    source, roots = audit_input()
    subprocess.run(["lake", "build", *replay_modules()], cwd=LEAN, check=True)
    run = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=LEAN, input=source,
                         text=True, encoding="utf-8", capture_output=True)
    output = run.stdout + run.stderr
    print(output, end="")
    validate_reports(output, run.returncode, roots)
    print(f"Verified {EXACT_COUNT} exact statements and {len(roots)} transitive axiom reports")
    if args.replay:
        from verify_project_axioms import replay
        replay(replay_modules(), "lake", args.jobs)
        print(f"Replayed {len(modules())} modules through the independent kernel checker")
    print(f"All {len(TARGETS)} bernoulli-time-uniform targets are certified")


if __name__ == "__main__":
    main()
