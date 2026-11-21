"""Audit the known-gap estimator that needs no rarity.

The proposition of research/2026-10-27-minimax-audit/adaptation.tex: at a
known fixed gap d < 1/2 and budget B >= 1, one estimator that never receives
rho buys m flips from each of floor(B/m) fresh coins, with m the least odd
integer at least log(2B)/(2d^2), debiases the share of majority-heads coins by
the exact binomial tail f, and clips to [0,1]. It obeys a deterministic cap of
floor B flips and E T <= B, outputs zero for B < 2m (with squared error exactly
theta^2 there), and has mean squared error at most 8m theta/B + 4m/B^2 for every
theta in [0,1]. The conservative interval [raw - r, raw + r] intersected with
[0,1], r = sqrt(log(2/delta)/(2n))/(1-2f), covers theta with probability at
least 1 - delta, also when centred at the clipped output. The shared-regression
example of the same audit is not part of this group.

The audit

1. requires the directory to hold exactly the registered modules and scans
   each for proof escapes;
2. pins the specification;
3. restates the three targets and three components with their types written out;
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

GROUP = "KnownGapRarity"
NAMES = ("Specification", "Estimator", "Cap", "Miss", "Risk", "Confidence", "Full")
SOURCE = LEAN / f"ThresholdHC/{GROUP}"
SPEC = SOURCE / "Specification.lean"
SPEC_HASH = "b635107a47d869c9f042b59eff428200680c97055ce1c68cf164cb69837587e6"
TARGETS = {
    "KnownGapRarity.flip_count": "KnownGapRarity.FlipCountStatement",
    "KnownGapRarity.known_gap_rarity_free": "KnownGapRarity.KnownGapRarityFreeStatement",
    "KnownGapRarity.known_gap_confidence": "KnownGapRarity.KnownGapConfidenceStatement",
}
COMPONENTS = (
    "KnownGapRarity.missRate_le",
    "KnownGapRarity.majority_pathwiseCap",
    "KnownGapRarity.zero_output_risk",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example :
  ∀ (d : Gap) (B : ℝ), 1 ≤ B →
    Odd (flipCount d B) ∧ Real.log (2*B) / (2*(d:ℝ)^2) ≤ flipCount d B ∧
    ∀ m : ℕ, Odd m → Real.log (2*B) / (2*(d:ℝ)^2) ≤ m → flipCount d B ≤ m :=
  KnownGapRarity.flip_count

example :
  ∀ (d : Gap), (d : ℝ) < 1/2 → ∀ B : ℝ, 1 ≤ B →
    PathwiseCap (knownGapEstimator d B) ⌊B⌋₊ ∧
    UniformBudget (Measure.dirac d) (knownGapEstimator d B) B ∧
    (B < 2 * (flipCount d B : ℝ) → ∀ z, (knownGapEstimator d B).output z = 0) ∧
    (B < 2 * (flipCount d B : ℝ) → ∀ q : SignLaw,
      squaredRisk (experimentLaw (Measure.dirac d) (knownGapEstimator d B) q)
          (populationOutput (knownGapEstimator d B)) (signMean (Measure.dirac d) q.val) =
        ENNReal.ofReal (signMean (Measure.dirac d) q.val ^ 2)) ∧
    ∀ q : SignLaw,
      squaredRisk (experimentLaw (Measure.dirac d) (knownGapEstimator d B) q)
          (populationOutput (knownGapEstimator d B)) (signMean (Measure.dirac d) q.val) ≤
        ENNReal.ofReal (8 * (flipCount d B : ℝ) * signMean (Measure.dirac d) q.val / B
          + 4 * (flipCount d B : ℝ) / B^2) :=
  KnownGapRarity.known_gap_rarity_free

example :
  ∀ (d : Gap), (d : ℝ) < 1/2 → ∀ B : ℝ, 1 ≤ B → ∀ δ : ℝ, 0 < δ → δ < 1 →
    (∀ q : SignLaw, experimentLaw (Measure.dirac d) (rawEstimator d B) q
      {z | signMean (Measure.dirac d) q.val ∉
        Set.Icc (populationOutput (rawEstimator d B) z - knownGapRadius d B δ)
                (populationOutput (rawEstimator d B) z + knownGapRadius d B δ) ∩ Set.Icc 0 1}
        ≤ ENNReal.ofReal δ) ∧
    Confidence.UniformConfidence (Measure.dirac d) (rawEstimator d B) (knownGapRadius d B δ) δ ∧
    Confidence.UniformConfidence (Measure.dirac d) (knownGapEstimator d B) (knownGapRadius d B δ) δ :=
  KnownGapRarity.known_gap_confidence

example : ∀ (d : Gap) {B : ℝ}, 0 < B → missRate d B ≤ 1 / (2*B) :=
  @KnownGapRarity.missRate_le

example : ∀ (k n : ℕ), PathwiseCap (majorityEstimator k n) (n*(2*k+1)) :=
  KnownGapRarity.majority_pathwiseCap

example : ∀ {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R), (∀ z, A.output z = 0) → ∀ (q : SignLaw) (θ : ℝ),
    squaredRisk (experimentLaw μ A q) (populationOutput A) θ = ENNReal.ofReal (θ^2) :=
  @KnownGapRarity.zero_output_risk
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
        raise ValueError("Duplicate known-gap-rarity declaration")
    required = {"ThresholdHC." + name for pair in TARGETS.items() for name in pair}
    required |= {"ThresholdHC." + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing known-gap-rarity target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SPEC) != SPEC_HASH:
        raise ValueError("Changed known-gap-rarity specification")
    roots = declared_roots()
    source = "\n".join([
        *[f"import ThresholdHC.{module}" for module in modules()],
        "open MeasureTheory ProbabilityTheory",
        "open scoped ENNReal",
        "open ThresholdHC ThresholdHC.Tier6 ThresholdHC.FixedPlan ThresholdHC.HardBudget ThresholdHC.KnownGapRarity",
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
    print(f"All {len(TARGETS)} known-gap-rarity targets are certified")


if __name__ == "__main__":
    main()
