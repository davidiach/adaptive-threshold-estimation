"""Audit the full-null bank of the zero-atom planner.

The robust-continuation zero-atom planner of the toolkit tests positive coins
against the full null law: a fair coin with probability z0 (the zero-gap atom)
mixed with the all-negative law of the reference gap law. The library's robust
planner used only the all-negative part. The group defines that bank, proves
it upward with Ville's bound under the full null and integrated false
positives at most u, per-coin work with the known-law constants and the
envelope z0 + threePieceEnvelope, and the level error and work bounds of the
robust planner with the full-null bank. The plan and planner rate built on it
are a later part and are not stated.

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

GROUP = "FullNullBank"
NAMES = ("Specification", "Bank", "CoinWork", "Level", "Full")
SOURCE = LEAN / f"ThresholdHC/{GROUP}"
SPEC = SOURCE / "Specification.lean"
SPEC_HASH = "147d640e8dbfe1ad13332f82db1d5b4908875c5eefdf1cc8a15c5ff5630b33fd"
TARGETS = {
    "FullNullBank.full_null_bank": "FullNullBank.FullNullBankStatement",
    "FullNullBank.full_null_level": "FullNullBank.FullNullLevelStatement",
}
COMPONENTS = (
    "FullNullBank.fullNull_prefix",
    "FullNullBank.allNegative_le_fullNull",
    "FullNullBank.fullNull_envelope_eq",
)
EXACT_COUNT = len(TARGETS) + len(COMPONENTS)

EXACT = """
example :
  ∀ (z₀ : ℝ) (η : Measure Gap) [IsProbabilityMeasure η] (weights : ℕ → ℝ≥0),
    HasSum weights 1 → 0 ≤ z₀ → z₀ < 1 →
    (∀ u, UpwardTest (fullNullBankTest z₀ η weights u)) ∧
    (∀ u, fullNullLaw z₀ η (everPrefixHit (fullNullBankTest z₀ η weights u)) ≤
      ENNReal.ofReal u) ∧
    (∀ u, 0 ≤ u → (1 - z₀) * (∫ d, tapeEventProbability false
      (everPrefixHit (fullNullBankTest z₀ η weights u)) d ∂η) ≤ u) ∧
    ∀ (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ],
      σ+τ+ζ = ENNReal.ofReal (1 - z₀) • η →
      Integrable (fun x : Gap => (x:ℝ)⁻¹^2) σ → Integrable (fun x : Gap => (x:ℝ)⁻¹) τ →
      ∀ {ε ρ : ℝ}, 0 < ε → ε ≤ 1 → 0 < ρ →
      ∀ (j L : ℕ), 0 < (weights j:ℝ) → (weights j:ℝ) ≤ 1 →
      ∀ {d₀ d : Gap}, d₀ ∈ EntropyTailQuantile.band j → (d₀:ℝ) ≤ d →
        conditionalRaceWork (negativeBankTest weights ε) (fullNullBankTest z₀ η weights (ρ*ε))
            L true d ≤
          12*positiveAllowance ε (weights j:ℝ) ρ (z₀ + threePieceEnvelope σ τ ζ d₀)/(d₀:ℝ)^2 ∧
        conditionalRaceWork (negativeBankTest weights ε) (fullNullBankTest z₀ η weights (ρ*ε))
            L false d ≤
          (3/(2*(d₀:ℝ)^2))*(1+Real.log (ε*(weights j:ℝ))⁻¹) :=
  FullNullBank.full_null_bank

example :
  ∀ (z₀ : ℝ) (η : Measure Gap) [IsProbabilityMeasure η], 0 ≤ z₀ → z₀ < 1 →
  ∀ (π : Measure (Gap × Gap)) [IsFiniteMeasure π], (∀ᵐ z ∂π, (z.1:ℝ) ≤ z.2) →
    π.map Prod.fst = ENNReal.ofReal (1 - z₀) • η →
  ∀ (μ₀ : Measure Gap) [IsFiniteMeasure μ₀] {ρ : ℝ}, 0 < ρ →
  ∀ q : SignLaw, RarePrior (π.map Prod.snd + μ₀) ρ q →
    (∀ (ν ζ : Measure Gap) [IsFiniteMeasure ν] [IsFiniteMeasure ζ],
      ν+ζ = ENNReal.ofReal (1 - z₀) • η →
      ∀ weights : ℕ → ℝ≥0, HasSum weights 1 → ∀ l k : ℕ,
      eta ν (4^k) ≤ levelAccuracy ρ l/8 →
      ζ.real univ + μ₀.real univ ≤ levelAccuracy ρ l/8 →
      racePopulationError (π.map Prod.snd + μ₀) q (negativeBankTest weights (levelEpsilon l))
        (fullNullBankTest z₀ η weights (ρ*levelEpsilon l)) (2*k) ≤ levelAccuracy ρ l) ∧
    (∀ (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ],
      σ+τ+ζ = ENNReal.ofReal (1 - z₀) • η →
      ∀ {t : ℝ} {N : ℕ}, 0 < t → (∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) →
      EntropyTailQuantile.bandEdge N < t → Integrable (fun d : Gap => (d:ℝ)⁻¹) τ →
      z₀ + ζ.real univ ≤ ρ → ∀ l L : ℕ,
      (∫ d, mixtureRaceWork q (negativeBankTest (referenceWeights σ) (levelEpsilon l))
          (fullNullBankTest z₀ η (referenceWeights σ) (ρ*levelEpsilon l)) L d
          ∂(π.map Prod.snd + μ₀)) ≤
        128*(l+1)*EntropyTailQuantile.costEntropy
            (fun j : Fin N => EntropyTailQuantile.bandCost σ j.val) +
        6*(∫ d : Gap, (d:ℝ)⁻¹ ∂τ)^2/ρ + 2*ordinaryCost τ (Uniform713.cap L) +
        2*Uniform713.cap L*(ζ.real univ + μ₀.real univ)) :=
  FullNullBank.full_null_level

example : ∀ (z₀ : ℝ) (η : Measure Gap) {n : ℕ} (w : Fin n → Bool),
    fullNullLaw z₀ η (tapePrefix n ⁻¹' {w}) =
      ENNReal.ofReal z₀ * ENNReal.ofReal (streamProb (1/2) w) +
        ENNReal.ofReal (1 - z₀) * allNegativeLaw η (tapePrefix n ⁻¹' {w}) :=
  @FullNullBank.fullNull_prefix

example : ∀ (z₀ : ℝ) (η : Measure Gap) (E : Set (ℕ → Bool)),
    ENNReal.ofReal (1 - z₀) * allNegativeLaw η E ≤ fullNullLaw z₀ η E :=
  FullNullBank.allNegative_le_fullNull

example : ∀ (z₀ : ℝ) (σ τ ζ : Measure Gap) (d : Gap),
    z₀ + threePieceEnvelope σ τ ζ d = (z₀ + ζ.real Set.univ) + (∫ x : Gap, (x:ℝ)⁻¹^2 ∂σ)*(d:ℝ)^2 +
      (∫ x : Gap, (x:ℝ)⁻¹ ∂τ)*(d:ℝ) :=
  FullNullBank.fullNull_envelope_eq
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
        raise ValueError("Duplicate full-null-bank declaration")
    required = {"ThresholdHC." + name for pair in TARGETS.items() for name in pair}
    required |= {"ThresholdHC." + name for name in COMPONENTS}
    missing = required - set(roots)
    if missing:
        raise ValueError("Missing full-null-bank target: " + ", ".join(sorted(missing)))
    return set(roots)


def audit_input() -> tuple[str, set[str]]:
    if sha(SPEC) != SPEC_HASH:
        raise ValueError("Changed full-null-bank specification")
    roots = declared_roots()
    source = "\n".join([
        *[f"import ThresholdHC.{module}" for module in modules()],
        "open MeasureTheory ProbabilityTheory",
        "open scoped ENNReal",
        "open Set NNReal ThresholdHC ThresholdHC.Tier2 ThresholdHC.Tier6 ThresholdHC.ObservableSimulation ThresholdHC.EntropyTailUpper ThresholdHC.EntropyTailAssembly ThresholdHC.RobustContinuation ThresholdHC.RareAboveTwo ThresholdHC.FullNullBank",
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
    print(f"All {len(TARGETS)} full-null-bank targets are certified")


if __name__ == "__main__":
    main()
