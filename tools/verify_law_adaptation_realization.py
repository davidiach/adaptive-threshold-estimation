"""Exact theorem types and transitive axioms for observable law adaptation."""

import subprocess
from verify_blind_upper_components import LEAN, validate_reports


def audit_input():
    source = """
import ThresholdHC.LawAdaptation.Properties
noncomputable section
set_option linter.unusedVariables false
open MeasureTheory
open scoped ENNReal
open ThresholdHC.Tier6 ThresholdHC.LawAdaptation ThresholdHC.HardBudget
open ThresholdHC.Anytime ThresholdHC.ObservableSimulation ThresholdHC.RareAboveTwo
open ThresholdHC.EntropyTail

example : ∀ (μ ν : Measure unitInterval)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ k : ℕ, ∫ x, (x:ℝ)^k ∂μ = ∫ x, (x:ℝ)^k ∂ν),
    μ = ν := @unitInterval_eq_of_moments

example : Measurable squaredGap := measurable_squaredGap

example : Function.Injective squaredGap := squaredGap_injective

example : ∀ (μ ν : Measure Gap)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ k : ℕ, 0 < k → evenMoment μ k = evenMoment ν k),
    μ = ν := @gapLaw_eq_of_evenMoments

example : ∀ (μ ν : Measure Gap)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hne : μ ≠ ν),
    ∃ k : ℕ, 0 < k ∧ evenMoment μ k ≠ evenMoment ν k := @exists_separating_moment

example : ∀ {ι : Type*} [Fintype ι] [Nonempty ι]
    (laws : ι → Measure Gap) [∀ i, IsProbabilityMeasure (laws i)]
    (hinj : Function.Injective laws),
    ∃ m : ℕ, 0 < m ∧ ∃ η : ℝ, 0 < η ∧
      ∀ i j, i ≠ j → ∃ k : Fin m,
        η ≤ |evenMoment (laws i) (k.val+1) - evenMoment (laws j) (k.val+1)| :=
  @finite_moment_separation

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (k : ℕ),
    ∫ tape, prefixParity k tape ∂originalPopulationTapeLaw μ q = evenMoment μ k :=
  @original_prefixParity_mean

example : ∀ {ι : Type*} [Nonempty ι] (laws : ι → Measure Gap)
    [∀ i, IsProbabilityMeasure (laws i)] (truth : ι) (q : SignLaw)
    {m n : ℕ} (hn : 0 < n) {η : ℝ} (hη : 0 < η)
    (hdist : ∀ i j, i ≠ j → ∃ k : Fin m,
      η ≤ |evenMoment (laws i) (k.val+1)-evenMoment (laws j) (k.val+1)|),
    (pilotTableLaw (laws truth) q)
      {t | identify (fun i (k : Fin m) => evenMoment (laws i) (k.val+1))
        (fun k => pilotAverage n (k.val+1) t) (η/4) ≠ truth} ≤
      ENNReal.ofReal (2*(m:ℝ)*Real.exp (-(n:ℝ)*η^2/32)) := @original_pilot_error

example : ∀ (m n j : ℕ) (s : Table) (hj : n ≤ j),
    (readBlock (pilotCost n m) (pilotReader m n) s).2 j = s j := @pilot_fresh

example : ∀ (n m k : ℕ) (hk : k ≤ m) (s : Table),
    historyAverage n m k (readBlock (pilotCost n m) (pilotReader m n) s).1 =
      pilotAverage n k s := @historyAverage_readBlock

example : ∀ {ι : Type*} [Nonempty ι] (laws : ι → Measure Gap)
    (n m : ℕ) (η : ℝ) (s : Table),
    chosenWord laws n m η (readBlock (pilotCost n m) (pilotReader m n) s).1 =
      chosenTable laws n m η s := @chosenWord_readBlock

example : ∀ (n m : ℕ) (p : Reader) (q : List Bool → Reader) (s : Table),
    readBlock (n+m) (thenChoose n p q) s =
      let v := readBlock n p s
      let u := readBlock m (q v.1) v.2
      (v.1++u.1,u.2) := @readBlock_thenChoose

example : ∀ {ι : Type} [Nonempty ι] {R : ι → ℕ → Type}
    [∀ i j, MeasurableSpace (R i j)] (laws : ι → Measure Gap)
    (n m : ℕ) (η M : ℝ) (base : ∀ i j, AdaptiveEstimator (R i j))
    (rad : ι → ℕ → ℝ) (k : ℕ) (upper : Bool),
    PathwiseCap (postEndpoint laws n m η M base rad k upper) (pilotCost n m+paid k) :=
  @postEndpoint_cap

example : ∀ {ι : Type} [Nonempty ι] {R : ι → ℕ → Type}
    [∀ i j, MeasurableSpace (R i j)] (laws : ι → Measure Gap)
    (n m : ℕ) (η M : ℝ) (base : ∀ i j, AdaptiveEstimator (R i j))
    (rad : ι → ℕ → ℝ) (k : ℕ) (upper : Bool)
    (r : ∀ i j, R i j) (s : Table),
    (postEndpoint laws n m η M base rad k upper).output
      (r,populationPath ((postEndpoint laws n m η M base rad k upper).policy r) s) =
      if upper then (postTableInterval laws n m η M base rad r s k).2
      else (postTableInterval laws n m η M base rad r s k).1 := @postEndpoint_output

example : ∀ {ι : Type} {R : ι → ℕ → Type} [∀ i j, MeasurableSpace (R i j)]
    (μ : Measure Gap) [IsProbabilityMeasure μ]
    (base : ∀ i j, AdaptiveEstimator (R i j)) (q : SignLaw) (n : ℕ) (i : ι),
    MeasurePreserving (branchInputs (R := R) n i)
      (familyStreamLaw μ base q) (streamLaw μ (base i) q) := @branchInputs_preserving

example : ∀ {ι : Type} [Nonempty ι] {R : ι → ℕ → Type}
    [∀ i j, MeasurableSpace (R i j)] (laws : ι → Measure Gap)
    (n m : ℕ) (η M : ℝ) (base : ∀ i j, AdaptiveEstimator (R i j))
    (rad : ι → ℕ → ℝ) (B : ℕ) (upper : Bool),
    PathwiseCap (budgetEndpoint laws n m η M base rad B upper) B := @budgetEndpoint_cap

example : ∀ {ι : Type} [Nonempty ι] {R : ι → ℕ → Type}
    [∀ i j, MeasurableSpace (R i j)] (laws : ι → Measure Gap)
    (n m : ℕ) (η M : ℝ) (base : ∀ i j, AdaptiveEstimator (R i j))
    (rad : ι → ℕ → ℝ) (B : ℕ) (z : (∀ i j, R i j) × Table),
    budgetInterval laws n m η M base rad B z =
      if pilotCost n m ≤ B then postTableInterval laws n m η M base rad z.1 z.2
        (stageCount ((B-pilotCost n m:ℕ):ℝ)) else (0,M) := @budgetInterval_eq

example : ∀ {ι : Type} [Nonempty ι] {R : ι → ℕ → Type}
    [∀ i j, MeasurableSpace (R i j)] (laws : ι → Measure Gap)
    (n m : ℕ) (η M : ℝ) (base : ∀ i j, AdaptiveEstimator (R i j))
    (rad : ι → ℕ → ℝ) {B C : ℕ} (hBC : B ≤ C) (upper upper' : Bool)
    (r : ∀ i j, R i j) (xs : List Bool)
    (hx : xs.length < if pilotCost n m ≤ B then
      pilotCost n m+paid (stageCount ((B-pilotCost n m:ℕ):ℝ)) else B),
    (budgetEndpoint laws n m η M base rad C upper').policy r xs =
      (budgetEndpoint laws n m η M base rad B upper).policy r xs :=
  @budget_policy_compatible

example : ∀ {m : ℕ} (hm : 0 < m) {η δ : ℝ}
    (hη : 0 < η) (hd : 0 < δ) (hd' : δ ≤ 1/4),
    0 < sampleCount m η δ ∧
      Real.log (4*(m:ℝ)/δ) ≤ (sampleCount m η δ:ℝ)*η^2/32 := @sampleCount_spec

example : ∀ {ι : Type} [Nonempty ι] [Fintype ι]
    (laws : ι → Measure Gap) [∀ i, IsProbabilityMeasure (laws i)]
    (hinj : Function.Injective laws) {ρ δ : ℝ}
    (hr : 0 < ρ) (hu : ρ ≤ 1/4) (hd : 0 < δ) (hd' : δ ≤ 1/4),
    ∃ (m : ℕ) (η : ℝ), 0 < m ∧ 0 < η ∧
      ∃ (R : ι → ℕ → Type) (_ : ∀ i j, MeasurableSpace (R i j))
        (base : ∀ i j, AdaptiveEstimator (R i j)),
        (∀ (B : ℕ) (upper : Bool), PathwiseCap
          (budgetEndpoint laws (sampleCount m η δ) m η ρ base
            (fun i => radius (laws i) ρ (δ/2)) B upper) B) ∧
        (∀ (truth : ι) (q : SignLaw), RarePrior (laws truth) ρ q →
          (familyStreamLaw (laws truth) base q) {z | ∃ B : ℕ,
            ¬ ((budgetInterval laws (sampleCount m η δ) m η ρ base
                (fun i => radius (laws i) ρ (δ/2)) B z).1 ≤ signMean (laws truth) q.val ∧
              signMean (laws truth) q.val ≤
                (budgetInterval laws (sampleCount m η δ) m η ρ base
                  (fun i => radius (laws i) ρ (δ/2)) B z).2 ∧
              (2*pilotCost (sampleCount m η δ) m ≤ B →
                halfWidth (budgetInterval laws (sampleCount m η δ) m η ρ base
                  (fun i => radius (laws i) ρ (δ/2)) B z) ≤
                    3000004*(selection (laws truth) ρ ((B:ℝ)/inflation (B:ℝ) δ)).toReal))} ≤
            ENNReal.ofReal δ) := @finite_family_anytime

example : ∀ {ι : Type} [Nonempty ι] {R : ι → ℕ → Type}
    [∀ i j, MeasurableSpace (R i j)] (laws : ι → Measure Gap)
    (n m : ℕ) (η M : ℝ) (base : ∀ i j, AdaptiveEstimator (R i j))
    (rad : ι → ℕ → ℝ) {B C : ℕ} (hBC : B ≤ C) (z : (∀ i j, R i j) × Table),
    (budgetInterval laws n m η M base rad B z).1 ≤
      (budgetInterval laws n m η M base rad C z).1 ∧
    (budgetInterval laws n m η M base rad C z).2 ≤
      (budgetInterval laws n m η M base rad B z).2 := @budgetInterval_nested

example : ∀ {ι : Type} [Nonempty ι] {R : ι → ℕ → Type}
    [∀ i j, MeasurableSpace (R i j)] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (laws : ι → Measure Gap) (n m : ℕ) (η M : ℝ)
    (base : ∀ i j, AdaptiveEstimator (R i j)) (rad : ι → ℕ → ℝ)
    (B : ℕ) (q : SignLaw),
    (experimentLaw μ (budgetEndpoint laws n m η M base rad B false) q).map
      (fun z => ((budgetEndpoint laws n m η M base rad B false).output (z.1.1,z.2),
        (budgetEndpoint laws n m η M base rad B true).output (z.1.1,z.2))) =
      (familyStreamLaw μ base q).map (budgetInterval laws n m η M base rad B) :=
  @original_budget_interval_law
"""
    roots = {"ThresholdHC.LawAdaptation." + name for name in [
        "unitInterval_eq_of_moments", "measurable_squaredGap", "squaredGap_injective",
        "gapLaw_eq_of_evenMoments", "exists_separating_moment", "finite_moment_separation",
        "original_prefixParity_mean", "original_pilot_error", "pilot_fresh",
        "historyAverage_readBlock", "chosenWord_readBlock", "readBlock_thenChoose",
        "postEndpoint_cap", "postEndpoint_output", "branchInputs_preserving",
        "budgetEndpoint_cap", "budgetInterval_eq", "budget_policy_compatible",
        "sampleCount_spec", "finite_family_anytime",
        "budgetInterval_nested", "original_budget_interval_law",
    ]}
    return source + "".join("#print axioms " + name + "\n" for name in sorted(roots)), roots


def main():
    source, roots = audit_input()
    subprocess.run(["lake", "build", "ThresholdHC.LawAdaptation.Properties"],
                   cwd=LEAN, check=True)
    run = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=LEAN, input=source,
                         text=True, encoding="utf-8", capture_output=True)
    output = run.stdout + run.stderr
    print(output, end="")
    validate_reports(output, run.returncode, roots)
    print(f"Verified {len(roots)} exact statements and transitive axiom reports")


if __name__ == "__main__":
    main()

