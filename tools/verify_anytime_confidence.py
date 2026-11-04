"""Audit the online controller, simultaneous coverage and known-law width."""

import subprocess

from verify_blind_upper_components import LEAN, validate_reports


def audit_input():
    source = """
import ThresholdHC.Anytime.Full
noncomputable section
open MeasureTheory ThresholdHC.Tier6 ThresholdHC.HardBudget ThresholdHC.Anytime
open ThresholdHC.Confidence ThresholdHC.RareAboveTwo ThresholdHC.EntropyTail
open scoped ENNReal

example {R : ℕ → Type} [∀ j, MeasurableSpace (R j)] (base : ∀ j, AdaptiveEstimator (R j))
    (M : ℝ) (radius : ℕ → ℝ) (B : ℝ) (upper : Bool) :
    PathwiseCap (endpointEstimator base M radius (stageCount B) upper) ⌊B⌋₊ :=
  endpoint_budget_cap base M radius B upper

example {R : ℕ → Type} [∀ j, MeasurableSpace (R j)] (base : ∀ j, AdaptiveEstimator (R j))
    (M : ℝ) (radius : ℕ → ℝ) {k l : ℕ} (hkl : k ≤ l) (upper upper' : Bool) (r : ∀ j, R j)
    (xs : List Bool) (hx : xs.length < paid k) :
    (endpointEstimator base M radius l upper').policy r xs =
      (endpointEstimator base M radius k upper).policy r xs :=
  endpoint_policy_compatible base M radius hkl upper upper' r xs hx

example {R : ℕ → Type} [∀ j, MeasurableSpace (R j)] (base : ∀ j, AdaptiveEstimator (R j))
    (r : ∀ j, R j) {k l : ℕ} (hkl : k ≤ l) (s : Table) :
    ((readBlock (paid l) (planReader base r l) s).1).take (paid k) =
      (readBlock (paid k) (planReader base r k) s).1 := planWord_prefix base r hkl s

example {R : ℕ → Type} [∀ j, MeasurableSpace (R j)] (base : ∀ j, AdaptiveEstimator (R j))
    (M : ℝ) (radius : ℕ → ℝ) (k : ℕ) (z : (∀ j, R j) × Table) :
    observedInterval base M radius k z = tableInterval base M radius z.1 z.2 k := observedInterval_eq base M radius k z

example {R : ℕ → Type} [∀ j, MeasurableSpace (R j)] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (base : ∀ j, AdaptiveEstimator (R j)) (q : SignLaw) (M : ℝ) (radius : ℕ → ℝ) {δ : ℝ}
    (hd : 0 ≤ δ) (hθ : 0 ≤ signMean μ q.val ∧ signMean μ q.val ≤ M)
    (hcap : ∀ j, PathwiseCap (base j) (stageCap j))
    (hf : ∀ j, failureProbability μ (base j) q (radius j) ≤ ENNReal.ofReal (stageFailure δ j)) :
    1-ENNReal.ofReal δ ≤ (streamLaw μ base q) {z | ∀ k,
      (observedInterval base M radius k z).1 ≤ signMean μ q.val ∧ signMean μ q.val ≤ (observedInterval base M radius k z).2} :=
  simultaneous_probability μ base q M radius hd hθ hcap hf

example {R : ℕ → Type} [∀ j, MeasurableSpace (R j)] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (base : ∀ j, AdaptiveEstimator (R j)) (q : SignLaw) (M : ℝ) (radius : ℕ → ℝ) {δ : ℝ}
    (hd : 0 ≤ δ) (hθ : 0 ≤ signMean μ q.val ∧ signMean μ q.val ≤ M)
    (hcap : ∀ j, PathwiseCap (base j) (stageCap j))
    (hf : ∀ j, failureProbability μ (base j) q (radius j) ≤ ENNReal.ofReal (stageFailure δ j))
    (τ : ((∀ j, R j) × Table) → ℝ) :
    (streamLaw μ base q) {z | ¬ ((observedInterval base M radius (stageCount (τ z)) z).1 ≤ signMean μ q.val ∧
      signMean μ q.val ≤ (observedInterval base M radius (stageCount (τ z)) z).2)} ≤ ENNReal.ofReal δ :=
  selected_budget_coverage μ base q M radius hd hθ hcap hf τ

example {R : ℕ → Type} [∀ j, MeasurableSpace (R j)] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (base : ∀ j, AdaptiveEstimator (R j)) {ρ B δ : ℝ} (hr : 0 < ρ) (hu : ρ ≤ 1/4)
    (hB : 1 ≤ B) (hd : 0 < δ) (hd' : δ ≤ 1/4) (r : ∀ j, R j) (s : Table) :
    halfWidth (tableInterval base ρ (Anytime.radius μ ρ δ) r s (stageCount B)) ≤
      1500002*(selection μ ρ (B/(Real.log (1/δ)+2*Real.log (2+Real.log (1+B)/Real.log 2)))).toReal :=
  all_budget_width μ base hr hu hB hd hd' r s

example (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ δ : ℝ}
    (hr : 0 < ρ) (hu : ρ ≤ 1/4) (hd : 0 < δ) (hd' : δ ≤ 1/4) :
    ∃ (R : ℕ → Type) (_ : ∀ j, MeasurableSpace (R j)) (base : ∀ j, AdaptiveEstimator (R j)),
    ∀ j, PathwiseCap (base j) (stageCap j) ∧ ∀ q : SignLaw, RarePrior μ ρ q →
      failureProbability μ (base j) q (Anytime.radius μ ρ δ j) ≤ ENNReal.ofReal (stageFailure δ j) :=
  known_stages μ hr hu hd hd'

example (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ δ : ℝ}
    (hr : 0 < ρ) (hu : ρ ≤ 1/4) (hd : 0 < δ) (hd' : δ ≤ 1/4) :
    ∃ (R : ℕ → Type) (_ : ∀ j, MeasurableSpace (R j)) (base : ∀ j, AdaptiveEstimator (R j)),
      (∀ B : ℝ, ∀ upper : Bool, PathwiseCap (endpointEstimator base ρ (Anytime.radius μ ρ δ) (stageCount B) upper) ⌊B⌋₊) ∧
      (∀ q : SignLaw, RarePrior μ ρ q →
        (streamLaw μ base q) {z | ∃ k, ¬ ((observedInterval base ρ (Anytime.radius μ ρ δ) k z).1 ≤ signMean μ q.val ∧
          signMean μ q.val ≤ (observedInterval base ρ (Anytime.radius μ ρ δ) k z).2)} ≤ ENNReal.ofReal δ) ∧
      (∀ q : SignLaw, RarePrior μ ρ q → ∀ τ : ((∀ j, R j) × Table) → ℝ,
        (streamLaw μ base q) {z | ¬ ((observedInterval base ρ (Anytime.radius μ ρ δ) (stageCount (τ z)) z).1 ≤ signMean μ q.val ∧
          signMean μ q.val ≤ (observedInterval base ρ (Anytime.radius μ ρ δ) (stageCount (τ z)) z).2)} ≤ ENNReal.ofReal δ) ∧
      (∀ B : ℝ, 1 ≤ B → ∀ z : (∀ j, R j) × Table,
        halfWidth (observedInterval base ρ (Anytime.radius μ ρ δ) (stageCount B) z) ≤
          1500002*(selection μ ρ (B/inflation B δ)).toReal) := known_anytime μ hr hu hd hd'
""".lstrip().replace("Anytime.radius", "ThresholdHC.Anytime.radius")
    roots = {"ThresholdHC.Anytime." + name for name in [
        "sum_stageFailure", "simultaneous_coverage", "interval_readBlock", "endpoint_output", "endpoint_cap",
        "planReader_compatible", "endpoint_policy_compatible", "planWord_prefix",
        "cap_stops", "hard_local_failure", "interval_nested", "interval_coverage", "interval_width",
        "all_stage_coverage", "stopped_stage_coverage", "known_rule", "known_stages", "count_log_bound",
        "completed_stage_bounds", "stage_log_le", "selection_antitone", "radius_width_bound", "all_budget_width",
        "observedInterval_eq", "measurable_observedInterval", "endpoint_budget_cap", "selected_budget_coverage",
        "simultaneous_probability", "known_anytime",
    ]}
    return source + "".join("#print axioms " + name + "\n" for name in sorted(roots)), roots


def main():
    source, roots = audit_input()
    subprocess.run(["lake", "build", "ThresholdHC.Anytime.Full"], cwd=LEAN, check=True)
    run = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=LEAN, input=source, text=True,
                         encoding="utf-8", capture_output=True)
    output = run.stdout + run.stderr
    print(output, end="")
    validate_reports(output, run.returncode, roots)
    print(f"Verified {len(roots)} transitive axiom reports")


if __name__ == "__main__":
    main()
