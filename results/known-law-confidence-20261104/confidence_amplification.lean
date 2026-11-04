import ThresholdHC.ConfidenceProgram.Upper
noncomputable section
open MeasureTheory ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.ObservableSimulation
open ThresholdHC.HardBudget ThresholdHC.Confidence ThresholdHC.ConfidenceProgram
open ThresholdHC.ConfidenceTransfer ThresholdHC.EntropyTail ThresholdHC.CriticalUpper
open scoped ENNReal

example {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (m N : ℕ) (M : ℝ) :
    PathwiseCap (cappedMedian A m N M) ((2*m+1)*N) := cappedMedian_cap A m N M

example {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (m N : ℕ) (M : ℝ) (r : ℕ → R) (s : Table) :
    (cappedMedian A m N M).output (r,populationPath ((cappedMedian A m N M).policy r) s) =
      median m (fun i => localValue M (outcome A N M (stageInputs (r,s) i.val))) :=
  cappedMedian_output A m N M r s

example {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (q : SignLaw) (m : ℕ) {B M r δ : ℝ}
    (hb : 0 < B) (hd : 0 ≤ δ) (hm : (3/4:ℝ)^(2*m+1) ≤ δ^2)
    (hθ : 0 ≤ signMean μ q.val ∧ signMean μ q.val ≤ M) (hr : 0 ≤ r)
    (hw : expectedWork μ A q ≤ ENNReal.ofReal (B/(8*(2*(m:ℝ)+1))))
    (hR : rootMeanRisk (experimentLaw μ A q) (populationOutput A) (signMean μ q.val) ≤ ENNReal.ofReal r) :
    let n := ⌊B/(2*(m:ℝ)+1)⌋₊
    PathwiseCap (cappedMedian A m n M) ⌊B⌋₊ ∧
      failureProbability μ (cappedMedian A m n M) q (Real.sqrt 8*r) ≤ ENNReal.ofReal δ :=
  capped_median_at_level μ A q m hb hd hm hθ hr hw hR

example (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ B δ : ℝ}
    (hr : 0 < ρ) (hu : ρ ≤ 1/4) (hb : 0 < B) (hd : 0 < δ) (hd' : δ ≤ 1/4) :
    let K := selection μ ρ (B/Real.log (1/δ))
    ENNReal.ofReal ((10:ℝ)⁻¹^17)*K/30 ≤ rareConfidenceRadius μ ρ B δ ∧
      rareConfidenceRadius μ ρ B δ ≤ hardConfidenceRadius μ ρ B δ ∧
      hardConfidenceRadius μ ρ B δ ≤ 750000*K := general_confidence_rate μ hr hu hb hd hd'

example : ∃ c : ℝ, 0 < c ∧ ∀ (ρ B δ : ℝ), 0 < ρ → ρ ≤ 1/4 → 0 < B → 0 < δ → δ ≤ 1/4 →
    let z := min ρ (Real.sqrt (ρ*ThresholdHC.CriticalEntropy.criticalLogFactor ρ*Real.log (1/δ)/B))
    ENNReal.ofReal (c*z) ≤ rareConfidenceRadius criticalPositiveLaw ρ B δ ∧
      rareConfidenceRadius criticalPositiveLaw ρ B δ ≤ hardConfidenceRadius criticalPositiveLaw ρ B δ ∧
      hardConfidenceRadius criticalPositiveLaw ρ B δ ≤ ENNReal.ofReal (2670000*z) := critical_confidence_rate
#print axioms ThresholdHC.ConfidenceProgram.baseBudget_scale
#print axioms ThresholdHC.ConfidenceProgram.cappedMedian_cap
#print axioms ThresholdHC.ConfidenceProgram.cappedMedian_output
#print axioms ThresholdHC.ConfidenceProgram.capped_median_at_level
#print axioms ThresholdHC.ConfidenceProgram.capped_median_failure
#print axioms ThresholdHC.ConfidenceProgram.critical_confidence_rate
#print axioms ThresholdHC.ConfidenceProgram.critical_hard_confidence_upper
#print axioms ThresholdHC.ConfidenceProgram.expected_confidence_le_hard
#print axioms ThresholdHC.ConfidenceProgram.general_confidence_rate
#print axioms ThresholdHC.ConfidenceProgram.general_hard_confidence_upper
#print axioms ThresholdHC.ConfidenceProgram.hard_confidence_of_base
#print axioms ThresholdHC.ConfidenceProgram.hard_median_transfer
#print axioms ThresholdHC.ConfidenceProgram.independent_words
#print axioms ThresholdHC.ConfidenceProgram.median_budget_cap
#print axioms ThresholdHC.ConfidenceProgram.observed_block
#print axioms ThresholdHC.ConfidenceProgram.quarter_majority
#print axioms ThresholdHC.ConfidenceProgram.schedule_failure
#print axioms ThresholdHC.ConfidenceProgram.single_capped_failure
#print axioms ThresholdHC.ConfidenceProgram.stageResult_value
#print axioms ThresholdHC.HardBudget.rare_base
#print axioms ThresholdHC.HardBudget.stopAt_pathwise_cap
#print axioms ThresholdHC.HardBudget.timeout_work
