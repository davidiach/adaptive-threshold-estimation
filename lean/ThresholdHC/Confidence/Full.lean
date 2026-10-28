import ThresholdHC.Confidence.Realization
import ThresholdHC.Confidence.BudgetScale
import ThresholdHC.Confidence.Nonvacuity

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.Confidence
open ThresholdHC.Tier6 ThresholdHC.BlindUpper ThresholdHC.ObservableSimulation
open ThresholdHC.Tier3 ThresholdHC.CriticalEntropy

def idleRepeatEstimator : AdaptiveEstimator RepeatSeed where
  randomLaw := repeatSeedLaw
  probability := repeatSeedLaw_probability
  policy := fun _ _ => none
  policy_measurable := by
    intro xs a
    exact measurableSet_eq_fun measurable_const measurable_const
  output := fun _ => 0
  output_measurable := measurable_const

theorem idleRepeat_expectedWork_zero (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    expectedWork μ idleRepeatEstimator q = 0 := by
  rw [original_expectedWork_simulation]
  have hz (z : RepeatSeed × (ℕ → ℕ → Bool)) :
      totalProcessWork (populationPath (idleRepeatEstimator.policy z.1) z.2) = 0 := by
    have he : populationPath (idleRepeatEstimator.policy z.1) z.2 = fun _ => none := by
      funext n
      simp [populationPath,populationSimulation,idleRepeatEstimator]
    rw [he]
    simp [totalProcessWork,ThresholdHC.workOf,processPrefix]
  simp_rw [hz]
  simp

theorem idleRepeat_confidence (μ : Measure Gap) [IsProbabilityMeasure μ] (δ r : ℝ) (hr : 1 ≤ r) :
    UniformConfidence μ idleRepeatEstimator r δ := by
  intro q
  have hm := signMean_bounds μ q
  have he : {z | r < |populationOutput idleRepeatEstimator z-signMean μ q.val|} = ∅ := by
    ext z
    simp only [populationOutput,idleRepeatEstimator,zero_sub,abs_neg,abs_of_nonneg hm.1,
      Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
    linarith
  unfold failureProbability
  rw [he,measure_empty]
  exact bot_le

theorem failureProbability_mono {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (q : SignLaw)
    {r s : ℝ} (hrs : r ≤ s) : failureProbability μ A q s ≤ failureProbability μ A q r :=
  measure_mono (fun _ h => lt_of_le_of_lt hrs h)

def confidenceEstimator (B δ : ℝ) : AdaptiveEstimator RepeatSeed :=
  if 4 ≤ B/(confidenceCount δ : ℝ) then
    repeatEstimator (confidenceRepetitions δ) (budgetLevel (B/(confidenceCount δ : ℝ)))
  else idleRepeatEstimator

/-- One family, selected without the magnitude law, with the advertised uniform
confidence radius and a budget on the expected number of actual observed flips. -/
theorem confidence_upper : ConfidenceUpperStatement := by
  refine ⟨RepeatSeed,inferInstance,confidenceEstimator,?_⟩
  intro B δ hB hδ hδle μ _
  have hB0 : 0 < B := by linarith
  have hk : 0 < (confidenceCount δ : ℝ) := by exact_mod_cast confidenceCount_pos δ
  by_cases hg : 4 ≤ B/(confidenceCount δ : ℝ)
  · rw [confidenceEstimator,ite_eq_left hg]
    constructor
    · intro q
      apply (repeat_uniformBudget (confidenceRepetitions δ) (budgetLevel (B/(confidenceCount δ : ℝ))) μ q).trans
      apply ENNReal.ofReal_le_ofReal
      have hb := (le_div_iff₀ hk).mp (budgetLevel_bounds _ hg).1
      change (confidenceCount δ : ℝ)*(4*(2 : ℝ)^(budgetLevel (B/(confidenceCount δ : ℝ)))) ≤ B
      nlinarith
    · intro q
      apply le_trans (failureProbability_mono μ _ q ?_)
        ((repeat_failure_le (confidenceRepetitions δ) (budgetLevel (B/(confidenceCount δ : ℝ))) μ q).trans
          (confidence_amplification_level hδ hδle))
      have hm := group_modulus_le μ B δ hB0 hδ hδle hg
      linarith
  · rw [confidenceEstimator,ite_eq_right hg]
    constructor
    · intro q
      rw [idleRepeat_expectedWork_zero]
      exact bot_le
    · exact idleRepeat_confidence μ δ _ (small_group_radius μ B δ hB0 hδ hδle (lt_of_not_ge hg))

theorem minimax_confidence_upper (μ : Measure Gap) [IsProbabilityMeasure μ]
    (B δ : ℝ) (hB : 1 ≤ B) (hδ : 0 < δ) (hδle : δ ≤ 1/4) :
    minimaxConfidenceRadius μ B δ ≤ ENNReal.ofReal (8192*modulus μ (confidenceScale B δ)) := by
  obtain ⟨R,mR,rule,h⟩ := confidence_upper
  have hu := h B δ hB hδ hδle μ
  apply sInf_le
  refine ⟨R,mR,rule B δ,8192*modulus μ (confidenceScale B δ),?_,hu.1,hu.2,rfl⟩
  exact mul_nonneg (by norm_num) (modulus_nonneg μ (Real.sqrt_nonneg _))

theorem confidence_characterization : ConfidenceCharacterizationStatement := by
  intro μ _ B δ hB hδ hδle
  exact ⟨minimax_confidence_lower μ B δ hB hδ hδle,minimax_confidence_upper μ B δ hB hδ hδle⟩

end ThresholdHC.Confidence
