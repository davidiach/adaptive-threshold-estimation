import ThresholdHC.RareAboveTwo.FixedBounds
import ThresholdHC.RareAboveTwo.BudgetMath
import ThresholdHC.RareAboveTwo.Nonvacuity

/-! The law-independent upper family, including the zero-work saturation regime. -/
noncomputable section
namespace ThresholdHC.RareAboveTwo
open MeasureTheory ProbabilityTheory Set ThresholdHC.CriticalEntropy ThresholdHC.Uniform713
open ThresholdHC.Tier2 ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.Tier6 ThresholdHC.ObservableSimulation
open ThresholdHC.BlindUpper
open scoped ENNReal

def idleEstimator (ρ : ℝ) : AdaptiveEstimator RareSeed where
  randomLaw := rareSeedLaw
  probability := rareSeedLaw_probability
  policy := fun _ _ => none
  policy_measurable := fun _ _ => measurableSet_eq_fun measurable_const measurable_const
  output := fun _ => ρ/2
  output_measurable := measurable_const

theorem idle_work (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (ρ : ℝ) :
    expectedWork μ (idleEstimator ρ) q = 0 := by
  rw [original_expectedWork_simulation]
  have hz (z : RareSeed × (ℕ → ℕ → Bool)) :
      totalProcessWork (populationPath ((idleEstimator ρ).policy z.1) z.2) = 0 := by
    rw [populationPath_none _ _ rfl]
    simp [totalProcessWork,ThresholdHC.workOf,processPrefix]
  simp_rw [hz]
  simp

theorem idle_risk (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ : ℝ) :
    rareRisk μ (idleEstimator ρ) ρ ≤ ENNReal.ofReal (ρ/2) := by
  apply iSup_le
  intro q
  apply iSup_le
  intro hq
  have hmean := (signMean_bounds μ q).1
  change signMean μ q.val ≤ ρ at hq
  have habs : |ρ/2-signMean μ q.val| ≤ ρ/2 := abs_le.mpr (by constructor <;> linarith)
  have he : squaredRisk (experimentLaw μ (idleEstimator ρ) q)
      (populationOutput (idleEstimator ρ)) (signMean μ q.val) =
      ENNReal.ofReal ((ρ/2-signMean μ q.val)^2) := by
    simp [squaredRisk,populationOutput,idleEstimator]
  unfold rootMeanRisk
  rw [he,← sq_abs (ρ/2-signMean μ q.val),ofReal_square_rpow_half _ (abs_nonneg _)]
  exact ENNReal.ofReal_le_ofReal habs

def budgetEstimator (W a ρ B : ℝ) : AdaptiveEstimator RareSeed :=
  if 224*(W/a^2)/ρ ≤ B then fixedEstimator a ρ (batchIndex (W/a^2) B) else idleEstimator ρ

theorem budget_guarantees (μ : Measure Gap) [IsProbabilityMeasure μ]
    (α W a ρ B : ℝ) (hα : 2 < α) (hW : 0 < W) (ha : 0 < a) (ha' : a ≤ 1/2)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hB : 0 < B) (hm : PowerMargin μ α a)
    (hwork : ∀ q : SignLaw, RarePrior μ ρ q →
      (∫⁻ z, stoppedProcedureWork (rareUnbiasedProcedure a ρ) z ∂samplingMeasure (originalPopulationTapeLaw μ q)) ≤
        ENNReal.ofReal (W/a^2)) :
    RareBudget μ (budgetEstimator W a ρ B) ρ B ∧
      rareRisk μ (budgetEstimator W a ρ B) ρ ≤ ENNReal.ofReal (min (ρ/2) (upperRate W a ρ B)) := by
  by_cases hlarge : 224*(W/a^2)/ρ ≤ B
  · rw [budgetEstimator,ite_eq_left hlarge]
    obtain ⟨hbudget,hsecond,hrate⟩ := large_budget_bounds W a ρ B hW ha hρ hρ1 hlarge
    refine ⟨?_,?_⟩
    · intro q hq
      exact (fixed_expectedWork_bound μ q a ρ (W/a^2) (hwork q hq) _).trans
        (ENNReal.ofReal_le_ofReal hbudget)
    · rw [min_eq_right hrate]
      apply iSup_le
      intro q
      apply iSup_le
      intro hq
      have hs := (fixed_squaredRisk_bound μ α a ρ hα ha ha' hρ hρ1 hm q hq _).trans
        (ENNReal.ofReal_le_ofReal hsecond)
      have hr := ENNReal.rpow_le_rpow hs (by norm_num : (0 : ℝ) ≤ 1/2)
      rw [ofReal_square_rpow_half _ (upperRate_pos W a ρ B hW ha hρ hB).le] at hr
      exact hr
  · rw [budgetEstimator,ite_eq_right hlarge]
    refine ⟨?_,?_⟩
    · intro q _
      rw [idle_work]
      exact bot_le
    · rw [min_eq_left (small_budget_bound W a ρ B hW ha hρ hB (lt_of_not_ge hlarge))]
      exact idle_risk μ ρ

theorem above_two_upper : AboveTwoUpperStatement := by
  intro α hα
  obtain ⟨W,hW,hwork⟩ := uniform_unbiased_work α hα
  refine ⟨rateCoefficient W,by unfold rateCoefficient; positivity,RareSeed,inferInstance,budgetEstimator W,?_⟩
  intro a ρ B ha ha' hρ hρ' hB μ _ hm
  exact budget_guarantees μ α W a ρ B hα hW ha ha' hρ (by linarith) (by linarith) hm
    (fun q hq => hwork a ρ ha ha' hρ (by linarith) μ hm q hq)

end ThresholdHC.RareAboveTwo
