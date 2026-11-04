import ThresholdHC.FiniteQuantile.TailInformation
import ThresholdHC.StoppingProgram.BernoulliFloor

/-! The direct T_h/32 obstruction for the original estimator, including
persistent labels, arbitrary interleaving and an expected-work budget. -/

noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace ThresholdHC.FiniteQuantile
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.StoppingProgram
open ThresholdHC.EntropyTailQuantile

theorem quantile_tail_lower (μ : Measure Gap) [IsProbabilityMeasure μ] (hs : μ.support.Finite)
    {ρ B : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) :
    ENNReal.ofReal (tailModulus (quantileTail μ ρ) (EntropyTailQuantile.budgetScale B) / 32) ≤
      rareMinimaxRisk μ ρ B := by
  let h := EntropyTailQuantile.budgetScale B
  let T := tailModulus (quantileTail μ ρ) h
  have hh : 0 ≤ h := inv_nonneg.mpr (sqrt_nonneg _)
  have hρ1 : ρ ≤ 1 := by linarith
  let low := tailEndpoint μ hρ hρ1 hh false
  let high := tailEndpoint μ hρ hρ1 hh true
  let mid := midpointPrior low high
  have hl : RarePrior μ ρ low := tailEndpoint_rare μ hρ hρ1 hh false
  have hr : RarePrior μ ρ high := tailEndpoint_rare μ hρ hρ1 hh true
  have hm : RarePrior μ ρ mid := mixPrior_rare μ _ _ hl hr (1/2) (by norm_num)
  have hT : 0 ≤ T := tailModulus_nonneg _ hh
  have hgap : signMean μ high.val - signMean μ low.val = T / 8 := by
    rw [tailEndpoint_mean, tailEndpoint_mean]
    simp only [ite_true, Bool.false_eq_true, ite_false]
    dsimp only [T]
    ring
  have hhB : h^2 * B = 1 := by
    dsimp only [h, EntropyTailQuantile.budgetScale]
    rw [inv_pow, sq_sqrt hB.le, inv_mul_cancel₀ hB.ne']
  apply le_sInf
  rintro _ ⟨R, mR, A, hbudget, rfl⟩
  apply prefix_lower_transfer μ A ρ B hρ.le hB.le hbudget low high hl hr
  intro cap
  have hinfo := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (tail_information_ratio μ hs hρ hρ1 hh cap)
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ h^2/4)] at hinfo
  let K := (informationRatio μ cap (midpointFourPriors low high)).toReal
  have hprice : K * B ≤ 1/4 := by
    have hp := mul_le_mul_of_nonneg_right hinfo hB.le
    change K * B ≤ h^2/4 * B at hp
    linarith only [hp, hhB]
  have hmean : signMean μ low.val ≤ signMean μ high.val := sub_nonneg.mp
    (hgap.ge.trans' (div_nonneg hT (by norm_num)))
  have hp := observable_prefix_risk μ A low high cap B hB.le (hbudget mid hm) hmean
    (prefixTruncation A ρ cap) (measurable_prefixTruncation A ρ cap)
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) hp
  rw [hgap]
  change T/32 ≤ T/8/2*(1-K*B/4)
  nlinarith only [mul_le_mul_of_nonneg_right hprice hT, hT]

/-- When h reaches the quantile threshold, the entire quantile tail pays
unit cost, so the tail obstruction controls the full quantile functional. -/
theorem above_threshold_lower (μ : Measure Gap) [IsProbabilityMeasure μ] (hs : μ.support.Finite)
    {ρ B : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B)
    (ht : quantileThreshold μ ρ ≤ EntropyTailQuantile.budgetScale B) :
    ENNReal.ofReal (1/32 : ℝ) * closedQuantileValue μ ρ B ≤ rareMinimaxRisk μ ρ B := by
  have h := quantile_tail_lower μ hs hρ hρ4 hB
  rw [tailModulus_eq_mass _ ((quantileTail_support μ ρ).mono (fun _ hg => hg.trans ht)),
    quantileTail_real_mass μ hρ (by linarith)] at h
  calc
    _ ≤ ENNReal.ofReal (1/32 : ℝ) * ENNReal.ofReal ρ :=
      mul_le_mul' le_rfl (min_le_left _ _)
    _ = ENNReal.ofReal (ρ/32) := by
      rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/32)]
      congr 1
      ring
    _ ≤ _ := h

end ThresholdHC.FiniteQuantile
