import ThresholdHC.EntropyTailLower.FiniteBandApprox
import ThresholdHC.EntropyTailQuantile.ScaleSeparated
import ThresholdHC.EntropyTailQuantile.QuantileTailBound

noncomputable section
open MeasureTheory Set Real
open scoped ENNReal
namespace ThresholdHC.FiniteQuantile
open ThresholdHC.Tier6 ThresholdHC.EntropyTailQuantile

/-- Rounded core entropy on the full prefix ending at the quantile band. -/
def prefixCoreEntropy (μ : Measure Gap) (n : ℕ) : ℝ :=
  costEntropy (fun i : Fin n => μ.real (EntropyTail.band i.val)/(bandEdge i.val)^2)

theorem prefixCoreEntropy_nonneg (μ : Measure Gap) (n : ℕ) : 0 ≤ prefixCoreEntropy μ n :=
  costEntropy_nonneg (fun _ => div_nonneg measureReal_nonneg (sq_nonneg _))

theorem core_entropy_le_prefix (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ : ℝ} {n : ℕ} (hn : bandEdge n < quantileThreshold μ ρ) :
    measureCostEntropy (quantileCore μ ρ) ≤ ENNReal.ofReal (4*prefixCoreEntropy μ n) := by
  rw [measureCostEntropy_eq_prefix_of_support _ (quantileCore_support μ ρ) hn]
  apply ENNReal.ofReal_le_ofReal
  unfold prefixCoreEntropy
  rw [← costEntropy_smul]
  apply costEntropy_mono (fun i => bandCost_nonneg _ _)
  intro i
  have h := (bandCost_mono (show quantileCore μ ρ ≤ μ from Measure.sub_le) i.val).trans
    (EntropyTailLower.canonical_bandCost_upper μ i.val)
  convert h using 1; dsimp [bandEdge]; ring

theorem closedQuantile_le_tail_core (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B : ℝ} (hρ : 0 ≤ ρ) {n : ℕ}
    (hn : bandEdge n < quantileThreshold μ ρ) :
    closedQuantileValue μ ρ B ≤ ENNReal.ofReal
      (tailModulus (quantileTail μ ρ) (EntropyTailQuantile.budgetScale B) +
        2*min ρ (sqrt (ρ*prefixCoreEntropy μ n/B))) := by
  let h := EntropyTailQuantile.budgetScale B
  let F := prefixCoreEntropy μ n
  let T := tailModulus (quantileTail μ ρ) h
  have hh : 0 ≤ h := inv_nonneg.mpr (sqrt_nonneg _)
  have hF : 0 ≤ F := prefixCoreEntropy_nonneg _ _
  have hT : 0 ≤ T := tailModulus_nonneg _ hh
  change min _ (ENNReal.ofReal T + ENNReal.ofReal h *
    (ENNReal.ofReal ρ * measureCostEntropy (quantileCore μ ρ)) ^ (1/2 : ℝ)) ≤
    ENNReal.ofReal (T+2*min ρ (sqrt (ρ*F/B)))
  rcases le_total ρ (sqrt (ρ*F/B)) with hl | hr
  · rw [min_eq_left hl]
    exact (min_le_left _ _).trans (ENNReal.ofReal_le_ofReal (by linarith))
  · rw [min_eq_right hr]
    apply (min_le_right _ _).trans
    rw [ENNReal.ofReal_add hT (by positivity)]
    apply add_le_add le_rfl
    have hγ := core_entropy_le_prefix μ hn
    calc
      _ ≤ ENNReal.ofReal h * (ENNReal.ofReal ρ * ENNReal.ofReal (4*F)) ^ (1/2:ℝ) := by
        gcongr
      _ = ENNReal.ofReal (h * sqrt (ρ*(4*F))) :=
        EntropyTail.entropyTerm_ofReal hh hρ (by positivity)
      _ = ENNReal.ofReal (2*sqrt (ρ*F/B)) := by
        apply congrArg ENNReal.ofReal
        rw [show ρ*(4*F) = 4*(ρ*F) by ring, sqrt_mul (by norm_num : (0:ℝ) ≤ 4),
          sqrt_div (mul_nonneg hρ hF)]
        rw [show sqrt (4:ℝ) = 2 by norm_num]
        dsimp [h, EntropyTailQuantile.budgetScale]
        ring

theorem quantileTail_threshold_floor (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ h : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hh : 0 ≤ h) (ht : h ≤ quantileThreshold μ ρ) :
    h / quantileThreshold μ ρ * ρ ≤ tailModulus (quantileTail μ ρ) h := by
  let ν := quantileTail μ ρ
  let t := quantileThreshold μ ρ
  let : IsFiniteMeasure ν := isFiniteMeasure_of_le μ (quantileTail_le μ hρ hρ1)
  have htpos : 0 < t := (quantileThreshold_properties μ hρ hρ1).1
  calc
    _ = ∫ _ : Gap, h/t ∂ν := by
      rw [integral_const, smul_eq_mul, quantileTail_real_mass μ hρ hρ1, mul_comm]
    _ ≤ _ := by
      apply integral_mono_ae (integrable_const _) (tailKernel_integrable ν hh)
      filter_upwards [quantileTail_support μ ρ] with g hg
      exact le_min ((div_le_one htpos).mpr ht)
        (div_le_div_of_nonneg_left hh g.property.1 hg)

end ThresholdHC.FiniteQuantile
