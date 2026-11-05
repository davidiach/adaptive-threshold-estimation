import ThresholdHC.RMSLocalization.CommonPair

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace ThresholdHC.RMSLocalization
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.CriticalEntropy
open ThresholdHC.ObservableSimulation ThresholdHC.ConfidenceTransfer ThresholdHC.ConfidenceLocalization
open ThresholdHC.AdditiveConfidence

theorem rms_rate_of_mixture {I R : Type} [Fintype I] [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (M : GapMixture I μ) (A : AdaptiveEstimator R)
    (ρ b J : I → ℝ) {ρtotal B : ℝ}
    (hb : ∀ i, 0 < b i) (hJ : ∀ i, 0 < J i) (hB : 0 < B)
    (hρ : ∑ i, (M.weight i : ℝ)*ρ i ≤ ρtotal)
    (cp : ∀ i, CommonPairBound (M.law i) (ρ i) (b i) (J i))
    (hw : RareBudget μ A ρtotal B) :
    ENNReal.ofReal ((∑ i, (M.weight i : ℝ)*min (b i) (Real.sqrt (J i/B)))/128) ≤ rareRisk μ A ρtotal := by
  classical
  have hp := fun i => component_pair_uniform (M.law i) (hb i) (hJ i) hB (by norm_num : (0 : ℝ) < 1) (cp i)
  simp only [mul_one] at hp
  choose q r hq hr hqh hrh hsep hloc using hp
  have hrare (u : I → SignLaw) (hu : ∀ i, RarePrior (M.law i) (ρ i) (u i))
      (hhalf : ∀ i d, (u i).val d ≤ 1/2) : RarePrior μ ρtotal (M.mixedSign u) := by
    unfold RarePrior
    rw [M.mixedSign_mean u hhalf]
    exact (Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_left (hu i) (M.weight i).property)).trans hρ
  let κ := 42/(1024*B)
  have hκ : 0 ≤ κ := by dsimp [κ]; positivity
  have hlocal : LocalNullWorkBound μ (gapParameter false) (gapParameter true)
      (signUnit (M.mixedSign q)) (signUnit (M.mixedSign r)) κ :=
    M.local_bound (gapParameter false) (gapParameter true)
      (measurable_gapParameter false) (measurable_gapParameter true) q r hqh hrh κ hκ hloc
  have hs : (∑ i, (M.weight i : ℝ)*min (b i) (Real.sqrt (J i/B)))/32 ≤
      signMean μ (M.mixedSign r).val-signMean μ (M.mixedSign q).val := by
    rw [M.mixedSign_mean r hrh,M.mixedSign_mean q hqh,← Finset.sum_sub_distrib,
      Finset.sum_div]
    apply Finset.sum_le_sum
    intro i _
    calc
      _ = (M.weight i : ℝ)*(min (b i) (Real.sqrt (J i/B))/32) := by ring
      _ ≤ (M.weight i : ℝ)*(signMean (M.law i) (r i).val-signMean (M.law i) (q i).val) :=
        mul_le_mul_of_nonneg_left (hsep i) (M.weight i).property
      _ = _ := by ring
  by_cases hzero : (∑ i, (M.weight i : ℝ)*min (b i) (Real.sqrt (J i/B))) ≤ 0
  · rw [ENNReal.ofReal_eq_zero.mpr (div_nonpos_of_nonpos_of_nonneg hzero (by norm_num))]
    exact bot_le
  have hinfo : 2*κ*B ≤ (1/10 : ℝ) := by
    have he : 2*κ*B = (21/256 : ℝ) := by
      dsimp [κ]
      field_simp [ne_of_gt hB]
      norm_num
    rw [he]
    norm_num
  have h := pair_rms_risk μ A (M.mixedSign q) (M.mixedSign r)
    (div_pos (lt_of_not_ge hzero) (by norm_num)) hB.le hκ
    (hrare q hq hqh) (hrare r hr hrh) (halfSign_le_half μ _) (halfSign_le_half μ _)
    hlocal hw hinfo hs
  convert h using 1
  congr 1
  ring

end ThresholdHC.RMSLocalization
