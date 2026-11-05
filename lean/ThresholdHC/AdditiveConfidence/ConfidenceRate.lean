import ThresholdHC.AdditiveConfidence.ComponentPair
import ThresholdHC.AdditiveConfidence.Submeasures

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace ThresholdHC.AdditiveConfidence
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.CriticalEntropy
open ThresholdHC.ObservableSimulation ThresholdHC.ConfidenceLocalization ThresholdHC.ConfidenceTransfer

/-- Additive confidence localization for finite overlapping components, charged
to the expected work of the original hidden-gap experiment. -/
theorem confidence_rate_of_mixture {I R : Type} [Fintype I] [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (M : GapMixture I μ) (A : AdaptiveEstimator R)
    (ρ b J : I → ℝ) {ρtotal B ε δ : ℝ}
    (hb : ∀ i, 0 < b i) (hJ : ∀ i, 0 < J i) (hB : 0 < B)
    (hδ : 0 < δ) (hδ' : δ ≤ 1/4)
    (hρ : ∑ i, (M.weight i : ℝ)*ρ i ≤ ρtotal)
    (cp : ∀ i, CommonPairBound (M.law i) (ρ i) (b i) (J i))
    (hw : RareBudget μ A ρtotal B)
    (hconf : ∀ u : SignLaw, RarePrior μ ρtotal u →
      ThresholdHC.Confidence.failureProbability μ A u ε ≤ ENNReal.ofReal δ) :
    (∑ i, (M.weight i : ℝ)*min (b i) (Real.sqrt (J i*Real.log (1/δ)/B)))/128 ≤ ε := by
  classical
  let ℓ := Real.log (1/δ)
  have hℓ : 0 < ℓ := ThresholdHC.Confidence.confidence_log_pos hδ hδ'
  choose q r hq hr hqh hrh hsep hloc using
    (fun i => component_pair_uniform (M.law i) (hb i) (hJ i) hB hℓ (cp i))
  have hrare (u : I → SignLaw) (hu : ∀ i, RarePrior (M.law i) (ρ i) (u i))
      (hhalf : ∀ i d, (u i).val d ≤ 1/2) : RarePrior μ ρtotal (M.mixedSign u) := by
    unfold RarePrior
    rw [M.mixedSign_mean u hhalf]
    exact (Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_left (hu i) (M.weight i).property)).trans hρ
  let κ := 42*ℓ/(1024*B)
  have hκ : 0 ≤ κ := by dsimp [κ]; positivity
  have hlocal : LocalNullWorkBound μ (gapParameter false) (gapParameter true)
      (signUnit (M.mixedSign q)) (signUnit (M.mixedSign r)) κ :=
    M.local_bound (gapParameter false) (gapParameter true)
      (measurable_gapParameter false) (measurable_gapParameter true) q r hqh hrh κ hκ hloc
  have hrev : LocalNullWorkBound μ (gapParameter false) (gapParameter true)
      (signUnit (M.mixedSign r)) (signUnit (M.mixedSign q)) κ := by
    intro U E _ _ ν _ proc n hcap
    rw [affinity_symm]
    exact hlocal ν proc n hcap
  have hs : (∑ i, (M.weight i : ℝ)*min (b i) (Real.sqrt (J i*ℓ/B)))/32 ≤
      signMean μ (M.mixedSign r).val-signMean μ (M.mixedSign q).val := by
    rw [M.mixedSign_mean r hrh,M.mixedSign_mean q hqh,← Finset.sum_sub_distrib,
      Finset.sum_div]
    apply Finset.sum_le_sum
    intro i _
    calc
      _ = (M.weight i : ℝ)*(min (b i) (Real.sqrt (J i*ℓ/B))/32) := by ring
      _ ≤ (M.weight i : ℝ)*(signMean (M.law i) (r i).val-signMean (M.law i) (q i).val) :=
        mul_le_mul_of_nonneg_left (hsep i) (M.weight i).property
      _ = _ := by ring
  by_contra! he
  have h := pair_confidence_work μ A (M.mixedSign r) (M.mixedSign q) hB.le hκ hδ hδ'
    (hrare r hr hrh) (hrare q hq hqh) (halfSign_le_half μ _) (halfSign_le_half μ _)
    hrev hw hconf (by dsimp [ℓ] at hs; linarith)
  change ℓ/4 ≤ 16/3*(42*ℓ/(1024*B))*B at h
  field_simp [ne_of_gt hB] at h
  nlinarith only [h,mul_pos hB hℓ]

end ThresholdHC.AdditiveConfidence
