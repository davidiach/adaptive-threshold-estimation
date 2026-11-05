import ThresholdHC.AdditiveConfidence.LocalBound

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace ThresholdHC.AdditiveConfidence
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.CriticalEntropy
open ThresholdHC.ObservableSimulation ThresholdHC.ConfidenceLocalization ThresholdHC.ConfidenceTransfer

theorem component_pair_uniform (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ b J B ℓ : ℝ} (hb : 0 < b) (hJ : 0 < J) (hB : 0 < B) (hℓ : 0 < ℓ)
    (cp : CommonPairBound μ ρ b J) :
    ∃ q r : SignLaw, RarePrior μ ρ q ∧ RarePrior μ ρ r ∧
      (∀ d, q.val d ≤ 1/2) ∧ (∀ d, r.val d ≤ 1/2) ∧
      min b (Real.sqrt (J*ℓ/B))/32 ≤ signMean μ r.val-signMean μ q.val ∧
      LocalNullWorkBound μ (gapParameter false) (gapParameter true) (signUnit q) (signUnit r)
        (42*ℓ/(1024*B)) := by
  let z := Real.sqrt (J*ℓ/B)
  have hz : 0 < z := Real.sqrt_pos.mpr (by positivity)
  have hz2 : z^2 = J*ℓ/B := Real.sq_sqrt (by positivity)
  let u := min b z
  have hu : 0 < u := lt_min hb hz
  have hub : u ≤ b := min_le_left _ _
  have huz : u ≤ z := min_le_right _ _
  have hu2 : u^2 ≤ z^2 := by nlinarith only [mul_nonneg (sub_nonneg.mpr huz) (add_nonneg hz.le hu.le)]
  obtain ⟨q,r,hq,hr,hqh,hrh,hsep,hloc⟩ := cp (u/32) (by positivity) (by linarith)
  refine ⟨q,r,hq,hr,hqh,hrh,hsep,?_⟩
  have hk : 42*(u/32)^2/J ≤ 42*ℓ/(1024*B) := by
    rw [hz2] at hu2
    have h := (le_div_iff₀ hB).mp hu2
    apply (div_le_div_iff₀ hJ (by positivity : 0 < 1024*B)).mpr
    nlinarith only [h]
  intro R E _ _ ν _ A n hcap
  exact (hloc ν A n hcap).trans
    (mul_le_mul_of_nonneg_right hk ENNReal.toReal_nonneg)

end ThresholdHC.AdditiveConfidence
