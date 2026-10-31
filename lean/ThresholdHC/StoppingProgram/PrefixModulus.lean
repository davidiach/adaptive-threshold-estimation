import ThresholdHC.StoppingProgram.PrefixRisk
import ThresholdHC.StoppingProgram.ContractionScale
import ThresholdHC.StoppingProgram.MidpointComparison

/-! The finite-prefix minimax comparison uses the actual adaptive population
experiment and the globally rare class, with the paper's factor eight. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.StoppingProgram
open ThresholdHC.CriticalEntropy ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.RareAboveTwo

theorem prefix_pair_modulus {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    (ρ B : ℝ) (hB : 0 ≤ B) (hbudget : RareBudget μ A ρ B)
    (N : ℕ) (f : R × (Fin N → Option Bool) → ℝ) (hf : Measurable f)
    (T : ℝ≥0∞) (hT : ∀ u : SignLaw, RarePrior μ ρ u →
      rootMeanRisk (observablePrefixLaw μ A u N) f (signMean μ u.val) ≤ T)
    (q r : SignLaw) (hq : RarePrior μ ρ q) (hr : RarePrior μ ρ r) :
    ENNReal.ofReal (3/8:ℝ)*dualRatio μ B N (midpointFourPriors q r)^(1/(2:ℝ)) ≤ T := by
  by_cases hgap : signMean μ q.val ≤ signMean μ r.val
  swap
  · have he : ENNReal.ofReal (signMean μ r.val-signMean μ q.val) = 0 :=
      ENNReal.ofReal_eq_zero.mpr (by linarith)
    simp only [dualRatio,midpointFourPriors,he,zero_pow (by norm_num : (2:ℕ) ≠ 0),
      ENNReal.zero_div,ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ) < 1/2),mul_zero]
    exact bot_le
  let K := (informationRatio μ N (midpointFourPriors q r)).toReal
  let x := B*K
  have hx : 0 ≤ x := mul_nonneg hB ENNReal.toReal_nonneg
  let s := 1/Real.sqrt (4+x)
  have hs : 0 ≤ s ∧ s ≤ 1 := (contraction_scale x hx).1
  have hsmall : s^2*x ≤ 1 := (contraction_scale x hx).2
  let q' := contractPrior q r s hs
  let r' := contractPrior r q s hs
  have hq' := contractPrior_rare μ q r hq hr s hs
  have hr' := contractPrior_rare μ r q hr hq s hs
  have hmid := mixPrior_rare μ q r hq hr (1/2) (by norm_num)
  have hw : expectedWork μ A (midpointPrior q' r') ≤ ENNReal.ofReal B := by
    rw [contractPrior_midpoint]
    exact hbudget _ hmid
  have hg : signMean μ q'.val ≤ signMean μ r'.val := by
    apply sub_nonneg.mp
    rw [contractPrior_gap]
    exact mul_nonneg hs.1 (sub_nonneg.mpr hgap)
  have hl := (observable_prefix_risk μ A q' r' N B hB hw hg f hf).trans
    (max_le (hT q' hq') (hT r' hr'))
  have hratio : (informationRatio μ N (midpointFourPriors q' r')).toReal = s^2*K := by
    rw [contractPrior_informationRatio,ENNReal.toReal_mul,ENNReal.toReal_ofReal (sq_nonneg s)]
  rw [midpoint_dual_root μ B hB N q r hgap,← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3/8)]
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) hl
  change (3/8)*((signMean μ r.val-signMean μ q.val)/Real.sqrt (4+x)) ≤ _
  rw [hratio,contractPrior_gap]
  have hh : 3/4 ≤ 1-s^2*K*B/4 := by dsimp only [x] at hsmall; nlinarith [hsmall]
  have hp := mul_le_mul_of_nonneg_left hh
    (div_nonneg (mul_nonneg hs.1 (sub_nonneg.mpr hgap)) (by norm_num : (0:ℝ) ≤ 2))
  calc
    _ = (s*(signMean μ r.val-signMean μ q.val)/2)*(3/4) := by dsimp only [s]; ring
    _ ≤ _ := hp

theorem prefix_program_bound {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    (ρ B : ℝ) (hρ : 0 < ρ) (hρhalf : ρ ≤ 1/2) (hB : 0 < B) (hbudget : RareBudget μ A ρ B)
    (N : ℕ) (f : R × (Fin N → Option Bool) → ℝ) (hf : Measurable f)
    (T : ℝ≥0∞) (hT : ∀ u : SignLaw, RarePrior μ ρ u →
      rootMeanRisk (observablePrefixLaw μ A u N) f (signMean μ u.val) ≤ T) :
    programValue μ ρ B N ≤ 8*T := by
  have hmid : ENNReal.ofReal (3/8:ℝ)*midpointValue μ ρ B N ≤ T := by
    unfold midpointValue midpointSquared
    simp_rw [ENNReal.iSup_rpow_of_pos (by norm_num : (0:ℝ) < 1/2),ENNReal.mul_iSup]
    apply iSup_le
    intro q
    apply iSup_le
    intro r
    apply iSup_le
    intro hq
    apply iSup_le
    intro hr
    exact prefix_pair_modulus μ A ρ B hB.le hbudget N f hf T hT q r hq hr
  have hm := mul_le_mul_right hmid (8:ℝ≥0∞)
  have he : (8:ℝ≥0∞)*ENNReal.ofReal (3/8:ℝ) = 3 := by
    rw [← ENNReal.ofReal_ofNat 8,← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 8)]
    norm_num
  rw [← mul_assoc,he] at hm
  exact (midpoint_comparison μ ρ B N hρ hρhalf hB).2.trans hm

end ThresholdHC.StoppingProgram
