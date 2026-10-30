import ThresholdHC.Genie.DirectRiskOptimization
import ThresholdHC.Genie.InfiniteMidpoint
import ThresholdHC.Genie.RevealBellman
import ThresholdHC.Genie.RevealTruncation
import ThresholdHC.Genie.CapLimits

/-! A certified genie information price yields the optimized direct lower
bound in the original unrestricted adaptive minimax experiment. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.Genie
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.StoppingProgram

theorem direct_pair_risk (μ : Measure Gap) [IsProbabilityMeasure μ]
    (ρ B : ℝ) (hρ : 0 ≤ ρ) (hB : 0 ≤ B) (q r : SignLaw)
    (hq : RarePrior μ ρ q) (hr : RarePrior μ ρ r) (hgap : signMean μ q.val ≤ signMean μ r.val)
    (κ : ℝ) (hκ : 0 ≤ κ) (hK : infiniteInformationRatio μ (midpointFourPriors q r) ≤ ENNReal.ofReal κ)
    (s : ℝ) (hs : s ∈ Set.Icc (0:ℝ) 1) :
    ENNReal.ofReal (directRiskProfile (signMean μ r.val-signMean μ q.val) (B*κ) s) ≤
      rareMinimaxRisk μ ρ B := by
  change 0 ≤ s ∧ s ≤ 1 at hs
  by_cases hpos : 0 ≤ 1-s^2*(B*κ)/4
  swap
  · simp only [directRiskProfile,max_eq_right (le_of_not_ge hpos),mul_zero,ENNReal.ofReal_zero]
    exact bot_le
  let q' := contractPrior q r s hs
  let r' := contractPrior r q s hs
  have hq' := contractPrior_rare μ q r hq hr s hs
  have hr' := contractPrior_rare μ r q hr hq s hs
  have hegap : signMean μ r'.val-signMean μ q'.val = s*(signMean μ r.val-signMean μ q.val) :=
    contractPrior_gap μ q r s hs
  have hg : signMean μ q'.val ≤ signMean μ r'.val := by
    apply sub_nonneg.mp
    rw [hegap]
    exact mul_nonneg hs.1 (sub_nonneg.mpr hgap)
  apply le_sInf
  rintro t ⟨R,mR,A,hbudget,rfl⟩
  letI := mR
  apply prefix_lower_transfer μ A ρ B hρ hB hbudget q' r' hq' hr'
  intro N
  have hw : expectedWork μ A (midpointPrior q' r') ≤ ENNReal.ofReal B := by
    rw [show midpointPrior q' r' = midpointPrior q r from contractPrior_midpoint q r s hs]
    exact hbudget _ (mixPrior_rare μ q r hq hr (1/2) (by norm_num))
  have hl := observable_prefix_risk μ A q' r' N B hB hw hg
    (prefixTruncation A ρ N) (measurable_prefixTruncation A ρ N)
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) hl
  have hKN : (informationRatio μ N (midpointFourPriors q r)).toReal ≤ κ := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      ((informationRatio_le_infinite μ N _).trans hK)
    simpa only [ENNReal.toReal_ofReal hκ] using hh
  have hKR : (informationRatio μ N (midpointFourPriors q' r')).toReal =
      s^2*(informationRatio μ N (midpointFourPriors q r)).toReal := by
    change (informationRatio μ N (midpointFourPriors (contractPrior q r s hs) (contractPrior r q s hs))).toReal = _
    rw [contractPrior_informationRatio,ENNReal.toReal_mul,ENNReal.toReal_ofReal (sq_nonneg s)]
  rw [hegap,hKR,directRiskProfile,max_eq_left hpos]
  have hsmall := mul_le_mul_of_nonneg_left hKN (sq_nonneg s)
  have hBsmall := mul_le_mul_of_nonneg_right hsmall hB
  have hp : 0 ≤ s*(signMean μ r.val-signMean μ q.val)/2 :=
    div_nonneg (mul_nonneg hs.1 (sub_nonneg.mpr hgap)) (by norm_num)
  have hh : 1-s^2*(B*κ)/4 ≤ 1-(s^2*(informationRatio μ N (midpointFourPriors q r)).toReal)*B/4 := by
    nlinarith [hBsmall]
  have hmul := mul_le_mul_of_nonneg_left hh hp
  convert hmul using 1 <;> ring

theorem genie_direct_risk (μ : Measure Gap) [IsProbabilityMeasure μ]
    (ρ B : ℝ) (hρ : 0 ≤ ρ) (hB : 0 ≤ B) (Q : FourPriors) (hQ : Admissible μ ρ Q)
    (hgap : signMean μ Q.low.val ≤ signMean μ Q.high.val)
    (N : ℕ) (hN : 0 < N) (κ : ℝ) (hκ : 0 ≤ κ)
    (hprice : genieInformationRatio μ N Q ≤ ENNReal.ofReal κ)
    (s : ℝ) (hs : s ∈ Set.Icc (0:ℝ) 1) :
    ENNReal.ofReal (directRiskProfile ((signMean μ Q.high.val-signMean μ Q.low.val)/3) (B*κ) s) ≤
      rareMinimaxRisk μ ρ B := by
  have hA := absorbedPriors_admissible μ Q hQ
  have hK := (absorbedPriors_infiniteInformation_le μ Q).trans
    ((infiniteInformationRatio_le_genie μ N hN Q).trans hprice)
  have hg : signMean μ (absorbedLow Q).val ≤ signMean μ (absorbedHigh Q).val := by
    apply sub_nonneg.mp
    change 0 ≤ signMean μ (absorbedPriors Q).high.val-signMean μ (absorbedPriors Q).low.val
    rw [absorbedPriors_gap]
    positivity
  have h := direct_pair_risk μ ρ B hρ hB (absorbedLow Q) (absorbedHigh Q)
    hA.1 hA.2.1 hg κ hκ hK s hs
  have he : signMean μ (absorbedHigh Q).val-signMean μ (absorbedLow Q).val =
      (signMean μ Q.high.val-signMean μ Q.low.val)/3 := by
    have hh := absorbedPriors_gap μ Q
    change signMean μ (absorbedHigh Q).val-signMean μ (absorbedLow Q).val = _ at hh
    linarith
  rwa [he] at h

theorem genie_direct_squared_risk (μ : Measure Gap) [IsProbabilityMeasure μ]
    (ρ B : ℝ) (hρ : 0 ≤ ρ) (hB : 0 ≤ B) (Q : FourPriors) (hQ : Admissible μ ρ Q)
    (hgap : signMean μ Q.low.val ≤ signMean μ Q.high.val)
    (N : ℕ) (hN : 0 < N) (κ : ℝ) (hκ : 0 ≤ κ)
    (hprice : genieInformationRatio μ N Q ≤ ENNReal.ofReal κ) :
    ENNReal.ofReal (directRiskSquared ((signMean μ Q.high.val-signMean μ Q.low.val)/3) (B*κ)) ≤
      rareMinimaxRisk μ ρ B ^ 2 := by
  have h := genie_direct_risk μ ρ B hρ hB Q hQ hgap N hN κ hκ hprice
    (directRiskScale (B*κ)) (directRiskScale_mem (B*κ))
  have hp : 0 ≤ directRiskProfile ((signMean μ Q.high.val-signMean μ Q.low.val)/3) (B*κ)
      (directRiskScale (B*κ)) := by
    unfold directRiskProfile
    exact mul_nonneg (div_nonneg (mul_nonneg (directRiskScale_mem (B*κ)).1
      (div_nonneg (sub_nonneg.mpr hgap) (by norm_num))) (by norm_num)) (le_max_right _ _)
  have hh := pow_le_pow_left₀ (by positivity) h 2
  rwa [←ENNReal.ofReal_pow hp,directRiskProfile_square _ _ (mul_nonneg hB hκ)] at hh

theorem genie_bellman_direct_squared_risk (μ : Measure Gap) [IsProbabilityMeasure μ]
    (ρ B : ℝ) (hρ : 0 ≤ ρ) (hB : 0 ≤ B) (Q : FourPriors) (hQ : Admissible μ ρ Q)
    (hgap : signMean μ Q.low.val ≤ signMean μ Q.high.val) (hC : latentDivergence μ Q ≠ ⊤)
    (N : ℕ) (hN : 0 < N) (κ : ℝ) (hκ : 0 ≤ κ)
    (hroot : rootBellman (genieReward μ Q N) (prefixCoefficient μ Q.work) κ (N-1) ≤ 0) :
    ENNReal.ofReal (directRiskSquared ((signMean μ Q.high.val-signMean μ Q.low.val)/3) (B*κ)) ≤
      rareMinimaxRisk μ ρ B ^ 2 := by
  exact genie_direct_squared_risk μ ρ B hρ hB Q hQ hgap N hN κ hκ
    ((genieInformationRatio_bellman_certificate μ N Q hN hC κ hκ).mpr hroot)

end ThresholdHC.Genie
