import ThresholdHC.ConfidenceProgram.Midpoint
import ThresholdHC.ConfidenceTransfer.CommonPairRate
import ThresholdHC.Genie.CapLimits
import ThresholdHC.Genie.InfiniteDuality
import ThresholdHC.Genie.OptimizedBrackets
import ThresholdHC.EntropyTailSharp.Full

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.ConfidenceProgram
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo
open ThresholdHC.Genie ThresholdHC.StoppingProgram ThresholdHC.ConfidenceTransfer ThresholdHC.ObservableSimulation

/-- Every four-prior certificate, including a singular reference, bounds the
confidence radius after adjusting the effective budget. -/
theorem quartet_confidence {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) {ρ B δ ε : ℝ} (hB : 0 < B) (hδ : 0 < δ) (hu : δ ≤ 1/4)
    (hw : RareBudget μ A ρ B)
    (hc : ∀ q : SignLaw, RarePrior μ ρ q → ThresholdHC.Confidence.failureProbability μ A q ε ≤ ENNReal.ofReal δ)
    (Q : FourPriors) (hQ : Admissible μ ρ Q) :
    infiniteDualRatio μ (B/Real.log (1/δ)) Q ≤ ENNReal.ofReal ((30*ε)^2) := by
  let ℓ := Real.log (1/δ)
  have hℓ : 0 < ℓ := ThresholdHC.Confidence.confidence_log_pos hδ hu
  let β := B/ℓ
  have hβ : 0 < β := div_pos hB hℓ
  change infiniteDualRatio μ β Q ≤ _
  by_cases htop : infiniteInformationRatio μ Q = ⊤
  · simp [infiniteDualRatio,htop,(ENNReal.ofReal_pos.mpr hβ).ne']
  let Δ := signMean μ Q.high.val-signMean μ Q.low.val
  by_cases hzero : Δ ≤ 0
  · simp [infiniteDualRatio,show ENNReal.ofReal (signMean μ Q.high.val-signMean μ Q.low.val) = 0
      from ENNReal.ofReal_eq_zero.mpr hzero]
  have hΔ : 0 < Δ := lt_of_not_ge hzero
  let K := (infiniteInformationRatio μ Q).toReal
  have hK : 0 ≤ K := ENNReal.toReal_nonneg
  have hKeq := ENNReal.ofReal_toReal htop
  let v := 1+6*β*K
  have hv1 : 1 ≤ v := by dsimp [v]; nlinarith [mul_nonneg hβ.le hK]
  let c := Real.sqrt v
  have hc1 : 1 ≤ c := Real.one_le_sqrt.mpr hv1
  have hc0 : 0 < c := by linarith
  have hc2 : c^2 = v := Real.sq_sqrt (by linarith)
  let a := 1/c
  have ha : 0 < a := one_div_pos.mpr hc0
  have ha1 : a ≤ 1 := (div_le_one hc0).2 hc1
  have hac : a*c = 1 := div_mul_cancel₀ _ hc0.ne'
  have hav : a^2*(1+6*β*K) = 1 := by change a^2*v = 1; rw [← hc2,← mul_pow,hac,one_pow]
  let q := absorbedLow Q
  let r := absorbedHigh Q
  let q' := contractPrior q r a ⟨ha.le,ha1⟩
  let r' := contractPrior r q a ⟨ha.le,ha1⟩
  have had := absorbedPriors_admissible μ Q hQ
  have hq := contractPrior_rare μ q r had.1 had.2.1 a ⟨ha.le,ha1⟩
  have hr := contractPrior_rare μ r q had.2.1 had.1 a ⟨ha.le,ha1⟩
  have hsep : signMean μ r'.val-signMean μ q'.val = a*(Δ/3) := by
    rw [show signMean μ r'.val-signMean μ q'.val = a*(signMean μ r.val-signMean μ q.val) from
      contractPrior_gap μ q r a ⟨ha.le,ha1⟩]
    have h := absorbedPriors_gap μ Q
    change signMean μ r.val-signMean μ q.val = (1/3)*Δ at h
    rw [h]; ring
  have hprice (n : ℕ) : informationRatio μ n (midpointFourPriors q' r') ≤ ENNReal.ofReal (a^2*K) := by
    rw [show informationRatio μ n (midpointFourPriors q' r') = _ from
      contractPrior_informationRatio μ n q r a ⟨ha.le,ha1⟩,ENNReal.ofReal_mul (sq_nonneg a)]
    exact mul_le_mul_right ((absorbedPriors_informationRatio_le μ n Q).trans
      ((informationRatio_le_infinite μ n Q).trans_eq hKeq.symm)) _
  have hl : LocalReferenceWorkBound μ (gapParameter false) (gapParameter true) (signUnit r') (signUnit q') (a^2*K/2) :=
    midpoint_reference_bound μ q' r' (mul_nonneg (sq_nonneg _) hK) hprice
  have hsmall : a*Δ ≤ 12*ε := by
    by_contra! hx
    have h := pair_reference_confidence_work μ A r' q' hB.le (by positivity : 0 ≤ a^2*K/2)
      hδ hu hr hq hl hw hc (by rw [hsep]; linarith)
    change ℓ/4 ≤ (8/3)*(a^2*K/2)*B at h
    have hB' : β*ℓ = B := div_mul_cancel₀ _ hℓ.ne'
    rw [← hB'] at h
    have hs : a^2*K*β ≤ 1/6 := by nlinarith only [hav,sq_nonneg a]
    nlinarith only [h,mul_le_mul_of_nonneg_right hs hℓ.le,hℓ]
  have hd : Δ ≤ (12*ε)*c := by
    have h := mul_le_mul_of_nonneg_right hsmall hc0.le
    calc Δ = (a*Δ)*c := by rw [mul_comm a Δ,mul_assoc,hac,mul_one]
         _ ≤ _ := h
  have hgap := pow_le_pow_left₀ hΔ.le hd 2
  rw [mul_pow,hc2] at hgap
  have hpos : 0 < 4+β*K := by positivity
  have hfactor : 144*v ≤ 900*(4+β*K) := by dsimp [v]; nlinarith only [mul_nonneg hβ.le hK]
  have hdiv : Δ^2/(4+β*K) ≤ (30*ε)^2 := (div_le_iff₀ hpos).2
    (by nlinarith only [hgap,mul_le_mul_of_nonneg_right hfactor (sq_nonneg ε)])
  have hden : 4+ENNReal.ofReal β*infiniteInformationRatio μ Q = ENNReal.ofReal (4+β*K) := by
    rw [← hKeq,← ENNReal.ofReal_mul hβ.le,← ENNReal.ofReal_ofNat 4,← ENNReal.ofReal_add (by norm_num) (mul_nonneg hβ.le hK)]
  change ENNReal.ofReal Δ ^2/(4+ENNReal.ofReal β*infiniteInformationRatio μ Q) ≤ _
  rw [hden,← ENNReal.ofReal_pow hΔ.le,← ENNReal.ofReal_div_of_pos hpos]
  exact ENNReal.ofReal_le_ofReal hdiv

theorem stopping_confidence_lower (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ B δ : ℝ}
    (hr : 0 < ρ) (hr' : ρ ≤ 1/2) (hb : 0 < B) (hd : 0 < δ) (hd' : δ ≤ 1/4) :
    infiniteProgramValue μ ρ (B/Real.log (1/δ))/30 ≤ rareConfidenceRadius μ ρ B δ := by
  let β := B/Real.log (1/δ)
  have hβ : 0 < β := div_pos hb (ThresholdHC.Confidence.confidence_log_pos hd hd')
  apply le_sInf
  rintro t ⟨R,mR,A,ε,hε,hw,hc,rfl⟩
  have h : infiniteProgramValue μ ρ β ^2 ≤ ENNReal.ofReal ((30*ε)^2) := by
    rw [(infinite_four_prior_duality μ hr hr' hβ).1]
    apply iSup_le; intro Q; apply iSup_le; intro hQ
    exact quartet_confidence μ A hb hd hd' hw hc Q hQ
  have hroot := ENNReal.rpow_le_rpow h (by norm_num : (0:ℝ) ≤ 1/2)
  rw [← ENNReal.rpow_two,← ENNReal.rpow_mul,ofReal_square_rpow_half (30*ε) (by positivity),
    ENNReal.ofReal_mul (by norm_num : 0 ≤ (30:ℝ))] at hroot
  apply (ENNReal.div_le_iff (by norm_num : (30:ℝ≥0∞) ≠ 0) (by norm_num : (30:ℝ≥0∞) ≠ ⊤)).2
  simpa [β,mul_comm] using hroot

theorem entropy_tail_confidence_lower (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ B δ : ℝ}
    (hr : 0 < ρ) (hr' : ρ ≤ 1/4) (hb : 0 < B) (hd : 0 < δ) (hd' : δ ≤ 1/4) :
    (ENNReal.ofReal ((10:ℝ)⁻¹^17)*ThresholdHC.EntropyTail.selection μ ρ (B/Real.log (1/δ)))/30 ≤
      rareConfidenceRadius μ ρ B δ := by
  have hβ := div_pos hb (ThresholdHC.Confidence.confidence_log_pos hd hd')
  have h := (ThresholdHC.EntropyTailSharp.paper_comparison μ hr hr' hβ).1.trans
    (infinite_program_comparison μ ρ _ hr (by linarith) hβ).1
  exact (ENNReal.div_le_div_right h _).trans (stopping_confidence_lower μ hr (by linarith) hb hd hd')

end ThresholdHC.ConfidenceProgram
