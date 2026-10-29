import ThresholdHC.RareAboveTwo.PathInformation
import ThresholdHC.CriticalEntropy.FiniteGeometry

/-! Quadratic information contraction for two rare mixing weights. -/
noncomputable section
namespace ThresholdHC.RareAboveTwo
open ThresholdHC.Proofs ThresholdHC.Proofs.Transcript ThresholdHC.CriticalEntropy

def priorMix (u P Q : ℝ) : ℝ := (1-u)*P+u*Q

theorem priorMix_nonneg (u P Q : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1) (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    0 ≤ priorMix u P Q := add_nonneg (mul_nonneg (sub_nonneg.mpr hu1) hP) (mul_nonneg hu hQ)

theorem priorMix_sqrt_bound (u v P Q : ℝ) (hu : 0 < u) (huv : u ≤ v) (hv : v ≤ 1/2)
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    u*(Real.sqrt (priorMix u P Q)-Real.sqrt (priorMix v P Q))^2 ≤
      2*(v-u)^2*(Real.sqrt P-Real.sqrt Q)^2 := by
  have hu1 : u ≤ 1 := by linarith
  have hv0 : 0 ≤ v := by linarith
  have hv1 : v ≤ 1 := by linarith
  let x := priorMix u P Q
  let y := priorMix v P Q
  have hx : 0 ≤ x := priorMix_nonneg u P Q hu.le hu1 hP hQ
  have hy : 0 ≤ y := priorMix_nonneg v P Q hv0 hv1 hP hQ
  have hxs := Real.sq_sqrt hx
  have hys := Real.sq_sqrt hy
  have hPs := Real.sq_sqrt hP
  have hQs := Real.sq_sqrt hQ
  by_cases hzero : P+Q = 0
  · have hPz : P = 0 := by linarith
    have hQz : Q = 0 := by linarith
    simp [hPz,hQz,priorMix]
  have hsum : 0 < P+Q := lt_of_le_of_ne (add_nonneg hP hQ) (Ne.symm hzero)
  have hden : u*(P+Q) ≤ (Real.sqrt x+Real.sqrt y)^2 := by
    have hxu : u*(P+Q) ≤ x := by dsimp [x,priorMix]; nlinarith [mul_nonneg (by linarith : 0 ≤ 1-2*u) hP]
    nlinarith [Real.sqrt_nonneg x,Real.sqrt_nonneg y,mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]
  have hid : (Real.sqrt x-Real.sqrt y)^2*(Real.sqrt x+Real.sqrt y)^2 = (v-u)^2*(P-Q)^2 := by
    calc
      _ = ((Real.sqrt x)^2-(Real.sqrt y)^2)^2 := by ring
      _ = (x-y)^2 := by rw [hxs,hys]
      _ = _ := by dsimp [x,y,priorMix]; ring
  have hsign : (P-Q)^2 ≤ 2*(P+Q)*(Real.sqrt P-Real.sqrt Q)^2 := by
    have hid' : 2*(P+Q)*(Real.sqrt P-Real.sqrt Q)^2-(P-Q)^2 =
        (P+Q-2*Real.sqrt P*Real.sqrt Q)^2 := by
      have he (x y : ℝ) : 2*(x^2+y^2)*(x-y)^2-(x^2-y^2)^2 = (x^2+y^2-2*x*y)^2 := by ring
      simpa only [hPs,hQs] using he (Real.sqrt P) (Real.sqrt Q)
    nlinarith [sq_nonneg (P+Q-2*Real.sqrt P*Real.sqrt Q)]
  have h₁ := mul_le_mul_of_nonneg_left hden (sq_nonneg (Real.sqrt x-Real.sqrt y))
  rw [hid] at h₁
  have h₂ := mul_le_mul_of_nonneg_left hsign (sq_nonneg (v-u))
  apply (mul_le_mul_iff_right₀ hsum).mp
  change (P+Q)*(u*(Real.sqrt x-Real.sqrt y)^2) ≤ _
  nlinarith only [h₁,h₂]

theorem sqrt_square_le_kl (P Q : ℝ) (hP : 0 < P) (hQ : 0 < Q) :
    (Real.sqrt P-Real.sqrt Q)^2 ≤ klTerm P Q+Q-P := by
  have hp := Real.sqrt_pos.mpr hP
  have hq := Real.sqrt_pos.mpr hQ
  have hlog := Real.log_le_sub_one_of_pos (div_pos hq hp)
  have he : Real.log (Real.sqrt Q/Real.sqrt P) = -(Real.log (P/Q))/2 := by
    rw [Real.log_div hq.ne' hp.ne',Real.log_sqrt hQ.le,Real.log_sqrt hP.le,Real.log_div hP.ne' hQ.ne']
    ring
  rw [he] at hlog
  have h := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 2*P by positivity)
  have hdiv : 2*P*(Real.sqrt Q/Real.sqrt P-1) = 2*Real.sqrt P*Real.sqrt Q-2*P := by
    have hm : P*(Real.sqrt Q/Real.sqrt P) = Real.sqrt P*Real.sqrt Q := by
      rw [← mul_div_assoc,div_eq_iff hp.ne']
      calc
        _ = (Real.sqrt P)^2*Real.sqrt Q := by rw [Real.sq_sqrt hP.le]
        _ = _ := by ring
    calc
      _ = 2*(P*(Real.sqrt Q/Real.sqrt P))-2*P := by ring
      _ = _ := by rw [hm]; ring
  rw [hdiv] at h
  unfold klTerm
  nlinarith [Real.sq_sqrt hP.le,Real.sq_sqrt hQ.le]

end ThresholdHC.RareAboveTwo
