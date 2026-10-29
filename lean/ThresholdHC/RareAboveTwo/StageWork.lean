import ThresholdHC.RareAboveTwo.BandWork
import ThresholdHC.RareAboveTwo.PowerBounds

/-! A summable survival envelope. Constants depend on the moment exponent,
not on the gap, rarity, law, or terminal cap. -/
noncomputable section
open MeasureTheory Set
namespace ThresholdHC.RareAboveTwo
open ThresholdHC.Uniform713

def workKernel (p : ℝ) (k : ℕ) : ℝ := cap k*((k : ℝ)+1)^p/(cap k)^p

theorem workKernel_nonneg (p : ℝ) (k : ℕ) : 0 ≤ workKernel p k := by
  unfold workKernel
  positivity [cap_pos k]

theorem workKernel_summable (p : ℝ) (hp : 1 < p) : Summable (workKernel p) := by
  have hr : 0 < 2/(2 : ℝ)^p := by positivity
  have hr1 : 2/(2 : ℝ)^p < 1 := by
    apply (div_lt_one (by positivity)).2
    simpa using Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hp
  have he : workKernel p = fun k : ℕ => ((k : ℝ)+1)^p*(2/(2 : ℝ)^p)^k := by
    funext k
    unfold workKernel cap
    rw [div_pow,Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2) p k]
    ring
  rw [he]
  exact summable_real_power_geometric p _ (by linarith) hr.le hr1

def workCoefficient (p : ℝ) : ℝ := ((2 : ℝ)^p+(2*p)^p)*(∑' k, workKernel p k)

theorem workCoefficient_pos (p : ℝ) (hp : 1 < p) : 0 < workCoefficient p := by
  unfold workCoefficient
  apply mul_pos (by positivity)
  have h := (workKernel_summable p hp).le_tsum 0 (fun k _ => workKernel_nonneg p k)
  have hzero : workKernel p 0 = 1 := by simp [workKernel,cap]
  rw [hzero] at h
  linarith

theorem scaled_inverse_bound (e : ℕ) (a d p : ℝ) (ha : 0 < a) (hd : 0 < d)
    (hp : 0 ≤ p) (hscale : 1 ≤ cap e*a^2) :
    (1/(cap e*d^2))^p ≤ (a/d)^(2*p) := by
  have he : 1/(cap e*d^2) = (1/cap e)/d^2 := by ring
  have hb : 1/(cap e*d^2) ≤ (a/d)^2 := by
    rw [he,div_pow]
    exact div_le_div_of_nonneg_right ((div_le_iff₀ (cap_pos e)).2 (by simpa [mul_comm] using hscale)) (sq_nonneg d)
  have h := Real.rpow_le_rpow (by positivity [cap_pos e] : 0 ≤ 1/(cap e*d^2)) hb hp
  convert h using 1
  exact Real.rpow_natCast_mul (div_pos ha hd).le 2 p

theorem scaled_work_kernel (e k : ℕ) (a d p : ℝ) (ha : 0 < a) (hd : 0 < d)
    (hp : 0 ≤ p) (hscale : 1 ≤ cap e*a^2) :
    cap (e+k)*((k : ℝ)+1)^p/(cap (e+k)*d^2)^p ≤
      cap e*(a/d)^(2*p)*workKernel p k := by
  have hcap : cap (e+k) = cap e*cap k := by simp [cap,pow_add]
  have he : cap (e+k)*((k : ℝ)+1)^p/(cap (e+k)*d^2)^p =
      cap e*workKernel p k*(1/(cap e*d^2))^p := by
    rw [hcap,show cap e*cap k*d^2 = (cap e*d^2)*cap k by ring,
      Real.mul_rpow (by positivity [cap_pos e]) (cap_pos k).le,
      Real.div_rpow (by norm_num : (0 : ℝ) ≤ 1) (by positivity [cap_pos e]),Real.one_rpow]
    unfold workKernel
    ring
  rw [he]
  have h := mul_le_mul_of_nonneg_left (scaled_inverse_bound e a d p ha hd hp hscale)
    (mul_nonneg (cap_pos e).le (workKernel_nonneg p k))
  nlinarith only [h]

theorem threshold_power_envelope (p F A : ℝ) (hp : 0 < p) (hF : 1 ≤ F)
    (hA : 0 ≤ A) (k : ℕ) (hAF : A ≤ F*((k : ℝ)+1)) :
    (2*A)^p+(2*p)^p ≤ ((2 : ℝ)^p+(2*p)^p)*F^p*((k : ℝ)+1)^p := by
  have hk : 1 ≤ (k : ℝ)+1 := by have := Nat.cast_nonneg (α := ℝ) k; linarith
  have hF0 : 0 < F := by linarith
  have hFk : 1 ≤ F*((k : ℝ)+1) := one_le_mul_of_one_le_of_one_le hF hk
  have hpow : 1 ≤ (F*((k : ℝ)+1))^p := by
    simpa using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hFk hp.le
  have hpA := Real.rpow_le_rpow (by positivity : 0 ≤ 2*A)
    (mul_le_mul_of_nonneg_left hAF (by norm_num : (0 : ℝ) ≤ 2)) hp.le
  have hpp := mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg (by positivity : 0 ≤ 2*p) p)
  have he : (2*(F*((k : ℝ)+1)))^p = (2 : ℝ)^p*F^p*((k : ℝ)+1)^p := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity),
      Real.mul_rpow hF0.le (by positivity)]
    ring
  rw [he] at hpA
  rw [Real.mul_rpow hF0.le (by positivity)] at hpp
  nlinarith only [hpA,hpp]

theorem band_work_power_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (m : ℕ → Ω → ℝ)
    (hm : ∀ k, Measurable (m k)) (e L : ℕ) (A₀ A₁ A : ℕ → ℝ)
    (a d p F : ℝ) (ha : 0 < a) (hd : 0 < d) (hp : 1 < p) (hF : 1 ≤ F)
    (hscale : 1 ≤ cap e*a^2) (hA : ∀ k, 0 ≤ A k)
    (hAF : ∀ k, A k ≤ F*((k : ℝ)+1))
    (hs : ∀ k, μ.real {ω | k < bandStop e A₀ A₁ (fun j => m j ω) L} ≤
      (if cap (e+k)*d^2 ≤ 2*A k then 1 else 0)+Real.exp (-(d^2/2*cap (e+k)))) :
    (∫ ω, cap (e+bandStop e A₀ A₁ (fun j => m j ω) L) ∂μ) ≤
      cap e*(1+workCoefficient p*F^p*(a/d)^(2*p)) := by
  have hp0 : 0 < p := by linarith
  have hk (k : ℕ) : cap (e+k)*μ.real {ω | k < bandStop e A₀ A₁ (fun j => m j ω) L} ≤
      cap e*((2 : ℝ)^p+(2*p)^p)*F^p*(a/d)^(2*p)*workKernel p k := by
    have hsur := survival_power_bound (cap (e+k)*d^2) (A k) p
      (by positivity [cap_pos (e+k)]) (hA k) hp0
    have htime : d^2/2*cap (e+k) = (cap (e+k)*d^2)/2 := by ring
    have hsk := hs k
    rw [htime] at hsk
    have h₁ := hsk.trans hsur
    have h₂ := div_le_div_of_nonneg_right (threshold_power_envelope p F (A k) hp0 hF (hA k) k (hAF k))
      (Real.rpow_nonneg (by positivity [cap_pos (e+k)] : 0 ≤ cap (e+k)*d^2) p)
    have h₃ := mul_le_mul_of_nonneg_left (h₁.trans h₂) (cap_pos (e+k)).le
    have h₄ := mul_le_mul_of_nonneg_left (scaled_work_kernel e k a d p ha hd hp0.le hscale)
      (show 0 ≤ ((2 : ℝ)^p+(2*p)^p)*F^p by positivity)
    calc
      _ ≤ cap (e+k)*(((2 : ℝ)^p+(2*p)^p)*F^p*((k : ℝ)+1)^p/(cap (e+k)*d^2)^p) := h₃
      _ = ((2 : ℝ)^p+(2*p)^p)*F^p*(cap (e+k)*((k : ℝ)+1)^p/(cap (e+k)*d^2)^p) := by ring
      _ ≤ ((2 : ℝ)^p+(2*p)^p)*F^p*(cap e*(a/d)^(2*p)*workKernel p k) := h₄
      _ = _ := by ring
  rw [band_work_survival_identity e A₀ A₁ hm L]
  have hsum := Finset.sum_le_sum (s := Finset.range L) (fun k _ => hk k)
  have hsummable := (workKernel_summable p hp).mul_left
    (cap e*((2 : ℝ)^p+(2*p)^p)*F^p*(a/d)^(2*p))
  have hfull := hsummable.sum_le_tsum (Finset.range L) (fun k _ => by positivity [cap_pos e, workKernel_nonneg p k])
  rw [tsum_mul_left] at hfull
  unfold workCoefficient
  nlinarith only [hsum,hfull]

end ThresholdHC.RareAboveTwo
