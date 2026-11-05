import ThresholdHC.ShiftedPower.Certificate
import ThresholdHC.ShiftedPower.BaseLevel
import ThresholdHC.ShiftedPower.TailRates

noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace ThresholdHC.ShiftedPower
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.EntropyTailUpper

def linearConstant : ℝ := 1+20*sqrt (workConstant 1)

theorem linearConstant_ge_one : 1 ≤ linearConstant :=
  le_add_of_nonneg_right (mul_nonneg (by norm_num) (sqrt_nonneg _))

theorem linearRate_of_lt {ρ x : ℝ} (hx : 0 < x) (h : x < ρ) :
    linearRate ρ x = x*(1+Real.log (ρ/x)) := by
  have ht : 1 ≤ ρ/x := (one_le_div hx).mpr h.le
  unfold linearRate
  rw [max_eq_right (Real.log_nonneg ht)]
  apply min_eq_right
  have hh := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos (hx.trans h) hx)) hx.le
  have he : x*(ρ/x)=ρ := mul_div_cancel₀ _ hx.ne'
  nlinarith only [hh,he]

theorem linearRate_of_ge {ρ x : ℝ} (hr : 0 < ρ) (h : ρ ≤ x) : linearRate ρ x = ρ := by
  have hx := hr.trans_le h
  unfold linearRate
  rw [max_eq_left (Real.log_nonpos (div_nonneg hr.le hx.le) ((div_le_one hx).mpr h)),add_zero,mul_one,min_eq_left h]

/-- The number of levels grows at most logarithmically with rho/x.
This is the sole source of the logarithmic factor at exponent one. -/
theorem linear_levels {a ρ x : ℝ} (ha : 0 < a) (_hr : 0 < ρ) (hx : 0 < x) (hxr : x < ρ)
    (k : ℕ) (hk : massBound 1 a k ≤ 2*ρ) :
    ∃ J : ℕ, errorBound 1 a (k+J) ≤ x ∧ (J:ℝ)+1 ≤ 5*(1+Real.log (ρ/x)) := by
  let s := sqrt (2:ℝ)
  have hs : 1 < s := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hs0 : 0 < s := by linarith
  have hs2 : s^2=2 := Real.sq_sqrt (by norm_num)
  have hsupper : s ≤ 3/2 := by nlinarith only [hs2,hs0]
  have hlogs : 1/4 ≤ Real.log s := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    have he : Real.log s = Real.log 2/2 := by dsimp [s]; rw [Real.log_sqrt (by norm_num)]
    norm_num at h
    linarith
  obtain ⟨j,hj,hj'⟩ := exists_nat_pow_near (x := ρ/x) (y := s) ((one_le_div hx).mpr hxr.le) hs
  refine ⟨j+4,?_,?_⟩
  · have hmass := mass_add (α := 1) ha k (j+4)
    have hdec : decay 1 = s⁻¹ := Real.rpow_one _
    have hpow : s^(j+4) = 4*s^j := by rw [pow_add,show s^4=(s^2)^2 by ring,hs2]; ring
    have hp : 0 < s^j := pow_pos hs0 _
    have hhi : ρ < x*s^j*s := by
      have h := (div_lt_iff₀ hx).mp hj'
      rw [pow_succ] at h
      nlinarith only [h]
    change massBound 1 a (k+(j+4))/(1-1/4) ≤ _
    rw [hmass,hdec,inv_pow,hpow]
    apply (div_le_iff₀ (by norm_num : (0:ℝ)<1-1/4)).mpr
    apply (mul_le_mul_iff_right₀ (show 0 < 4*s^j by positivity)).mp
    field_simp
    nlinarith only [hk,hhi,mul_le_mul_of_nonneg_left hsupper (mul_nonneg hx.le hp.le)]
  · have hlog := Real.log_le_log (pow_pos hs0 j) hj
    rw [Real.log_pow] at hlog
    have hj0 : (0:ℝ) ≤ j := Nat.cast_nonneg _
    have hl := Real.log_nonneg ((one_le_div hx).mpr hxr.le)
    push_cast
    nlinarith only [hlog,mul_le_mul_of_nonneg_left hlogs hj0,hl]

theorem linear_rms_family {a ρ B : ℝ} (ha : 0 < a) (ha' : a ≤ 1) (hr : 0 < ρ) (hr' : ρ ≤ 1) (hB : 0 < B) :
    ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R),
    ∀ (ν : Measure Gap) [IsProbabilityMeasure ν], PowerMargin ν 1 a →
      RareBudget ν A ρ B ∧ rareRisk ν A ρ ≤ ENNReal.ofReal (linearConstant*linearRate ρ ((sqrt B)⁻¹/a)) := by
  let x := (sqrt B)⁻¹/a
  have hx : 0 < x := div_pos (inv_pos.mpr (sqrt_pos.mpr hB)) ha
  by_cases hs : ρ ≤ x
  · refine ⟨_,inferInstance,idleEstimator ρ,?_⟩
    intro ν _ _
    refine ⟨fun q _ => (idle_work ν q ρ).le.trans bot_le,?_⟩
    rw [linearRate_of_ge hr hs]
    exact (idle_risk ν ρ).trans (ENNReal.ofReal_le_ofReal
      ((by linarith : ρ/2 ≤ ρ).trans (le_mul_of_one_le_left hr.le linearConstant_ge_one)))
  · have hxr := lt_of_not_ge hs
    obtain ⟨k,hkl,hku⟩ := base_level (α := 1) (by norm_num) (by norm_num) ha ha' hr hr'
    obtain ⟨J,hJ,hcount⟩ := linear_levels ha hr hx hxr k hku
    refine ⟨_,inferInstance,shiftedEstimator 1 a B k J,?_⟩
    intro ν _ hm
    have hbound (q : SignLaw) (hq : RarePrior ν ρ q) :=
      shifted_bounds ν q (by norm_num) (by norm_num) ha hB hm hq k J (by linarith)
    refine ⟨fun q hq => (hbound q hq).1,?_⟩
    apply iSup_le; intro q; apply iSup_le; intro hq
    apply (hbound q hq).2.trans
    apply ENNReal.ofReal_le_ofReal
    rw [linear_certificate ha,linearRate_of_lt hx hxr]
    have hlog := Real.log_nonneg ((one_le_div hx).mpr hxr.le)
    have h := mul_le_mul_of_nonneg_left hcount (show 0 ≤ 4*sqrt (workConstant 1)/a/sqrt B by positivity)
    change _ ≤ linearConstant*(x*(1+Real.log (ρ/x)))
    have he : (4*sqrt (workConstant 1)/a/sqrt B) = 4*sqrt (workConstant 1)*x := by dsimp [x]; ring
    rw [he] at h
    have he' : (4*sqrt (workConstant 1)/a*(J+1))/sqrt B = (4*sqrt (workConstant 1)*x)*(J+1) := by dsimp [x]; ring
    rw [he']
    unfold linearConstant
    nlinarith only [hJ,h,mul_nonneg hx.le hlog]

end ThresholdHC.ShiftedPower
