import ThresholdHC.PowerWindow.CoreCost
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

noncomputable section
open MeasureTheory Set
namespace ThresholdHC.PowerWindow

/-- Integration by parts for the logarithmic first moments of a truncated
power density. Keeping the shift free covers both orientations of the core. -/
theorem rpow_log_balance {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) (r c : ℝ) :
    r * (∫ u in ρ..1, u ^ (r - 1) * (Real.log u - c)) +
      (∫ u in ρ..1, u ^ (r - 1)) = -c - ρ ^ r * (Real.log ρ - c) := by
  have hpos (u : ℝ) (hu : u ∈ uIcc ρ 1) : 0 < u := by
    rw [uIcc_of_le hρ1.le] at hu
    exact hρ.trans_le hu.1
  have hpow : ContinuousOn (fun u : ℝ => u ^ (r - 1)) (uIcc ρ 1) :=
    continuousOn_id.rpow_const (fun u hu => Or.inl (hpos u hu).ne')
  have hlog : ContinuousOn (fun u : ℝ => Real.log u - c) (uIcc ρ 1) :=
    (continuousOn_id.log (fun u hu => (hpos u hu).ne')).sub continuousOn_const
  have hderiv (u : ℝ) (hu : u ∈ uIcc ρ 1) :
      HasDerivAt (fun u : ℝ => u ^ r * (Real.log u - c))
        (r * (u ^ (r - 1) * (Real.log u - c)) + u ^ (r - 1)) u := by
    have hu0 := hpos u hu
    have hp : u ^ r * u⁻¹ = u ^ (r - 1) := by
      rw [Real.rpow_sub hu0, Real.rpow_one, div_eq_mul_inv]
    convert ((hasDerivAt_id u).rpow_const (p := r) (Or.inl hu0.ne')).mul
      ((Real.hasDerivAt_log hu0.ne').sub_const c) using 1 <;>
      first | rfl | (simp only [id_eq, one_mul, hp]; ring)
  have ip : IntervalIntegrable (fun u : ℝ => u ^ (r - 1) * (Real.log u - c)) volume ρ 1 :=
    (hpow.mul hlog).intervalIntegrable
  have ipr : IntervalIntegrable (fun u : ℝ => r * (u ^ (r - 1) * (Real.log u - c))) volume ρ 1 :=
    ip.const_mul r
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (ipr.add hpow.intervalIntegrable)
  rw [intervalIntegral.integral_add ipr hpow.intervalIntegrable,
    intervalIntegral.integral_const_mul] at hi
  simpa only [Real.one_rpow, Real.log_one, zero_sub, one_mul] using hi

theorem upper_log_moment_bound {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) (r : ℝ) :
    r * (∫ u in ρ..1, u ^ (r - 1) * (-Real.log u)) ≤
      ∫ u in ρ..1, u ^ (r - 1) := by
  have hb := rpow_log_balance hρ hρ1 r 0
  have hlog : ρ ^ r * Real.log ρ ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg hρ.le _) (Real.log_nonpos hρ.le hρ1.le)
  have he : (∫ u in ρ..1, u ^ (r - 1) * (-Real.log u)) =
      -(∫ u in ρ..1, u ^ (r - 1) * (Real.log u - 0)) := by
    rw [← intervalIntegral.integral_neg]
    congr 1
    ext u
    ring
  rw [he]
  simp only [sub_zero]
  simp only [sub_zero, neg_zero, zero_sub] at hb
  linarith

theorem lower_log_moment_bound {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) (r : ℝ) :
    (-r) * (∫ u in ρ..1, u ^ (r - 1) * (Real.log u - Real.log ρ)) ≤
      ∫ u in ρ..1, u ^ (r - 1) := by
  have hb := rpow_log_balance hρ hρ1 r (Real.log ρ)
  simp only [sub_self, mul_zero, sub_zero] at hb
  linarith [Real.log_nonpos hρ.le hρ1.le]

end ThresholdHC.PowerWindow
