import ThresholdHC.CriticalUpper.GapIntegration

/-! Exact integration of the capped reciprocal work envelope. -/

noncomputable section
namespace ThresholdHC.CriticalUpper
open MeasureTheory Set ThresholdHC.CriticalEntropy ThresholdHC.Uniform713
open scoped ENNReal

/-- The reciprocal work envelope is bounded even at arbitrarily small gaps. -/
theorem cappedReciprocal_integrableOn (N K a b : ℝ) (hN : 0 ≤ N) (hK : 0 ≤ K)
    (ha : 0 ≤ a) : IntegrableOn (fun u : ℝ => min N (K/u)) (Ioc a b) := by
  apply (integrable_const N).mono' (by fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  have hu0 : 0 < u := lt_of_le_of_lt ha hu.1
  rw [Real.norm_of_nonneg (le_min hN (div_nonneg hK hu0.le))]
  exact min_le_left _ _

theorem cappedReciprocal_integral_small (N K x : ℝ) (hN : 0 < N) (hK : 0 < K)
    (hx : 0 ≤ x) (hsmall : N*x ≤ K) :
    (∫ u in Ioc (0 : ℝ) x, min N (K/u)) = N*x := by
  have he : (fun u : ℝ => min N (K/u)) =ᵐ[volume.restrict (Ioc 0 x)] fun _ => N := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    apply min_eq_left
    apply (le_div_iff₀ hu.1).mpr
    exact (mul_le_mul_of_nonneg_left hu.2 hN.le).trans hsmall
  rw [integral_congr_ae he,integral_const]
  simp only [MeasureTheory.Measure.real,Measure.restrict_apply_univ,Real.volume_Ioc,
    sub_zero,ENNReal.toReal_ofReal hx,smul_eq_mul]
  ring

theorem cappedReciprocal_integral_large (N K x : ℝ) (hN : 0 < N) (hK : 0 < K)
    (hlarge : K/N ≤ x) :
    (∫ u in Ioc (0 : ℝ) x, min N (K/u)) = K*(1+Real.log (N*x/K)) := by
  have hr : 0 < K/N := div_pos hK hN
  have hx : 0 < x := hr.trans_le hlarge
  have h0r : IntervalIntegrable (fun u : ℝ => min N (K/u)) volume 0 (K/N) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hr.le).mpr
      (cappedReciprocal_integrableOn N K 0 (K/N) hN.le hK.le le_rfl)
  have hrx : IntervalIntegrable (fun u : ℝ => min N (K/u)) volume (K/N) x :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hlarge).mpr
      (cappedReciprocal_integrableOn N K (K/N) x hN.le hK.le hr.le)
  have hi : (∫ u in (K/N)..x, min N (K/u)) = K*Real.log (x/(K/N)) := by
    rw [intervalIntegral.integral_of_le hlarge]
    have he : (fun u : ℝ => min N (K/u)) =ᵐ[volume.restrict (Ioc (K/N) x)]
        fun u => K*u⁻¹ := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      have hu0 : 0 < u := hr.trans hu.1
      rw [min_eq_right,div_eq_mul_inv]
      apply (div_le_iff₀ hu0).mpr
      exact (div_le_iff₀ hN).mp hu.1.le |>.trans_eq (mul_comm u N)
    rw [integral_congr_ae he,← intervalIntegral.integral_of_le hlarge,
      intervalIntegral.integral_const_mul,integral_inv_of_pos hr hx]
  rw [← intervalIntegral.integral_of_le hx.le,
    ← intervalIntegral.integral_add_adjacent_intervals h0r hrx,
    intervalIntegral.integral_of_le hr.le,
    cappedReciprocal_integral_small N K (K/N) hN hK hr.le (le_of_eq (by field_simp)),hi]
  have he : x/(K/N) = N*x/K := by field_simp
  rw [he]
  field_simp

/-- A logarithmic work bound, uniform through the saturation regime. -/
theorem cappedReciprocal_integral_le (N K x : ℝ) (hN : 0 < N) (hK : 0 < K)
    (hx : 0 ≤ x) :
    (∫ u in Ioc (0 : ℝ) x, min N (K/u)) ≤ K*(1+max 0 (Real.log (N*x/K))) := by
  by_cases hsmall : N*x ≤ K
  · rw [cappedReciprocal_integral_small N K x hN hK hx hsmall]
    have hmax : 0 ≤ max 0 (Real.log (N*x/K)) := le_max_left _ _
    nlinarith
  · have hlarge : K/N ≤ x := by apply (div_le_iff₀ hN).mpr; nlinarith
    rw [cappedReciprocal_integral_large N K x hN hK hlarge]
    apply mul_le_mul_of_nonneg_left _ hK.le
    linarith [le_max_right (0 : ℝ) (Real.log (N*x/K))]

end ThresholdHC.CriticalUpper
