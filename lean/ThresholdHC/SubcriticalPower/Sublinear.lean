import ThresholdHC.SubcriticalPower.Layers

noncomputable section
open MeasureTheory Set Real Filter
open scoped ENNReal
namespace ThresholdHC.SubcriticalPower
open ThresholdHC.Tier6 ThresholdHC.EntropyTailQuantile ThresholdHC.RareAboveTwo

private theorem margin_all (ν : Measure Gap) [IsProbabilityMeasure ν] {α a x : ℝ}
    (h : PowerMargin ν α a) (ha : 0 < a) (hα : 0 ≤ α) (hx : 0 < x) :
    ν.real {d : Gap | (d:ℝ) ≤ x} ≤ (x/a)^α := by
  by_cases hxa : x < a
  · exact h x hx hxa
  · exact measureReal_le_one.trans (Real.one_le_rpow ((one_le_div ha).mpr (le_of_not_gt hxa)) hα)

/-- The ordinary blind estimator already has the required unsaturated
rate in this regime. The factor is uniform over the entire CDF envelope. -/
theorem sublinear_modulus (ν : Measure Gap) [IsProbabilityMeasure ν] {α a h : ℝ}
    (hm : PowerMargin ν α a) (ha : 0 < a) (hα : 0 < α) (hu : α < 1) (hh : 0 < h) :
    modulus ν h ≤ (h/a)^α/(1-α) := by
  let F (x : ℝ) := ν.real {d : Gap | (d:ℝ) ≤ x}
  have hmono : Monotone F := fun _ _ hxy => measureReal_mono (fun _ hd => le_trans hd hxy)
  have hmeas : Measurable (fun t : ℝ => F (h/t)) := hmono.measurable.comp (measurable_const.div measurable_id)
  have hFi : IntervalIntegrable (fun t : ℝ => F (h/t)) volume 0 1 := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
    apply (integrableOn_const (C := (1:ℝ)) (hs := by rw [Real.volume_Ioc]; finiteness)).mono' hmeas.aestronglyMeasurable
    exact ae_of_all _ (fun t => by rw [Real.norm_eq_abs,abs_of_nonneg (measureReal_nonneg : 0 ≤ F (h/t))]; exact measureReal_le_one)
  have hneg : -1 < -α := by linarith
  have hgi : IntervalIntegrable (fun t : ℝ => (h/a)^α*t^(-α)) volume 0 1 :=
    (intervalIntegral.intervalIntegrable_rpow' hneg).const_mul _
  change tailModulus ν h ≤ _
  rw [tail_layers ν hh.le]
  calc _ ≤ ∫ t in (0:ℝ)..1, (h/a)^α*t^(-α) := by
             apply intervalIntegral.integral_mono_on_of_le_Ioo zero_le_one hFi hgi
             intro t ht
             have ht' := ht.1
             have hb := margin_all ν hm ha hα.le (div_pos hh ht')
             apply hb.trans_eq
             rw [show h/t/a = (h/a)/t by ring,Real.div_rpow (div_nonneg hh.le ha.le) ht'.le,Real.rpow_neg ht'.le]
             ring
       _ = _ := by
         rw [intervalIntegral.integral_const_mul,integral_rpow (Or.inl hneg),Real.one_rpow,Real.zero_rpow (by linarith : -α+1 ≠ 0)]
         ring

/-- On all gaps up to h the clipped loss is one. This gives the right
saturated lower bound for every positive exponent and the full first row. -/
theorem power_tail_floor (μ : Measure Gap) [IsProbabilityMeasure μ] {α a ρ h : ℝ}
    (hm : ExactPowerLaw μ α a) (hr : 0 < ρ) (hu : ρ ≤ 1) (hh : 0 < h) :
    min ρ ((h/a)^α) ≤ tailModulus (quantileTail μ ρ) h := by
  let _ := isFiniteMeasure_of_le μ (quantileTail_le μ hr hu)
  have hlo := mass_le_tail (quantileTail μ ρ) hh.le
  rw [quantile_cdf μ hr hu h,hm h hh,← min_assoc,min_eq_left hu] at hlo
  exact hlo

end ThresholdHC.SubcriticalPower
