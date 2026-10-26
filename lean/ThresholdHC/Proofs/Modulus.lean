import ThresholdHC.Statements

namespace ThresholdHC.Proofs
open ThresholdHC Real MeasureTheory

theorem scaling_up_pointwise : ThresholdHC.Targets.scaling_up_pointwise := by
  intro c h x hc hh hx
  by_cases hratio : h / x ≤ 1
  · rw [min_eq_right hratio]
    simpa [mul_div_assoc] using (min_le_right (1 : ℝ) (c * h / x))
  · rw [min_eq_left (le_of_not_ge hratio)]
    simpa using le_trans (min_le_left (1 : ℝ) (c * h / x)) hc

theorem scaling_down_pointwise : ThresholdHC.Targets.scaling_down_pointwise := by
  intro b h x hb hble hh hx
  apply le_min
  · calc
      b * min 1 (h / x) ≤ b * 1 := mul_le_mul_of_nonneg_left (min_le_left _ _) (le_of_lt hb)
      _ ≤ 1 := by simpa using hble
  · simpa [mul_div_assoc] using mul_le_mul_of_nonneg_left (min_le_right (1 : ℝ) (h / x)) (le_of_lt hb)

theorem modulus_scaling_up : ThresholdHC.Targets.modulus_scaling_up := by
  intro μ hμ hμ0 c h hc hh
  letI : IsProbabilityMeasure μ := hμ
  have hxpos : ∀ᵐ x ∂μ, 0 < x := by
    rw [ae_iff]
    simpa only [not_lt, Set.Iic] using hμ0
  have hint (a : ℝ) (ha : 0 < a) : Integrable (fun x : ℝ => min 1 (a/x)) μ := by
    apply (integrable_const (1 : ℝ)).mono'
    · exact (measurable_const.min (measurable_const.div measurable_id)).aestronglyMeasurable
    · filter_upwards [hxpos] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (by norm_num) (div_nonneg ha.le hx.le))]
      exact min_le_left _ _
  rw [← integral_const_mul]
  apply integral_mono_ae (hint (c*h) (mul_pos (by linarith) hh)) ((hint h hh).const_mul c)
  filter_upwards [hxpos] with x hx
  exact scaling_up_pointwise c h x hc hh hx

theorem power_modulus_critical : ThresholdHC.Targets.power_modulus_critical := by
  intro u hu hu1
  have hleft_eq : Set.EqOn (fun t : ℝ => min 1 (u/t)) (fun _ => (1 : ℝ)) (Set.uIoc 0 u) := by
    intro t ht
    rw [Set.uIoc_of_le hu.le] at ht
    exact min_eq_left ((one_le_div ht.1).2 ht.2)
  have hright_eq : Set.EqOn (fun t : ℝ => min 1 (u/t)) (fun t => u/t) (Set.uIoc u 1) := by
    intro t ht
    rw [Set.uIoc_of_le hu1.le] at ht
    exact min_eq_right ((div_le_one (lt_trans hu ht.1)).2 ht.1.le)
  have hintleft : IntervalIntegrable (fun t : ℝ => min 1 (u/t)) volume 0 u :=
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 u).congr hleft_eq.symm
  have hrightcont : ContinuousOn (fun t : ℝ => u/t) (Set.uIcc u 1) := by
    apply continuousOn_const.div continuousOn_id
    intro t ht
    rw [Set.uIcc_of_le hu1.le] at ht
    exact ne_of_gt (lt_of_lt_of_le hu ht.1)
  have hintright : IntervalIntegrable (fun t : ℝ => min 1 (u/t)) volume u 1 :=
    hrightcont.intervalIntegrable.congr hright_eq.symm
  have ileft : (∫ t in (0 : ℝ)..u, min 1 (u/t)) = u := by
    calc
      _ = ∫ _t in (0 : ℝ)..u, (1 : ℝ) := by
        apply intervalIntegral.integral_congr_ae
        exact Filter.Eventually.of_forall (fun t ht => hleft_eq ht)
      _ = u := by simp
  have iright : (∫ t in u..(1 : ℝ), min 1 (u/t)) = u * Real.log (1/u) := by
    calc
      _ = ∫ t in u..(1 : ℝ), u * t⁻¹ := by
        apply intervalIntegral.integral_congr_ae
        exact Filter.Eventually.of_forall (fun t ht => by simpa only [div_eq_mul_inv] using hright_eq ht)
      _ = u * (∫ t in u..(1 : ℝ), t⁻¹) := intervalIntegral.integral_const_mul u _
      _ = u * Real.log (1/u) := by rw [integral_inv_of_pos hu (by norm_num)]
  change (∫ t in (0 : ℝ)..1, min 1 (u/t)) = u * (1 - Real.log u)
  rw [← intervalIntegral.integral_add_adjacent_intervals hintleft hintright, ileft, iright]
  rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (ne_of_gt hu), Real.log_one]
  ring

theorem power_modulus : ThresholdHC.Targets.power_modulus := by
  intro α u hα hα1 hu hu1
  have hleft_eq : Set.EqOn (fun t : ℝ => min 1 (u/t) * (α * t^(α-1)))
      (fun t => α * t^(α-1)) (Set.uIoc 0 u) := by
    intro t ht
    rw [Set.uIoc_of_le hu.le] at ht
    dsimp only
    rw [min_eq_left ((one_le_div ht.1).2 ht.2), one_mul]
  have hright_eq : Set.EqOn (fun t : ℝ => min 1 (u/t) * (α * t^(α-1)))
      (fun t => u * α * t^(α-2)) (Set.uIoc u 1) := by
    intro t ht
    rw [Set.uIoc_of_le hu1.le] at ht
    have htpos := lt_trans hu ht.1
    dsimp only
    rw [min_eq_right ((div_le_one htpos).2 ht.1.le)]
    rw [show α-2 = (α-1)-1 by ring, Real.rpow_sub_one (ne_of_gt htpos) (α-1)]
    ring
  have hzero : (0 : ℝ) ∉ Set.uIcc u 1 := by
    rw [Set.uIcc_of_le hu1.le]
    intro ht
    linarith [ht.1]
  have hintleft : IntervalIntegrable (fun t : ℝ => min 1 (u/t) * (α*t^(α-1))) volume 0 u :=
    ((intervalIntegral.intervalIntegrable_rpow' (show -1 < α-1 by linarith)).const_mul α).congr hleft_eq.symm
  have hintright : IntervalIntegrable (fun t : ℝ => min 1 (u/t) * (α*t^(α-1))) volume u 1 :=
    ((intervalIntegral.intervalIntegrable_rpow (Or.inr hzero)).const_mul (u*α)).congr hright_eq.symm
  have ileft : (∫ t in (0 : ℝ)..u, min 1 (u/t) * (α*t^(α-1))) = u^α := by
    calc
      _ = ∫ t in (0 : ℝ)..u, α*t^(α-1) := by
        apply intervalIntegral.integral_congr_ae
        exact Filter.Eventually.of_forall (fun t ht => hleft_eq ht)
      _ = α * (∫ t in (0 : ℝ)..u, t^(α-1)) := intervalIntegral.integral_const_mul α _
      _ = u^α := by
        rw [integral_rpow (Or.inl (show -1 < α-1 by linarith))]
        simp only [sub_add_cancel, Real.zero_rpow (ne_of_gt hα), sub_zero]
        field_simp
  have iright : (∫ t in u..(1 : ℝ), min 1 (u/t) * (α*t^(α-1))) =
      u*α*((1-u^(α-1))/(α-1)) := by
    calc
      _ = ∫ t in u..(1 : ℝ), (u*α)*t^(α-2) := by
        apply intervalIntegral.integral_congr_ae
        exact Filter.Eventually.of_forall (fun t ht => hright_eq ht)
      _ = (u*α) * (∫ t in u..(1 : ℝ), t^(α-2)) := intervalIntegral.integral_const_mul (u*α) _
      _ = u*α*((1-u^(α-1))/(α-1)) := by
        rw [integral_rpow (Or.inr ⟨(by intro he; apply hα1; linarith), hzero⟩)]
        simp only [show α-2+1 = α-1 by ring, Real.one_rpow]
  change (∫ t in (0 : ℝ)..1, min 1 (u/t) * (α*t^(α-1))) = (α*u-u^α)/(α-1)
  rw [← intervalIntegral.integral_add_adjacent_intervals hintleft hintright, ileft, iright]
  rw [Real.rpow_sub_one (ne_of_gt hu) α]
  have hαm1 : α-1 ≠ 0 := sub_ne_zero.mpr hα1
  field_simp
  <;> ring

end ThresholdHC.Proofs
