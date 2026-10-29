import ThresholdHC.RareAboveTwo.Parameters

/-! A terminal cap whose integrated majority error is uniform over all
power-margin laws with exponent at least two. -/
noncomputable section
open MeasureTheory Set
namespace ThresholdHC.RareAboveTwo
open ThresholdHC.Tier6 ThresholdHC.Uniform713 ThresholdHC.CriticalUpper

theorem margin_gaussian_bound (μ : Measure Gap) [IsProbabilityMeasure μ]
    (a N t : ℝ) (ha : 0 < a) (hN : 0 ≤ N) (ht : 1 < t)
    (hNt : t^2 ≤ N*a^2) (hm : PowerMargin μ 2 a) :
    (∫ d : Gap, Real.exp (-2*N*(d : ℝ)^2) ∂μ) ≤ 2/t := by
  have ht0 : 0 < t := by linarith
  have hsq : 1 < Real.sqrt t := by simpa using Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) ht
  let x := a/Real.sqrt t
  have hx : 0 < x := div_pos ha (by positivity)
  have hxa : x < a := div_lt_self ha hsq
  have hxid : x^2*t = a^2 := by
    dsimp [x]
    rw [div_pow,Real.sq_sqrt ht0.le]
    field_simp
  have hcdf : μ.real {d : Gap | (d : ℝ) ≤ x} ≤ 1/t := by
    apply (hm x hx hxa).trans_eq
    rw [Real.rpow_two]
    have h : (x/a)^2*t = 1 := by
      rw [div_pow]
      field_simp
      nlinarith [hxid]
    exact (eq_div_iff ht0.ne').2 h
  let E : Set Gap := {d | (d : ℝ) ≤ x}
  have hE : MeasurableSet E := measurableSet_le measurable_subtype_coe measurable_const
  have hf : Integrable (fun d : Gap => Real.exp (-2*N*(d : ℝ)^2)) μ := by
    apply Integrable.of_bound (show Measurable (fun d : Gap => Real.exp (-2*N*(d : ℝ)^2)) by fun_prop).aestronglyMeasurable 1
    exact ae_of_all _ (fun d => by
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      apply Real.exp_le_one_iff.2
      nlinarith [sq_nonneg (d : ℝ)])
  have hi : Integrable (E.indicator (fun _ => (1 : ℝ))) μ := (integrable_const _).indicator hE
  have hp (d : Gap) : Real.exp (-2*N*(d : ℝ)^2) ≤ E.indicator (fun _ => (1 : ℝ)) d+1/t := by
    by_cases hd : d ∈ E
    · rw [indicator_of_mem hd]
      have hb : Real.exp (-2*N*(d : ℝ)^2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg (d : ℝ)])
      have : 0 < 1/t := by positivity
      linarith
    · rw [indicator_of_notMem hd,zero_add]
      have hxd : x < (d : ℝ) := lt_of_not_ge hd
      have hsq' : x^2 ≤ (d : ℝ)^2 := by nlinarith [d.property.1]
      have hxdt := mul_le_mul_of_nonneg_right hsq' ht0.le
      rw [hxid] at hxdt
      have hscaled := mul_le_mul_of_nonneg_left hxdt hN
      have htd : t ≤ N*(d : ℝ)^2 := by nlinarith
      calc
        _ ≤ Real.exp (-Real.log t) := Real.exp_le_exp.mpr (by linarith [Real.log_le_sub_one_of_pos ht0])
        _ = 1/t := by rw [Real.exp_neg,Real.exp_log ht0]; simp [one_div]
  calc
    _ ≤ ∫ d : Gap, E.indicator (fun _ => (1 : ℝ)) d+1/t ∂μ := integral_mono hf (hi.add (integrable_const _)) hp
    _ = μ.real E+1/t := by rw [integral_add hi (integrable_const _),integral_indicator_const _ hE]; simp
    _ ≤ 1/t+1/t := add_le_add hcdf le_rfl
    _ = 2/t := by ring

theorem terminal_gaussian_error (μ : Measure Gap) [IsProbabilityMeasure μ]
    (α a ρ : ℝ) (hα : 2 < α) (ha : 0 < a) (ha' : a ≤ 1/2)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hm : PowerMargin μ α a) (j : ℕ) :
    (∫ d : Gap, Real.exp (-2*cap (initialLevel a+terminalLevel ρ j)*(d : ℝ)^2) ∂μ) ≤
      ρ*screenAccuracy j := by
  let t := cap (screenLevel ρ j)
  have ht : 1 < t := by
    change 1 < (2 : ℝ)^(screenLevel ρ j)
    apply one_lt_pow₀ (by norm_num)
    unfold screenLevel
    omega
  have hcap : cap (initialLevel a+terminalLevel ρ j) = cap (initialLevel a)*t^2 := by
    simp only [terminalLevel,t,cap,pow_add]
    rw [show 2*screenLevel ρ j = screenLevel ρ j*2 by omega,pow_mul]
  have hNt : t^2 ≤ cap (initialLevel a+terminalLevel ρ j)*a^2 := by
    rw [hcap]
    have h := mul_le_mul_of_nonneg_right (initialLevel_bounds a ha ha').1 (sq_nonneg t)
    nlinarith only [h]
  have hb := margin_gaussian_bound μ a (cap (initialLevel a+terminalLevel ρ j)) t ha
    (cap_pos _).le ht hNt (margin_quadratic μ α a hα.le ha hm)
  have hg := screenLevel_gaussian ρ hρ hρ1 j
  have hle : 2/t ≤ 8/t := div_le_div_of_nonneg_right (by norm_num) (by linarith)
  exact hb.trans (hle.trans (by dsimp [t]; linarith [mul_pos hρ (screenAccuracy_pos j)]))

end ThresholdHC.RareAboveTwo
