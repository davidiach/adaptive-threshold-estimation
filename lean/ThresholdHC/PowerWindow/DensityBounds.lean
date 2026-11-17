import ThresholdHC.PowerWindow.LogMoments

noncomputable section
open MeasureTheory Set
namespace ThresholdHC.PowerWindow

theorem power_density_balance {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) (r : ℝ) :
    r * (∫ u in ρ..1, u ^ (r - 1)) = 1 - ρ ^ r := by
  by_cases hr : r = 0
  · simp [hr]
  · rw [integral_rpow (Or.inr ⟨by intro he; apply hr; linarith,
      notMem_uIcc_of_lt hρ (by norm_num)⟩)]
    simp only [sub_add_cancel, Real.one_rpow]
    field_simp

/-- A truncated power density has peak-to-average ratio at most the sum of
the reciprocal logarithmic window length and the absolute exponent. -/
theorem power_density_peak {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) (r : ℝ) :
    max 1 (ρ ^ r) ≤ ((-Real.log ρ)⁻¹ + |r|) *
      (∫ u in ρ..1, u ^ (r - 1)) := by
  let L := -Real.log ρ
  let J := ∫ u in ρ..1, u ^ (r - 1)
  have hL : 0 < L := neg_pos.2 (Real.log_neg hρ hρ1)
  have hb : r * J = 1 - ρ ^ r := power_density_balance hρ hρ1 r
  have hp : 0 < ρ ^ r := Real.rpow_pos_of_pos hρ r
  have he : ρ ^ r = Real.exp (-r * L) := by
    rw [Real.rpow_def_of_pos hρ]
    congr 1
    dsimp [L]
    ring
  change max 1 (ρ ^ r) ≤ (L⁻¹ + |r|) * J
  rcases lt_trichotomy r 0 with hr | hr | hr
  · have hpl : 1 ≤ ρ ^ r := by
      rw [he]
      exact Real.one_le_exp (mul_nonneg (neg_nonneg.2 hr.le) hL.le)
    rw [max_eq_right hpl, abs_of_neg hr]
    have hx : 1 - r * L ≤ ρ ^ r := by
      rw [he]
      linarith [Real.add_one_le_exp (-r * L)]
    have hJL : L ≤ J := by nlinarith
    have hmul : ρ ^ r * L ≤ (L⁻¹ + -r) * J * L := by
      have hi : L⁻¹ * L = 1 := inv_mul_cancel₀ hL.ne'
      nlinarith [congrArg (fun x : ℝ => x * L) hb,
        congrArg (fun x : ℝ => x * J) hi]
    exact (mul_le_mul_iff_left₀ hL).mp (by nlinarith [hmul])
  · subst r
    have hJ : J = L := by
      dsimp [J, L]
      norm_num only [zero_sub, Real.rpow_neg_one]
      rw [integral_inv_of_pos hρ (by norm_num), one_div, Real.log_inv]
    simp only [Real.rpow_zero, max_self, abs_zero, add_zero, hJ]
    rw [inv_mul_cancel₀ hL.ne']
  · have hpl : ρ ^ r ≤ 1 := by rw [he]; exact Real.exp_le_one_iff.2 (by nlinarith)
    rw [max_eq_left hpl, abs_of_pos hr]
    have hx : ρ ^ r * (1 + r * L) ≤ 1 := by
      have hh := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (r * L)) hp.le
      have hc : ρ ^ r * Real.exp (r * L) = 1 := by
        rw [he, ← Real.exp_add]
        convert Real.exp_zero using 2 <;> ring
      rw [hc] at hh
      nlinarith
    have hJL : L ≤ (1 + r * L) * J := by
      have hh : r * L ≤ r * ((1 + r * L) * J) := by
        nlinarith [congrArg (fun x : ℝ => x * (1 + r * L)) hb]
      exact (mul_le_mul_iff_right₀ hr).mp hh
    apply (mul_le_mul_iff_left₀ hL).mp
    have hi : L⁻¹ * L = 1 := inv_mul_cancel₀ hL.ne'
    nlinarith [congrArg (fun x : ℝ => x * J) hi]

/-- The mass of a logarithmic subwindow is bounded by its width times the
peak of the power density in logarithmic coordinates. -/
theorem power_density_band_bound {ρ l u : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hl : 0 < l) (hlu : l ≤ u) (r : ℝ) :
    (∫ v in Ioc ρ 1 ∩ Ioc l u, v ^ (r - 1)) ≤
      max 1 (ρ ^ r) * Real.log (u / l) := by
  have hp : 0 ≤ max 1 (ρ ^ r) := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)
  have hi : IntegrableOn (fun v : ℝ => v ^ (r - 1)) (Ioc ρ 1) := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hρ1.le).1
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_id.rpow_const
    intro v hv
    rw [uIcc_of_le hρ1.le] at hv
    exact Or.inl (hρ.trans_le hv.1).ne'
  have hv : IntegrableOn (fun v : ℝ => v⁻¹) (Ioc l u) := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hlu).1
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_id.inv₀
    intro v hv
    rw [uIcc_of_le hlu] at hv
    exact (hl.trans_le hv.1).ne'
  have hvc : IntegrableOn (fun v : ℝ => max 1 (ρ ^ r) * v⁻¹) (Ioc l u) :=
    hv.const_mul _
  have hm := setIntegral_mono_on (hi.mono_set inter_subset_left)
    (hvc.mono_set inter_subset_right)
    (measurableSet_Ioc.inter measurableSet_Ioc) (fun v hv' => show
      v ^ (r - 1) ≤ max 1 (ρ ^ r) * v⁻¹ from by
        have hv0 := hρ.trans hv'.1.1
        rw [Real.rpow_sub hv0, Real.rpow_one, div_eq_mul_inv]
        apply mul_le_mul_of_nonneg_right _ (inv_nonneg.2 hv0.le)
        rcases le_total 0 r with hr | hr
        · have hvr : v ^ r ≤ 1 := by
            simpa only [Real.one_rpow] using Real.rpow_le_rpow hv0.le hv'.1.2 hr
          exact hvr.trans (le_max_left _ _)
        · exact (Real.rpow_le_rpow_of_nonpos hρ hv'.1.1.le hr).trans (le_max_right _ _))
  have hs := setIntegral_mono_set (hv.const_mul (max 1 (ρ ^ r)))
    ((ae_restrict_mem measurableSet_Ioc).mono fun v hv' =>
      mul_nonneg hp (inv_nonneg.2 (hl.trans hv'.1).le))
    (Filter.Eventually.of_forall fun v hv' => hv'.2 :
      Ioc ρ 1 ∩ Ioc l u ≤ᵐ[volume] Ioc l u)
  have he : (∫ v in Ioc l u, max 1 (ρ ^ r) * v⁻¹) =
      max 1 (ρ ^ r) * Real.log (u / l) := by
    rw [integral_const_mul, ← intervalIntegral.integral_of_le hlu,
      integral_inv_of_pos hl (hl.trans_le hlu)]
  exact hm.trans (he ▸ hs)

end ThresholdHC.PowerWindow
