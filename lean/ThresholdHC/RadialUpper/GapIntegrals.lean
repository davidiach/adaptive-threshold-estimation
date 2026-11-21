import ThresholdHC.RadialUpper.Cutoff

/-! One-dimensional integrals against the quadratic law `32x dx` on `(0,1/4]`:
the exponential moment, the radial first moment, and the inverse moment. -/

noncomputable section
namespace ThresholdHC.RadialUpper
open MeasureTheory Set ThresholdHC.Tier6
open ThresholdHC.ConfidenceTransfer (criticalPositiveLaw)
open ThresholdHC.CriticalEntropy (criticalGapLaw)

/-- Integrals of functions of the gap value as integrals with density `32x` on `(0,1/4]`. -/
theorem positive_integral_density (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ d, f (d : ℝ) ∂criticalPositiveLaw) = ∫ x in Ioc (0 : ℝ) (1/4), 32*x*f x := by
  rw [positive_integral_map f hf]
  have hr : criticalGapLaw.restrict (Ioc 0 (1/4)) = criticalGapLaw :=
    Measure.restrict_eq_self_of_ae_mem CriticalUpper.criticalGap_ae_support
  rw [← hr, CriticalPsi.criticalGap_integral_Ioc f 0 (1/4) le_rfl le_rfl]

/-- The exponential moment: `∫ 32 x e^{-l x} dx <= 32/l^2` on `(0,1/4]`. -/
theorem density_exp_le {l : ℝ} (hl : 0 < l) :
    (∫ x in Ioc (0 : ℝ) (1/4), 32*x*Real.exp (-(l*x))) ≤ 32/l^2 := by
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1/4)]
  have hd : ∀ x ∈ uIcc (0 : ℝ) (1/4), HasDerivAt
      (fun x => -(32/l^2)*((1+l*x)*Real.exp (-(l*x)))) (32*x*Real.exp (-(l*x))) x := by
    intro x _
    have h1 : HasDerivAt (fun x => 1+l*x) l x := by
      simpa using ((hasDerivAt_id x).const_mul l).const_add 1
    have h2 : HasDerivAt (fun x => Real.exp (-(l*x))) (Real.exp (-(l*x)) * (-l)) x := by
      simpa using ((hasDerivAt_id x).const_mul l).neg.exp
    have h3 := (h1.mul h2).const_mul (-(32/l^2))
    convert h3 using 1
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [mul_zero, add_zero, neg_zero, Real.exp_zero, mul_one]
  have : 0 ≤ (32/l^2) * ((1+l*(1/4)) * Real.exp (-(l*(1/4)))) := by positivity
  linarith

/-- The radial first moment: `E[w_b(D) D] >= 4 b^2` for `b <= 1/8`. -/
theorem weight_moment_lower {b : ℝ} (hb0 : 0 < b) (hb : b ≤ 1/8) :
    4*b^2 ≤ ∫ d, radialWeight b d * d ∂criticalPositiveLaw := by
  have hf : Measurable (fun x : ℝ => min 1 (b^2/x^2) * x) := by fun_prop
  have h := positive_integral_density (fun x : ℝ => min 1 (b^2/x^2) * x) hf
  change (∫ d, radialWeight b d * d ∂criticalPositiveLaw) = _ at h
  rw [h]
  have he : ∀ x : ℝ, 32*x*(min 1 (b^2/x^2) * x) = 32 * min (x^2) (b^2) := by
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · simp [sq_nonneg b]
    · have hx2 : 0 < x^2 := by positivity
      rw [show 32*x*(min 1 (b^2/x^2)*x) = 32 * (x^2 * min 1 (b^2/x^2)) by ring,
        mul_min_of_nonneg _ _ hx2.le, mul_one, mul_div_cancel₀ _ hx2.ne']
  simp_rw [he]
  have hint : IntegrableOn (fun x : ℝ => 32 * min (x^2) (b^2)) (Ioc 0 (1/4)) :=
    ((by fun_prop : Continuous (fun x : ℝ => 32 * min (x^2) (b^2))).intervalIntegrable 0 (1/4)).1
  have hmono := setIntegral_mono_set hint (ae_of_all _ (fun x => by positivity))
    (Ioc_subset_Ioc_left hb0.le).eventuallyLE
  have hval : (∫ x in Ioc b (1/4), 32 * min (x^2) (b^2)) = 32*b^2*(1/4-b) := by
    rw [setIntegral_congr_fun measurableSet_Ioc (g := fun _ => 32*b^2) (fun x hx => by
      have : b^2 ≤ x^2 := by nlinarith [hx.1]
      simp only [min_eq_right this])]
    rw [setIntegral_const, Real.volume_real_Ioc_of_le (by linarith), smul_eq_mul]
    ring
  nlinarith

/-- The inverse moment: if `g(x) <= 1/(2x)` on `(0,1/4]` then `E g(D) <= 4`. -/
theorem inverse_moment_le (g : ℝ → ℝ) (hg : Continuous g)
    (hgb : ∀ x : ℝ, 0 < x → x ≤ 1/4 → g x ≤ 1/(2*x)) :
    (∫ d, g (d : ℝ) ∂criticalPositiveLaw) ≤ 4 := by
  rw [positive_integral_density g hg.measurable]
  have hi : IntegrableOn (fun x => 32*x*g x) (Ioc (0 : ℝ) (1/4)) :=
    ((by fun_prop : Continuous fun x => 32*x*g x).intervalIntegrable 0 (1/4)).1
  have hc : IntegrableOn (fun _ : ℝ => (16 : ℝ)) (Ioc (0 : ℝ) (1/4)) := integrableOn_const (by simp [Real.volume_Ioc])
  calc _ ≤ ∫ x in Ioc (0 : ℝ) (1/4), (16 : ℝ) := setIntegral_mono_on hi hc measurableSet_Ioc
          (fun x hx => by
            have h1 := mul_le_mul_of_nonneg_left (hgb x hx.1 hx.2) (by linarith [hx.1] : 0 ≤ 32*x)
            have h2 : 32*x*(1/(2*x)) = 16 := by field_simp [hx.1.ne']; ring
            linarith)
    _ = 4 := by
      rw [setIntegral_const, Real.volume_real_Ioc_of_le (by norm_num), smul_eq_mul]
      norm_num

end ThresholdHC.RadialUpper
