import Mathlib

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace ThresholdHC.CriticalEntropy

/-- A direct moment bound that retains the additive radius term. -/
theorem square_le_shifted_exponentials (e R a : ℝ) (hR : 0 ≤ R) (ha : 0 < a) :
    e^2 ≤ R^2+(2*R*a+2*a^2)*Real.exp (-R/a)*
      (Real.exp (e/a)+Real.exp (-e/a)) := by
  have hC : 0 ≤ 2*R*a+2*a^2 := by positivity
  by_cases he : |e| ≤ R
  · have hs : e^2 ≤ R^2 := by nlinarith [sq_abs e,abs_nonneg e]
    exact hs.trans (le_add_of_nonneg_right (by positivity))
  · let v := (|e|-R)/a
    have hv : 0 ≤ v := div_nonneg (by linarith) ha.le
    have hve : |e| = R+a*v := by dsimp [v]; field_simp; ring
    have h1 : v ≤ Real.exp v := by linarith [Real.add_one_le_exp v]
    have h2 : v^2 ≤ 2*Real.exp v := by
      have h := Real.pow_div_factorial_le_exp v hv 2
      norm_num at h
      linarith
    have hA := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 2*R*a)
    have hB := mul_le_mul_of_nonneg_left h2 (sq_nonneg a)
    have hs : e^2 ≤ R^2+(2*R*a+2*a^2)*Real.exp v := by
      rw [← sq_abs e,hve]
      nlinarith
    have habs : Real.exp (|e|/a) ≤ Real.exp (e/a)+Real.exp (-e/a) := by
      by_cases hp : 0 ≤ e
      · rw [abs_of_nonneg hp]
        exact le_add_of_nonneg_right (Real.exp_nonneg _)
      · rw [abs_of_nonpos (le_of_not_ge hp)]
        exact le_add_of_nonneg_left (Real.exp_nonneg _)
    have hev : Real.exp v = Real.exp (-R/a)*Real.exp (|e|/a) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [v]
      ring
    rw [hev] at hs
    calc
      _ ≤ R^2+(2*R*a+2*a^2)*(Real.exp (-R/a)*Real.exp (|e|/a)) := hs
      _ ≤ _ := by
        have hm := mul_le_mul_of_nonneg_left habs (mul_nonneg hC (Real.exp_nonneg (-R/a)))
        nlinarith

/-- Two exponential-moment bounds imply genuine square integrability and a
quantitative second-moment bound, without totalized infinite integrals. -/
theorem second_moment_of_exponential_bounds {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hX : AEStronglyMeasurable X μ) (R a : ℝ) (hR : 0 ≤ R) (ha : 0 < a)
    (hp : Integrable (fun ω => Real.exp (X ω/a)) μ)
    (hm : Integrable (fun ω => Real.exp (-X ω/a)) μ)
    (hpb : (∫ ω, Real.exp (X ω/a) ∂μ) ≤ Real.exp (R/a-Real.log 2))
    (hmb : (∫ ω, Real.exp (-X ω/a) ∂μ) ≤ Real.exp (R/a-Real.log 2)) :
    MemLp X 2 μ ∧ (∫ ω, (X ω)^2 ∂μ) ≤ R^2+2*R*a+2*a^2 := by
  let C := (2*R*a+2*a^2)*Real.exp (-R/a)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbound (ω : Ω) : (X ω)^2 ≤ R^2+C*(Real.exp (X ω/a)+Real.exp (-X ω/a)) :=
    square_le_shifted_exponentials (X ω) R a hR ha
  have hK : Integrable (fun ω => R^2+C*(Real.exp (X ω/a)+Real.exp (-X ω/a))) μ :=
    (integrable_const _).add ((hp.add hm).const_mul C)
  have hsumI : Integrable (fun ω => Real.exp (X ω/a)+Real.exp (-X ω/a)) μ := hp.add hm
  have hsq : Integrable (fun ω => (X ω)^2) μ := by
    apply hK.mono' (hX.pow 2)
    apply ae_of_all
    intro ω
    simpa only [Real.norm_eq_abs,Pi.pow_apply,abs_of_nonneg (sq_nonneg (X ω))] using hbound ω
  refine ⟨(memLp_two_iff_integrable_sq hX).mpr hsq,?_⟩
  have hsum : (∫ ω, Real.exp (X ω/a) ∂μ)+(∫ ω, Real.exp (-X ω/a) ∂μ) ≤ Real.exp (R/a) := by
    calc
      _ ≤ 2*Real.exp (R/a-Real.log 2) := by linarith
      _ = _ := by rw [Real.exp_sub,Real.exp_log (by norm_num : (0 : ℝ) < 2)]; ring
  calc
    _ ≤ ∫ ω, R^2+C*(Real.exp (X ω/a)+Real.exp (-X ω/a)) ∂μ :=
      integral_mono hsq hK hbound
    _ = R^2+C*((∫ ω, Real.exp (X ω/a) ∂μ)+(∫ ω, Real.exp (-X ω/a) ∂μ)) := by
      rw [integral_add (integrable_const _) (hsumI.const_mul C),integral_const_mul,
        integral_add hp hm]
      simp
    _ ≤ R^2+C*Real.exp (R/a) := by gcongr
    _ = _ := by
      dsimp [C]
      rw [mul_assoc,← Real.exp_add]
      have he : -R/a+R/a = 0 := by ring
      rw [he,Real.exp_zero,mul_one]
      ring

end ThresholdHC.CriticalEntropy
