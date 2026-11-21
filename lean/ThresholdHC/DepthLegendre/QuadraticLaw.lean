import ThresholdHC.DepthLegendre.Specification
import ThresholdHC.PowerWindow.Law

/-! The change of variable `d = h x`, `h = a √ρ`, for the exact quadratic law of
`thm:cap` in `research/2026-10-27-nonlinear-population/upper/proof-body.tex`
(lines 10, 110-111, 123-125). Under `ExactPowerLaw μ 2 a` (the law `2d dd/a²` on
`(0,a]`), for continuous `G`,
`∫ 1{d ≤ h} G(d/h) dμ = ∫₀¹ 2ρ x G(x) dx`. The law is the image of the uniform
variable `U` under `a √U`; the cut `a √U ≤ a √ρ` is `U ≤ ρ`, and `U = ρ x²`
finishes. Only `a ≤ 1/2` and `ρ ≤ 1` are needed. -/

noncomputable section
namespace ThresholdHC.DepthLegendre
open MeasureTheory Set
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.RareAboveTwo (ExactPowerLaw powerQuantile powerGapLaw measurable_powerQuantile
  uniformUnit_ae_positive)
open ThresholdHC.CriticalEntropy (uniformUnitMeasure)

/-- `∫₀^ρ G(√u/√ρ) du = ∫₀¹ 2ρ x G(x) dx`. -/
theorem sqrt_substitution {ρ : ℝ} (hρ : 0 < ρ) (G : ℝ → ℝ) (hG : Continuous G) :
    ∫ u in (0:ℝ)..ρ, G (Real.sqrt u / Real.sqrt ρ) = ∫ x in (0:ℝ)..1, 2 * ρ * x * G x := by
  have hs : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hρ
  have hsub := intervalIntegral.integral_comp_mul_deriv (a := 0) (b := 1)
    (f := fun x : ℝ => ρ * x^2) (f' := fun x => 2 * ρ * x)
    (g := fun u => G (Real.sqrt u / Real.sqrt ρ))
    (fun x _ => by simpa [mul_comm, mul_assoc, mul_left_comm] using
      ((hasDerivAt_id x).pow 2).const_mul ρ)
    (by fun_prop) (hG.comp (Real.continuous_sqrt.div_const _))
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, one_pow,
    mul_one] at hsub
  rw [← hsub]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le zero_le_one] at hx
  simp only [Function.comp_apply]
  rw [Real.sqrt_mul hρ.le, Real.sqrt_sq hx.1, mul_div_cancel_left₀ _ hs.ne']
  ring

theorem quadratic_cut_integral (μ : Measure Gap) [IsProbabilityMeasure μ] {a ρ : ℝ}
    (ha : 0 < a) (ha2 : a ≤ 1/2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hm : ExactPowerLaw μ 2 a)
    (G : ℝ → ℝ) (hG : Continuous G) :
    ∫ d, (if (d:ℝ) ≤ a * Real.sqrt ρ then G ((d:ℝ) / (a * Real.sqrt ρ)) else 0) ∂μ =
      ∫ x in (0:ℝ)..1, 2 * ρ * x * G x := by
  have h2 : (0:ℝ) < 2 := two_pos
  have hFm : Measurable (fun d : Gap =>
      if (d:ℝ) ≤ a * Real.sqrt ρ then G ((d:ℝ) / (a * Real.sqrt ρ)) else 0) :=
    Measurable.ite (measurableSet_le measurable_subtype_coe measurable_const)
      (hG.measurable.comp (measurable_subtype_coe.div_const _)) measurable_const
  rw [ThresholdHC.PowerWindow.exact_power_law_eq μ h2 ha ha2 hm, powerGapLaw,
    integral_map (measurable_powerQuantile 2 a h2 ha ha2).aemeasurable hFm.aestronglyMeasurable]
  have hae : (fun u => (if ((powerQuantile 2 a h2 ha ha2 u : Gap) : ℝ) ≤ a * Real.sqrt ρ then
        G (((powerQuantile 2 a h2 ha ha2 u : Gap) : ℝ) / (a * Real.sqrt ρ)) else 0))
      =ᵐ[uniformUnitMeasure] (Iic ρ).indicator (fun u => G (Real.sqrt u / Real.sqrt ρ)) := by
    filter_upwards [uniformUnit_ae_positive] with u hu
    have hq : ((powerQuantile 2 a h2 ha ha2 u : Gap) : ℝ) = a * Real.sqrt u := by
      simp only [powerQuantile, dite_eq_left hu]
      rw [Real.sqrt_eq_rpow, one_div]
    rw [hq, indicator_apply]
    simp only [mem_Iic, mul_le_mul_iff_right₀ ha, Real.sqrt_le_sqrt_iff hρ.le,
      mul_div_mul_left _ _ ha.ne']
  rw [integral_congr_ae hae, integral_indicator measurableSet_Iic, uniformUnitMeasure,
    Measure.restrict_restrict measurableSet_Iic]
  have hi : Iic ρ ∩ Icc (0 : ℝ) 1 = Icc 0 ρ := by
    ext u
    simp only [mem_inter_iff, mem_Iic, mem_Icc]
    constructor
    · rintro ⟨hu, hu0, _⟩
      exact ⟨hu0, hu⟩
    · rintro ⟨hu0, hu⟩
      exact ⟨hu, hu0, hu.trans hρ1⟩
  rw [hi, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hρ.le]
  exact sqrt_substitution hρ G hG

end ThresholdHC.DepthLegendre
