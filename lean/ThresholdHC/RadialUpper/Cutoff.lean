import ThresholdHC.RadialUpper.Specification
import ThresholdHC.Tier3.Optimizer
import ThresholdHC.CriticalPsi.Formula

/-! The calibrated cutoff of the radial submodel.

Under the quadratic law the radial mass is `E w_b(D) = 16 b^2 (1 + log(1/(16 b^2)))`
for `0 < b <= 1/4`. The cutoff with mass `rho` exists and is unique (the arbitrary-law
cutoff theorem), and lies below `1/4`. The scalar facts `b <= 1/8`,
`rho <= 32 b^2 L` and `rho <= 8 b` follow from the mass formula. -/

noncomputable section
namespace ThresholdHC.RadialUpper
open MeasureTheory Set ThresholdHC.Tier6
open ThresholdHC.ConfidenceTransfer (criticalPositiveLaw criticalPositiveLaw_map)
open ThresholdHC.CriticalEntropy (criticalGapLaw)

theorem radial_support : ∀ᵐ (d : Gap) ∂criticalPositiveLaw, (d : ℝ) ≤ 1/4 := by
  have h : ∀ᵐ x ∂(Measure.map (Subtype.val : Gap → ℝ) criticalPositiveLaw), x ≤ (1/4 : ℝ) := by
    rw [criticalPositiveLaw_map]
    filter_upwards [CriticalUpper.criticalGap_ae_support] with x hx using hx.2
  exact ae_of_ae_map measurable_subtype_coe.aemeasurable h

/-- Integrals of functions of the gap value move to the quadratic law on the line. -/
theorem positive_integral_map (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ d, f (d : ℝ) ∂criticalPositiveLaw) = ∫ x, f x ∂criticalGapLaw := by
  rw [← criticalPositiveLaw_map, integral_map measurable_subtype_coe.aemeasurable
    hf.aestronglyMeasurable]

theorem radial_mass {b : ℝ} (hb0 : 0 < b) (hb : b ≤ 1/4) :
    signMean criticalPositiveLaw (radialWeight b) = 16*b^2*(1+Real.log (1/(16*b^2))) := by
  have h := CriticalPsi.critical_allocation_mass b hb0 hb
  rw [← h]
  exact positive_integral_map (fun x => Tier3.allocation b x)
    (by unfold Tier3.allocation; fun_prop)

theorem cutoff_exists_unique : RadialCutoffStatement := by
  intro ρ hρ hρq
  obtain ⟨t, ht, _, hm, huniq⟩ := Tier3.arbitrary_law_cutoff Gap criticalPositiveLaw
    Subtype.val ρ measurable_subtype_coe (ae_of_all _ (fun d => d.2)) hρ (by linarith)
  have hm' : signMean criticalPositiveLaw (radialWeight t) = ρ := hm
  have ht4 : t < 1/4 := by
    by_contra hn
    have hae : ∀ᵐ d ∂criticalPositiveLaw, radialWeight t d = 1 := by
      filter_upwards [radial_support] with d hd
      exact Tier3.allocation_eq_one d.2.1 (hd.trans (not_lt.mp hn))
    have hone : signMean criticalPositiveLaw (radialWeight t) = 1 := by
      unfold signMean
      rw [integral_congr_ae hae]
      simp
    linarith
  refine ⟨t, ⟨ht, ht4, hm'⟩, ?_⟩
  rintro s ⟨hs, _, hsm⟩
  exact huniq s hs hsm

theorem two_log_le_self {u : ℝ} (hu : 0 < u) : 2 * Real.log u ≤ u := by
  set s := Real.sqrt u with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hu
  have hsu : s^2 = u := Real.sq_sqrt hu.le
  have hl : Real.log u = 2 * Real.log s := by rw [← hsu, Real.log_pow]; push_cast; ring
  have h1 := Real.log_le_sub_one_of_pos hs0
  nlinarith [sq_nonneg (s-2)]

/-- Scalar consequences of the calibration used by the constants. -/
theorem calibrated_facts {ρ b : ℝ} (hρ : 0 < ρ) (hρq : ρ ≤ 1/4) (h : RadialCalibrated ρ b) :
    0 < b ∧ b ≤ 1/8 ∧ ρ ≤ 32*b^2*radialLogFactor ρ ∧ ρ ≤ 8*b ∧ 1 ≤ radialLogFactor ρ := by
  obtain ⟨hb0, hb4, hm⟩ := h
  rw [radial_mass hb0 hb4.le] at hm
  set β := 16*b^2 with hβ
  have hβ0 : 0 < β := by positivity
  have hβ1 : β ≤ 1 := by nlinarith
  set u := 1 + Real.log (1/β) with hu
  have hlogβ : 0 ≤ Real.log (1/β) := Real.log_nonneg (by rw [le_div_iff₀ hβ0]; linarith)
  have hu1 : 1 ≤ u := by linarith
  have hρu : ρ = β*u := hm.symm
  have hL1 : 1 ≤ radialLogFactor ρ := by
    unfold radialLogFactor
    have : 0 ≤ Real.log (1/ρ) := Real.log_nonneg (by rw [le_div_iff₀ hρ]; linarith)
    linarith
  refine ⟨hb0, ?_, ?_, ?_, hL1⟩
  · have hβq : β ≤ 1/4 := by nlinarith
    nlinarith
  · have hL : radialLogFactor ρ = u - Real.log u := by
      unfold radialLogFactor
      rw [hρu, one_div, mul_inv, Real.log_mul (inv_pos.mpr hβ0).ne' (inv_pos.mpr (by linarith)).ne',
        Real.log_inv u, ← one_div]
      ring
    rw [hL, hρu]
    have h2 := two_log_le_self (show 0 < u by linarith)
    have : β * u ≤ 2*β*(u - Real.log u) := by nlinarith
    linarith
  · have hl := Real.log_le_sub_one_of_pos (show 0 < 1/(4*b) by positivity)
    have he : 1/β = (1/(4*b))^2 := by rw [hβ]; field_simp; ring
    have hlog : Real.log (1/β) = 2*Real.log (1/(4*b)) := by rw [he, Real.log_pow]; push_cast; ring
    have hm2 : b^2 * Real.log (1/(4*b)) ≤ b^2 * (1/(4*b) - 1) :=
      mul_le_mul_of_nonneg_left hl (sq_nonneg b)
    have hb2 : b^2 * (1/(4*b)) = b/4 := by field_simp
    rw [hρu, hu, hlog]
    nlinarith

end ThresholdHC.RadialUpper
