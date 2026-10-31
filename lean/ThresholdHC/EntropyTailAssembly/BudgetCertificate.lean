import ThresholdHC.EntropyTailAssembly.CertificateAlgebra
import ThresholdHC.EntropyTailAssembly.LevelCertificates

/-! Uniform finite multilevel allocation certificate. This is an analytic
certificate for the actual single-coin races; realization of random numbers
of independent population calls is a separate probabilistic obligation. -/

noncomputable section
open MeasureTheory Set Real
open scoped BigOperators

namespace ThresholdHC.EntropyTailAssembly
open ThresholdHC.Tier6

def levelWorkCertificate (σ τ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ]
    (ρ Γ z : ℝ) (hρ : 0 < ρ) (l : ℕ) : ℝ :=
  128*(l+1)*Γ+6*(∫ d : Gap, (d:ℝ)⁻¹ ∂τ)^2/ρ+
  2*ordinaryCost τ (4^(errorCapExponent (σ+τ) (levelAccuracy ρ l) (levelAccuracy_pos hρ l)))+
  2*z*4^(errorCapExponent (σ+τ) (levelAccuracy ρ l) (levelAccuracy_pos hρ l))

theorem levelWorkCertificate_nonneg (σ τ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ]
    {ρ Γ z : ℝ} (hρ : 0 < ρ)
    (hΓ : 0 ≤ Γ) (hz : 0 ≤ z) (l : ℕ) : 0 ≤ levelWorkCertificate σ τ ρ Γ z hρ l := by
  unfold levelWorkCertificate
  positivity [ordinaryCost_nonneg τ (by positivity : (0:ℝ) ≤
    4^(errorCapExponent (σ+τ) (levelAccuracy ρ l) (levelAccuracy_pos hρ l)))]

theorem levelWorkCertificate_root_sum (σ τ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ]
    (hσ : Integrable (fun d : Gap => (d:ℝ)⁻¹^2) σ)
    (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ) {ρ Γ z : ℝ}
    (hρ : 0 < ρ) (hΓ : 0 ≤ Γ) (hz : 0 ≤ z)
    (hAΓ : (∫ d : Gap, (d:ℝ)⁻¹^2 ∂σ) ≤ Γ)
    (hm : ρ/128 < (σ+τ).real univ) (J : ℕ) (hzJ : z ≤ levelAccuracy ρ J/8) :
    (∑ l ∈ Finset.range (J+1), sqrt (levelAccuracy ρ l*levelWorkCertificate σ τ ρ Γ z hρ l)) ≤
      27*sqrt (ρ*Γ)+5203*(∫ d : Gap, (d:ℝ)⁻¹ ∂τ) := by
  let k := fun l => errorCapExponent (σ+τ) (levelAccuracy ρ l) (levelAccuracy_pos hρ l)
  let H := ∫ d : Gap, (d:ℝ)⁻¹ ∂τ
  let C := sqrt (ρ*Γ)
  have hH : 0 ≤ H := integral_nonneg (fun d => inv_nonneg.mpr d.property.1.le)
  have hC : 0 ≤ C := sqrt_nonneg _
  have hAC : sqrt (ρ*(∫ d : Gap, (d:ℝ)⁻¹^2 ∂σ)) ≤ C :=
    sqrt_le_sqrt (mul_le_mul_of_nonneg_left hAΓ hρ.le)
  have h := Finset.sum_le_sum (s := Finset.range (J+1)) (fun l _ =>
    level_work_root hρ hΓ hH hz (by positivity : (0:ℝ) ≤ 4^(k l))
      (ordinaryCost_nonneg τ (by positivity : (0:ℝ) ≤ 4^(k l))) l)
  change (∑ l ∈ Finset.range (J+1), sqrt (levelAccuracy ρ l*levelWorkCertificate σ τ ρ Γ z hρ l)) ≤
    ∑ l ∈ Finset.range (J+1), (12*C*(l+1)*(1/4:ℝ)^(l+1)+3*H*(1/4:ℝ)^(l+1)+
      (3/2)*sqrt (levelAccuracy ρ l*ordinaryCost τ (4^(k l)))+
      (3/2)*sqrt (z*levelAccuracy ρ l*4^(k l))) at h
  simp only [Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum] at h
  have h1 := mul_le_mul_of_nonneg_left (quarter_linear_sum (J+1)) (show 0 ≤ 12*C by positivity)
  have h2 := mul_le_mul_of_nonneg_left (quarter_tail_sum (J+1)) (show 0 ≤ 3*H by positivity)
  have h3 := mixed_work_sum σ τ hσ hτ hρ hm J
  have h4 := unresolved_work_sum σ τ hσ hτ hρ hz hm J hzJ
  change (∑ l ∈ Finset.range (J+1), sqrt (levelAccuracy ρ l*ordinaryCost τ (4^(k l)))) ≤
    3340*H+12*sqrt (ρ*(∫ d : Gap, (d:ℝ)⁻¹^2 ∂σ)) at h3
  change (∑ l ∈ Finset.range (J+1), sqrt (z*levelAccuracy ρ l*4^(k l))) ≤
    2*sqrt (ρ*(∫ d : Gap, (d:ℝ)⁻¹^2 ∂σ))+128*H at h4
  simp only [mul_assoc] at h4
  change _ ≤ 27*C+5203*H
  nlinarith only [h, h1, h2, h3, h4, hAC, hC]

theorem multilevel_budget_certificate (σ τ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ]
    (hσ : Integrable (fun d : Gap => (d:ℝ)⁻¹^2) σ)
    (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ) {ρ Γ z : ℝ}
    (hρ : 0 < ρ) (hΓ : 0 ≤ Γ) (hz : 0 ≤ z)
    (hAΓ : (∫ d : Gap, (d:ℝ)⁻¹^2 ∂σ) ≤ Γ)
    (hm : ρ/128 < (σ+τ).real univ) (J : ℕ) (hzJ : z ≤ levelAccuracy ρ J/8) :
    (∑ l ∈ Finset.range (J+1), sqrt (17*levelAccuracy ρ l*
      adjacentCost (levelWorkCertificate σ τ ρ Γ z hρ) l)) ≤
      28000*(sqrt (ρ*Γ)+(∫ d : Gap, (d:ℝ)⁻¹ ∂τ)) := by
  have h1 := adjacent_root_sum hρ (levelWorkCertificate σ τ ρ Γ z hρ)
    (levelWorkCertificate_nonneg σ τ hρ hΓ hz) J
  have h2 := levelWorkCertificate_root_sum σ τ hσ hτ hρ hΓ hz hAΓ hm J hzJ
  have hH : 0 ≤ ∫ d : Gap, (d:ℝ)⁻¹ ∂τ := integral_nonneg (fun d => inv_nonneg.mpr d.property.1.le)
  nlinarith [sqrt_nonneg (ρ*Γ)]

end ThresholdHC.EntropyTailAssembly
