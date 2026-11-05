import ThresholdHC.QuantileOptimality.Specification

noncomputable section
open Real
namespace ThresholdHC.QuantileOptimality

theorem atom_root_identity {ρ t G : ℝ} (hρ : 0 < ρ) (ht : 0 < t) (hG : 0 ≤ G) :
    sqrt (ρ*(ρ/t^2*G)) = (ρ/t)*sqrt G := by
  apply (sq_eq_sq₀ (sqrt_nonneg _) (mul_nonneg (div_nonneg hρ.le ht.le) (sqrt_nonneg _))).mp
  rw [sq_sqrt (by positivity),mul_pow,sq_sqrt hG]
  field_simp

def finiteEnvelope (ρ A t : ℝ) : ℝ := A+4*t^2/ρ+sqrt (8*A*t^2/ρ)

theorem finiteEnvelope_nonneg {ρ A t : ℝ} (hρ : 0 < ρ) (hA : 0 ≤ A) :
    0 ≤ finiteEnvelope ρ A t := by
  unfold finiteEnvelope
  positivity

theorem finiteEnvelope_scale {ρ A t : ℝ} (hρ : 0 < ρ) (hA : 0 ≤ A) (ht : 0 < t) :
    (ρ/t^2)*finiteEnvelope ρ A t =
      (ρ/t^2)*A+4+sqrt (2*((ρ/t^2)*A)*4) := by
  have hr : (ρ/t^2)*sqrt (8*A*t^2/ρ)=sqrt (2*((ρ/t^2)*A)*4) := by
    apply (sq_eq_sq₀ (by positivity) (sqrt_nonneg _)).mp
    rw [mul_pow,sq_sqrt (by positivity),sq_sqrt (by positivity)]
    field_simp
    ring
  unfold finiteEnvelope
  rw [mul_add,mul_add,hr]
  have he : (ρ/t^2)*(4*t^2/ρ)=4 := by field_simp
  rw [he]

theorem finiteEnvelope_continuous (ρ A : ℝ) : Continuous (finiteEnvelope ρ A) := by
  unfold finiteEnvelope
  fun_prop

theorem finiteEnvelope_zero (ρ A : ℝ) : finiteEnvelope ρ A 0=A := by
  simp [finiteEnvelope]

end ThresholdHC.QuantileOptimality
