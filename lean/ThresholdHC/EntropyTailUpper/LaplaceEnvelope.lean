import ThresholdHC.EntropyTailUpper.NullMixture

/-! The null-mixture envelope at the matching gap's scale. Only the selected
component needs an inverse-square moment, and only the resolved tail needs
an inverse moment; the unresolved component is charged its mass. -/

noncomputable section
open MeasureTheory Real Set

namespace ThresholdHC.EntropyTailUpper
open ThresholdHC.Tier6

theorem gaussian_relative_bounds {d x : ℝ} (hd : 0 < d) (hx : 0 < x)
    (n : ℕ) (hn : 1 ≤ n*d^2) :
    exp (-2*n*x^2) ≤ d^2*x⁻¹^2 ∧ exp (-2*n*x^2) ≤ d*x⁻¹ := by
  have hd2 := sq_pos_of_pos hd
  have hy : (x/d)^2 ≤ n*x^2 := by
    rw [div_pow]
    apply (div_le_iff₀ hd2).mpr
    have h := mul_le_mul_of_nonneg_right hn (sq_nonneg x)
    nlinarith only [h]
  have he := add_one_le_exp (2*n*x^2)
  have hsq : (x/d)^2 ≤ exp (2*n*x^2) := by nlinarith [sq_nonneg (x/d)]
  have hlin : x/d ≤ exp (2*n*x^2) := by nlinarith [sq_nonneg (x/d-1)]
  have hs := inv_anti₀ (sq_pos_of_pos (div_pos hx hd)) hsq
  have hl := inv_anti₀ (div_pos hx hd) hlin
  have heq : exp (-2*n*x^2) = (exp (2*n*x^2))⁻¹ := by
    rw [← exp_neg]
    congr 1
    ring
  rw [heq]
  constructor
  · convert hs using 1
    field_simp
  · convert hl using 1
    field_simp

theorem nullLaplace_le_mass (ξ : Measure Gap) [IsFiniteMeasure ξ] (n : ℕ) :
    nullLaplace ξ n ≤ ξ.real univ := by
  have h := integral_mono (integrable_nullLaplace ξ n) (integrable_const (1:ℝ))
    (fun d : Gap => show exp (-2*n*(d:ℝ)^2) ≤ 1 from exp_le_one_iff.mpr (by
      nlinarith [mul_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ n) (sq_nonneg (d:ℝ))]))
  change (∫ d : Gap, exp (-2*n*(d:ℝ)^2) ∂ξ) ≤ ξ.real univ
  simpa only [integral_const, smul_eq_mul, mul_one] using h

theorem nullLaplace_three_piece (σ τ ζ : Measure Gap)
    [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ]
    (hσ : Integrable (fun x : Gap => (x:ℝ)⁻¹^2) σ)
    (hτ : Integrable (fun x : Gap => (x:ℝ)⁻¹) τ)
    (d : Gap) (n : ℕ) (hn : 1 ≤ n*(d:ℝ)^2) :
    nullLaplace (σ+τ+ζ) n ≤ ζ.real univ +
      (∫ x : Gap, (x:ℝ)⁻¹^2 ∂σ)*(d:ℝ)^2 + (∫ x : Gap, (x:ℝ)⁻¹ ∂τ)*(d:ℝ) := by
  have hs := integral_mono (integrable_nullLaplace σ n) (hσ.const_mul ((d:ℝ)^2))
    (fun x : Gap => (gaussian_relative_bounds d.property.1 x.property.1 n hn).1)
  have ht := integral_mono (integrable_nullLaplace τ n) (hτ.const_mul (d:ℝ))
    (fun x : Gap => (gaussian_relative_bounds d.property.1 x.property.1 n hn).2)
  rw [integral_const_mul] at hs ht
  have hz := nullLaplace_le_mass ζ n
  unfold nullLaplace at *
  rw [integral_add_measure (integrable_nullLaplace (σ+τ) n) (integrable_nullLaplace ζ n),
    integral_add_measure (integrable_nullLaplace σ n) (integrable_nullLaplace τ n)]
  linarith

end ThresholdHC.EntropyTailUpper
