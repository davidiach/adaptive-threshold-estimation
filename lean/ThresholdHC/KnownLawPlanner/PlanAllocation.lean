import ThresholdHC.EntropyTailUpper.Allocation

/-! Allocation of a budget from rounded weights.

The optimal mean count of level `i` is proportional to `√(v_i / k_i)`, where
`v_i` bounds the second moment of its correction and `k_i` its expected cost.
A planner computes weights `w_i` with `√(v_i/k_i) ≤ w_i ≤ θ √(v_i/k_i)`, for
example dyadic upper square roots with `θ = 2`, and uses the mean counts
`n_i = B w_i / Σ_j k_j w_j`. They spend the budget exactly, and the variance
term of the certificate is at most `θ (Σ_i √(v_i k_i))² / B`. -/

noncomputable section
open Real
open scoped BigOperators

namespace ThresholdHC.KnownLawPlanner
open ThresholdHC.EntropyTailUpper
variable {ι : Type*} [Fintype ι]

/-- The mean count of level `i` from the weights `w`. -/
def planCount (B : ℝ) (k w : ι → ℝ) (i : ι) : ℝ := B * w i / ∑ j, k j * w j

theorem planCount_pos [Nonempty ι] {B : ℝ} {k w : ι → ℝ} (hB : 0 < B) (hk : ∀ i, 0 < k i)
    (hw : ∀ i, 0 < w i) (i : ι) : 0 < planCount B k w i :=
  div_pos (mul_pos hB (hw i))
    (Finset.sum_pos (fun j _ => mul_pos (hk j) (hw j)) Finset.univ_nonempty)

/-- The mean counts spend the budget exactly. -/
theorem planCount_work [Nonempty ι] {B : ℝ} {k w : ι → ℝ} (hk : ∀ i, 0 < k i)
    (hw : ∀ i, 0 < w i) : ∑ i, k i * planCount B k w i = B := by
  have hW : 0 < ∑ j, k j * w j :=
    Finset.sum_pos (fun j _ => mul_pos (hk j) (hw j)) Finset.univ_nonempty
  have he (i : ι) : k i * planCount B k w i = B / (∑ j, k j * w j) * (k i * w i) := by
    unfold planCount
    ring
  simp only [he, ← Finset.mul_sum]
  exact div_mul_cancel₀ _ hW.ne'

/-- For positive `v` and `k`: `k √(v/k) = √(v k)`. -/
theorem mul_sqrt_div {v k : ℝ} (hv : 0 < v) (hk : 0 < k) : k * sqrt (v / k) = sqrt (v * k) := by
  have h : v * k = k ^ 2 * (v / k) := by
    field_simp
  rw [h, sqrt_mul (sq_nonneg k), sqrt_sq hk.le]

/-- For positive `v` and `k`: `v / √(v/k) = √(v k)`. -/
theorem div_sqrt_div {v k : ℝ} (hv : 0 < v) (hk : 0 < k) : v / sqrt (v / k) = sqrt (v * k) := by
  have hs : 0 < sqrt (v / k) := sqrt_pos.mpr (div_pos hv hk)
  rw [div_eq_iff hs.ne', ← sqrt_mul (mul_nonneg hv.le hk.le)]
  have h : v * k * (v / k) = v ^ 2 := by
    field_simp
  rw [h, sqrt_sq hv.le]

/-- The variance term of the certificate. With weights between `√(v_i/k_i)`
and `θ √(v_i/k_i)`, it is at most `θ (Σ_i √(v_i k_i))² / B`. -/
theorem planCount_variance_le [Nonempty ι] {B θ : ℝ} {v k w : ι → ℝ} (hB : 0 < B)
    (hv : ∀ i, 0 < v i) (hk : ∀ i, 0 < k i) (hlow : ∀ i, sqrt (v i / k i) ≤ w i)
    (hup : ∀ i, w i ≤ θ * sqrt (v i / k i)) :
    ∑ i, v i / planCount B k w i ≤ θ * (allocationCertificate v k) ^ 2 / B := by
  have hw : ∀ i, 0 < w i := fun i =>
    lt_of_lt_of_le (sqrt_pos.mpr (div_pos (hv i) (hk i))) (hlow i)
  have hW : 0 < ∑ j, k j * w j :=
    Finset.sum_pos (fun j _ => mul_pos (hk j) (hw j)) Finset.univ_nonempty
  have hS : 0 < allocationCertificate v k := allocationCertificate_pos hv hk
  have he (i : ι) : v i / planCount B k w i = (∑ j, k j * w j) / B * (v i / w i) := by
    unfold planCount
    field_simp [(hw i).ne', hW.ne', hB.ne']
  have hsum1 : ∑ i, v i / w i ≤ allocationCertificate v k := by
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← div_sqrt_div (hv i) (hk i)]
    exact div_le_div_of_nonneg_left (hv i).le (sqrt_pos.mpr (div_pos (hv i) (hk i))) (hlow i)
  have hsum2 : ∑ j, k j * w j ≤ θ * allocationCertificate v k := by
    unfold allocationCertificate
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    calc k j * w j ≤ k j * (θ * sqrt (v j / k j)) :=
          mul_le_mul_of_nonneg_left (hup j) (hk j).le
      _ = θ * sqrt (v j * k j) := by rw [← mul_sqrt_div (hv j) (hk j)]; ring
  simp only [he, ← Finset.mul_sum]
  calc (∑ j, k j * w j) / B * ∑ i, v i / w i
      ≤ θ * allocationCertificate v k / B * allocationCertificate v k := by
        refine mul_le_mul (div_le_div_of_nonneg_right hsum2 hB.le) hsum1 ?_ ?_
        · exact Finset.sum_nonneg fun i _ => div_nonneg (hv i).le (hw i).le
        · exact div_nonneg (hW.le.trans hsum2) hB.le
    _ = θ * (allocationCertificate v k) ^ 2 / B := by ring

end ThresholdHC.KnownLawPlanner
