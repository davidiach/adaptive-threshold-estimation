import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! Optimal finite positive-budget allocation of second-moment certificates.
Counts will be Poisson with these deterministic means; their probabilistic and
observable realizations are separate obligations. -/

noncomputable section
open Real
open scoped BigOperators

namespace ThresholdHC.EntropyTailUpper
variable {ι : Type*} [Fintype ι]

def allocationCertificate (v k : ι → ℝ) : ℝ := ∑ i, sqrt (v i * k i)

def allocationMean (B : ℝ) (v k : ι → ℝ) (i : ι) : ℝ :=
  B * sqrt (v i * k i) / (k i * allocationCertificate v k)

theorem allocationCertificate_pos [Nonempty ι] {v k : ι → ℝ}
    (hv : ∀ i, 0 < v i) (hk : ∀ i, 0 < k i) : 0 < allocationCertificate v k := by
  exact Finset.sum_pos (fun i _ => sqrt_pos.mpr (mul_pos (hv i) (hk i))) Finset.univ_nonempty

theorem allocationMean_pos [Nonempty ι] {B : ℝ} {v k : ι → ℝ}
    (hB : 0 < B) (hv : ∀ i, 0 < v i) (hk : ∀ i, 0 < k i) (i : ι) :
    0 < allocationMean B v k i := by
  exact div_pos (mul_pos hB (sqrt_pos.mpr (mul_pos (hv i) (hk i))))
    (mul_pos (hk i) (allocationCertificate_pos hv hk))

theorem allocationMean_work [Nonempty ι] {B : ℝ} {v k : ι → ℝ}
    (hv : ∀ i, 0 < v i) (hk : ∀ i, 0 < k i) : ∑ i, k i * allocationMean B v k i = B := by
  have hA := allocationCertificate_pos hv hk
  have he (i : ι) : k i * allocationMean B v k i =
      (B/allocationCertificate v k) * sqrt (v i * k i) := by
    unfold allocationMean
    field_simp [(hk i).ne']
  simp only [he, ← Finset.mul_sum]
  change B / allocationCertificate v k * allocationCertificate v k = B
  exact div_mul_cancel₀ _ hA.ne'

theorem allocationMean_variance [Nonempty ι] {B : ℝ} {v k : ι → ℝ}
    (hB : 0 < B) (hv : ∀ i, 0 < v i) (hk : ∀ i, 0 < k i) :
    ∑ i, v i / allocationMean B v k i = (allocationCertificate v k)^2/B := by
  have hA := allocationCertificate_pos hv hk
  have he (i : ι) : v i / allocationMean B v k i =
      (allocationCertificate v k/B) * sqrt (v i * k i) := by
    have hs := sq_sqrt (mul_nonneg (hv i).le (hk i).le)
    have hsp := sqrt_pos.mpr (mul_pos (hv i) (hk i))
    unfold allocationMean
    field_simp [hB.ne', (hk i).ne', hA.ne', hsp.ne']
    nlinarith only [hs]
  simp only [he, ← Finset.mul_sum]
  change allocationCertificate v k / B * allocationCertificate v k = _
  ring

theorem allocation_certificate_optimal {B : ℝ} {v k x : ι → ℝ}
    (hB : 0 < B) (hv : ∀ i, 0 ≤ v i) (hk : ∀ i, 0 ≤ k i) (hx : ∀ i, 0 < x i)
    (hwork : ∑ i, k i*x i ≤ B) :
    (allocationCertificate v k)^2/B ≤ ∑ i, v i/x i := by
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := fun i => sqrt (v i*k i)) (f := fun i => v i/x i) (g := fun i => k i*x i)
    (fun i _ => div_nonneg (hv i) (hx i).le)
    (fun i _ => mul_nonneg (hk i) (hx i).le)
    (fun i _ => by
      rw [sq_sqrt (mul_nonneg (hv i) (hk i))]
      exact le_of_eq (by field_simp [(hx i).ne']))
  apply (div_le_iff₀ hB).2
  exact hcs.trans (mul_le_mul_of_nonneg_left hwork
    (Finset.sum_nonneg (fun i _ => div_nonneg (hv i) (hx i).le)))

end ThresholdHC.EntropyTailUpper
