import ThresholdHC.FiniteQuantileFormula.Specification

/-! Finite atomic measures `∑ i, ofReal (c i) • dirac (d i)` with real weights:
restriction, real mass, integrals, scaling, sums and finite support. These are
real-weight versions of the rational lemmas of `FiniteLawCertificates.Atomic`. -/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators Classical
namespace ThresholdHC.FiniteQuantileFormula
open ThresholdHC.Tier6

variable {n : ℕ}

theorem atoms_restrict (d : Fin n → Gap) (c : Fin n → ℝ) (S : Set Gap) :
    (∑ i, ENNReal.ofReal (c i) • Measure.dirac (d i)).restrict S =
      ∑ i, ENNReal.ofReal (if d i ∈ S then c i else 0) • Measure.dirac (d i) := by
  rw [← Measure.sum_fintype, Measure.restrict_sum_of_countable, Measure.sum_fintype]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : d i ∈ S <;> simp [Measure.restrict_smul, restrict_dirac, hi]

theorem atoms_apply (d : Fin n → Gap) (c : Fin n → ℝ) (S : Set Gap) :
    (∑ i, ENNReal.ofReal (c i) • Measure.dirac (d i)) S =
      ∑ i, if d i ∈ S then ENNReal.ofReal (c i) else 0 := by
  rw [← Measure.restrict_apply_univ, atoms_restrict]
  simp only [Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

theorem atoms_real (d : Fin n → Gap) (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i) (S : Set Gap) :
    (∑ i, ENNReal.ofReal (c i) • Measure.dirac (d i)).real S =
      ∑ i, if d i ∈ S then c i else 0 := by
  have hn (i : Fin n) : 0 ≤ (if d i ∈ S then c i else 0) := by
    split_ifs
    · exact hc i
    · exact le_rfl
  rw [measureReal_def, atoms_apply]
  have he : (∑ i, if d i ∈ S then ENNReal.ofReal (c i) else 0) =
      ENNReal.ofReal (∑ i, if d i ∈ S then c i else 0) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => hn i)]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  rw [he, ENNReal.toReal_ofReal (Finset.sum_nonneg (fun i _ => hn i))]

theorem atoms_integral (d : Fin n → Gap) (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    (f : Gap → ℝ) :
    ∫ x, f x ∂(∑ i, ENNReal.ofReal (c i) • Measure.dirac (d i)) = ∑ i, c i * f (d i) := by
  rw [integral_finsetSum_measure (fun i _ =>
    (integrable_dirac (by finiteness)).smul_measure (by finiteness))]
  simp only [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hc _), smul_eq_mul]

theorem atoms_smul (d : Fin n → Gap) (c : Fin n → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    ENNReal.ofReal r • (∑ i, ENNReal.ofReal (c i) • Measure.dirac (d i)) =
      ∑ i, ENNReal.ofReal (r * c i) • Measure.dirac (d i) := by
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_smul, ENNReal.ofReal_mul hr]

theorem atoms_add (d : Fin n → Gap) (b c : Fin n → ℝ) (hb : ∀ i, 0 ≤ b i)
    (hc : ∀ i, 0 ≤ c i) :
    (∑ i, ENNReal.ofReal (b i) • Measure.dirac (d i)) +
        (∑ i, ENNReal.ofReal (c i) • Measure.dirac (d i)) =
      ∑ i, ENNReal.ofReal (b i + c i) • Measure.dirac (d i) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [ENNReal.ofReal_add (hb i) (hc i), add_smul]

theorem atoms_support_finite (d : Fin n → Gap) (c : Fin n → ℝ) :
    (∑ i, ENNReal.ofReal (c i) • Measure.dirac (d i)).support.Finite := by
  apply (Set.finite_range d).subset
  apply Measure.support_subset_of_isClosed (Set.finite_range d).isClosed
  rw [mem_ae_iff, atoms_apply]
  apply Finset.sum_eq_zero
  intro i _
  have hi : d i ∉ (Set.range d)ᶜ := fun h => h ⟨i, rfl⟩
  simp [hi]

end ThresholdHC.FiniteQuantileFormula
