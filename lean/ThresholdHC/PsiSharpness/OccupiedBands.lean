import ThresholdHC.PsiSharpness.Specification
import ThresholdHC.PsiGap.Full

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace ThresholdHC.PsiSharpness
open ThresholdHC.Tier6 ThresholdHC.PsiClosedForm ThresholdHC.PsiGap
open ThresholdHC.EntropyTailQuantile

/-- Normalize only the nonzero coordinates; zero bands do not contribute to
the support cardinality in the entropy bound. -/
theorem finite_support_entropy {a : ℕ → ℝ} (ha : ∀ j, 0 ≤ a j)
    (hs : (Function.support a).Finite) {A : ℝ}
    (hA : 0 < A) (htotal : ∑ j ∈ hs.toFinset, a j = A) :
    0 < (Function.support a).ncard ∧
    (∑' j : ℕ, Real.negMulLog (a j / A)) ≤ Real.log (Function.support a).ncard := by
  classical
  let s := hs.toFinset
  have hsne : s.Nonempty := by
    by_contra h
    have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.1 h
    have : A = 0 := by simpa [s, ← htotal] using congrArg (fun t => ∑ j ∈ t, a j) he
    exact hA.ne' this
  have hcard : (0 : ℝ) < s.card := by exact_mod_cast hsne.card_pos
  have hsum : costTotal (fun j : s => a j) = A := by
    simpa only [costTotal, Finset.sum_coe_sort, s] using htotal
  have hnorm := costEntropy_normalized (a := fun j : s => a j) (hsum ▸ hA)
  have href := costEntropy_le_reference (a := fun j : s => a j)
    (p := fun _ : s => (s.card : ℝ)⁻¹) (fun j => ha j)
    (fun _ => inv_pos.2 hcard) (by simp [hcard.ne'])
  have hrhs : (∑ j : s, a j * (1 - Real.log (s.card : ℝ)⁻¹)) =
      A * (1 + Real.log s.card) := by
    rw [← Finset.sum_mul, Real.log_inv]
    change costTotal (fun j : s => a j) * _ = _
    rw [hsum]
    ring
  rw [hnorm, hsum, hrhs] at href
  have hE : (∑ j : s, Real.negMulLog (a j / A)) ≤ Real.log s.card := by
    have := (mul_le_mul_iff_right₀ hA).1 href
    linarith
  have hseries : (∑' j : ℕ, Real.negMulLog (a j / A)) =
      ∑ j : s, Real.negMulLog (a j / A) := by
    rw [tsum_eq_sum (s := s) (fun j hj => by
      have hz : a j = 0 := by
        simpa only [s, Set.Finite.mem_toFinset, Function.mem_support, not_not] using hj
      simp [hz])]
    exact (Finset.sum_coe_sort s _).symm
  rw [Set.ncard_eq_toFinset_card _ hs]
  exact ⟨hsne.card_pos, hseries ▸ hE⟩

theorem occupied_band_entropy : OccupiedBandEntropyStatement := by
  classical
  intro μ _ ρ hρ hρ4
  have hρ1 : ρ ≤ 1 := by linarith
  have : IsFiniteMeasure (quantileCore μ ρ) :=
    isFiniteMeasure_of_le μ (quantileCore_le μ ρ)
  have ht := quantileThreshold_properties μ hρ hρ1
  obtain ⟨N, hN, hlog, hzero, hint, htotal⟩ :=
    core_bands (quantileCore μ ρ) ht.1 ht.2.1 (quantileCore_support μ ρ)
  let a : ℕ → ℝ := bandCost (quantileCore μ ρ)
  have hsub : Function.support a ⊆ (Finset.range N : Set ℕ) := by
    intro j hj
    by_contra hn
    exact hj (hzero j (by simpa using hn))
  have hs : (Function.support a).Finite := (Finset.finite_toSet _).subset hsub
  have hsum : (∑ j ∈ hs.toFinset, a j) = coreCost μ ρ := by
    have hrange : (∑ j ∈ hs.toFinset, a j) = ∑ j ∈ Finset.range N, a j := by
      apply Finset.sum_subset
      · intro j hj
        exact hsub (hs.mem_toFinset.1 hj)
      · intro j _ hj
        simpa only [Set.Finite.mem_toFinset, Function.mem_support, not_not] using hj
    rw [hrange, ← Fin.sum_univ_eq_sum_range]
    change costTotal (fun j : Fin N => bandCost (quantileCore μ ρ) j) = coreCost μ ρ
    rw [htotal]
    unfold coreCost inverseSquareCost
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun d => sq_nonneg ((d : ℝ)⁻¹)), ENNReal.toReal_ofReal
      (integral_nonneg fun d : Gap => sq_nonneg ((d : ℝ)⁻¹))]
  have hA := (core_entropy μ ρ hρ hρ4).1
  obtain ⟨hn, hE⟩ := finite_support_entropy (a := a)
    (bandCost_nonneg (quantileCore μ ρ)) hs hA hsum
  have hnN : (Function.support a).ncard ≤ N := by
    simpa using Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  have hnR : (0 : ℝ) < (Function.support a).ncard := by exact_mod_cast hn
  refine ⟨hs, hn, hE, ?_⟩
  exact Real.log_le_log hnR ((by exact_mod_cast hnN :
    ((Function.support a).ncard : ℝ) ≤ N).trans hlog)

end ThresholdHC.PsiSharpness
