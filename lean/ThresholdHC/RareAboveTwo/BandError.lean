import ThresholdHC.RareAboveTwo.BandModel
import ThresholdHC.CriticalUpper.ScreenError

/-! Wrong-decision bounds from the finite dyadic crossing decomposition. -/

noncomputable section
namespace ThresholdHC.RareAboveTwo
open MeasureTheory Set ThresholdHC.CriticalEntropy ThresholdHC.Uniform713
open scoped ENNReal

theorem band_early_error (e : ℕ) (A : ℕ → ℝ) (d : ℝ)
    (hA : ∀ k, 0 ≤ A k) (hd : 0 ≤ d) (k : ℕ) :
    Real.exp (-2*cap (e+k)*(d+bandBoundary e A k)^2) ≤ Real.exp (-A k) :=
  CriticalUpper.screen_early_error (A k) d (hA k) hd (e+k)

section ScreenProbability
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {m : ℕ → Ω → ℝ}

theorem band_error_positive (e : ℕ) (A₀ A₁ : ℕ → ℝ) (hA₀ : ∀ k, 0 ≤ A₀ k) (L : ℕ)
    {d : ℝ} (hd : 0 < d) (ht : HasMeanTails μ m (1/2+d)) :
    μ.real {ω | bandDecision e A₀ A₁ (fun k => m (e+k) ω) L ≠ 1} ≤
      Real.exp (-2*cap (e+L)*d^2)+∑ k ∈ Finset.range L, Real.exp (-A₀ k) := by
  have hsub : {ω | bandDecision e A₀ A₁ (fun k => m (e+k) ω) L ≠ 1} ⊆
      {ω | d ≤ (1/2+d)-m (e+L) ω} ∪
      ⋃ k ∈ Finset.range L, {ω | d+bandBoundary e A₀ k ≤ (1/2+d)-m (e+k) ω} := by
    intro ω hω
    rcases band_wrong_positive e A₀ A₁ (fun k => m (e+k) ω) L d hω with ⟨_,h⟩ | ⟨hs,h⟩
    · exact Or.inl h
    · exact Or.inr (mem_iUnion.mpr ⟨_,mem_iUnion.mpr ⟨Finset.mem_range.mpr hs,h⟩⟩)
  calc
    _ ≤ μ.real ({ω | d ≤ (1/2+d)-m (e+L) ω} ∪
      ⋃ k ∈ Finset.range L, {ω | d+bandBoundary e A₀ k ≤ (1/2+d)-m (e+k) ω}) := measureReal_mono hsub
    _ ≤ μ.real {ω | d ≤ (1/2+d)-m (e+L) ω} +
      ∑ k ∈ Finset.range L, μ.real {ω | d+bandBoundary e A₀ k ≤ (1/2+d)-m (e+k) ω} :=
      (measureReal_union_le _ _).trans
        (add_le_add_right (measureReal_biUnion_finset_le _ _) _)
    _ ≤ Real.exp (-2*cap (e+L)*d^2)+∑ k ∈ Finset.range L, Real.exp (-A₀ k) := by
      apply add_le_add (ht.lower (e+L) d hd.le)
      apply Finset.sum_le_sum
      intro k _
      exact (ht.lower (e+k) _ (add_nonneg hd.le (bandBoundary_nonneg e A₀ k))).trans
        (band_early_error e A₀ d hA₀ hd.le k)


theorem band_error_negative (e : ℕ) (A₀ A₁ : ℕ → ℝ) (hA₁ : ∀ k, 0 ≤ A₁ k) (L : ℕ)
    {d : ℝ} (hd : 0 < d) (ht : HasMeanTails μ m (1/2-d)) :
    μ.real {ω | bandDecision e A₀ A₁ (fun k => m (e+k) ω) L ≠ 0} ≤
      Real.exp (-2*cap (e+L)*d^2)+∑ k ∈ Finset.range L, Real.exp (-A₁ k) := by
  have hsub : {ω | bandDecision e A₀ A₁ (fun k => m (e+k) ω) L ≠ 0} ⊆
      {ω | d ≤ m (e+L) ω-(1/2-d)} ∪
      ⋃ k ∈ Finset.range L, {ω | d+bandBoundary e A₁ k ≤ m (e+k) ω-(1/2-d)} := by
    intro ω hω
    rcases band_wrong_negative e A₀ A₁ (fun k => m (e+k) ω) L d hω with ⟨_,h⟩ | ⟨hs,h⟩
    · exact Or.inl h
    · exact Or.inr (mem_iUnion.mpr ⟨_,mem_iUnion.mpr ⟨Finset.mem_range.mpr hs,h⟩⟩)
  calc
    _ ≤ μ.real ({ω | d ≤ m (e+L) ω-(1/2-d)} ∪
      ⋃ k ∈ Finset.range L, {ω | d+bandBoundary e A₁ k ≤ m (e+k) ω-(1/2-d)}) := measureReal_mono hsub
    _ ≤ μ.real {ω | d ≤ m (e+L) ω-(1/2-d)} +
      ∑ k ∈ Finset.range L, μ.real {ω | d+bandBoundary e A₁ k ≤ m (e+k) ω-(1/2-d)} :=
      (measureReal_union_le _ _).trans
        (add_le_add_right (measureReal_biUnion_finset_le _ _) _)
    _ ≤ Real.exp (-2*cap (e+L)*d^2)+∑ k ∈ Finset.range L, Real.exp (-A₁ k) := by
      apply add_le_add (ht.upper (e+L) d hd.le)
      apply Finset.sum_le_sum
      intro k _
      exact (ht.upper (e+k) _ (add_nonneg hd.le (bandBoundary_nonneg e A₁ k))).trans
        (band_early_error e A₁ d hA₁ hd.le k)


end ScreenProbability

end ThresholdHC.RareAboveTwo
