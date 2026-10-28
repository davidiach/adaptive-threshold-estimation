import ThresholdHC.CriticalUpper.ScreenModel

/-! Wrong-decision bounds from the finite dyadic crossing decomposition. -/

noncomputable section
namespace ThresholdHC.CriticalUpper
open MeasureTheory Set ThresholdHC.CriticalEntropy ThresholdHC.Uniform713
open scoped ENNReal

theorem screen_early_error (A d : ℝ) (hA : 0 ≤ A) (hd : 0 ≤ d) (k : ℕ) :
    Real.exp (-2*cap k*(d+screenBoundary A k)^2) ≤ Real.exp (-A) := by
  have hb := screenBoundary_nonneg A k
  have hs : 2*cap k*(screenBoundary A k)^2 = A := by
    rw [screenBoundary_sq A hA k]
    field_simp [(cap_pos k).ne']
  apply Real.exp_le_exp.mpr
  have hm := mul_le_mul_of_nonneg_left
    (show (screenBoundary A k)^2 ≤ (d+screenBoundary A k)^2 by nlinarith) (cap_pos k).le
  nlinarith

section ScreenProbability
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {m : ℕ → Ω → ℝ}

theorem screen_error_positive (A₀ A₁ : ℝ) (hA₀ : 0 ≤ A₀) (L : ℕ)
    {d : ℝ} (hd : 0 < d) (ht : HasMeanTails μ m (1/2+d)) :
    μ.real {ω | screenDecision A₀ A₁ (fun k => m k ω) L ≠ 1} ≤
      Real.exp (-2*cap L*d^2)+(L : ℝ)*Real.exp (-A₀) := by
  have hsub : {ω | screenDecision A₀ A₁ (fun k => m k ω) L ≠ 1} ⊆
      {ω | d ≤ (1/2+d)-m L ω} ∪
      ⋃ k ∈ Finset.range L, {ω | d+screenBoundary A₀ k ≤ (1/2+d)-m k ω} := by
    intro ω hω
    rcases screen_wrong_positive A₀ A₁ (fun k => m k ω) L d hω with ⟨_,h⟩ | ⟨hs,h⟩
    · exact Or.inl h
    · exact Or.inr (mem_iUnion.mpr ⟨_,mem_iUnion.mpr ⟨Finset.mem_range.mpr hs,h⟩⟩)
  calc
    _ ≤ μ.real ({ω | d ≤ (1/2+d)-m L ω} ∪
      ⋃ k ∈ Finset.range L, {ω | d+screenBoundary A₀ k ≤ (1/2+d)-m k ω}) := measureReal_mono hsub
    _ ≤ μ.real {ω | d ≤ (1/2+d)-m L ω} +
      ∑ k ∈ Finset.range L, μ.real {ω | d+screenBoundary A₀ k ≤ (1/2+d)-m k ω} :=
      (measureReal_union_le _ _).trans
        (add_le_add_right (measureReal_biUnion_finset_le _ _) _)
    _ ≤ Real.exp (-2*cap L*d^2)+∑ _k ∈ Finset.range L, Real.exp (-A₀) := by
      apply add_le_add (ht.lower L d hd.le)
      apply Finset.sum_le_sum
      intro k _
      exact (ht.lower k _ (add_nonneg hd.le (screenBoundary_nonneg A₀ k))).trans
        (screen_early_error A₀ d hA₀ hd.le k)
    _ = _ := by simp

theorem screen_error_negative (A₀ A₁ : ℝ) (hA₁ : 0 ≤ A₁) (L : ℕ)
    {d : ℝ} (hd : 0 < d) (ht : HasMeanTails μ m (1/2-d)) :
    μ.real {ω | screenDecision A₀ A₁ (fun k => m k ω) L ≠ 0} ≤
      Real.exp (-2*cap L*d^2)+(L : ℝ)*Real.exp (-A₁) := by
  have hsub : {ω | screenDecision A₀ A₁ (fun k => m k ω) L ≠ 0} ⊆
      {ω | d ≤ m L ω-(1/2-d)} ∪
      ⋃ k ∈ Finset.range L, {ω | d+screenBoundary A₁ k ≤ m k ω-(1/2-d)} := by
    intro ω hω
    rcases screen_wrong_negative A₀ A₁ (fun k => m k ω) L d hω with ⟨_,h⟩ | ⟨hs,h⟩
    · exact Or.inl h
    · exact Or.inr (mem_iUnion.mpr ⟨_,mem_iUnion.mpr ⟨Finset.mem_range.mpr hs,h⟩⟩)
  calc
    _ ≤ μ.real ({ω | d ≤ m L ω-(1/2-d)} ∪
      ⋃ k ∈ Finset.range L, {ω | d+screenBoundary A₁ k ≤ m k ω-(1/2-d)}) := measureReal_mono hsub
    _ ≤ μ.real {ω | d ≤ m L ω-(1/2-d)} +
      ∑ k ∈ Finset.range L, μ.real {ω | d+screenBoundary A₁ k ≤ m k ω-(1/2-d)} :=
      (measureReal_union_le _ _).trans
        (add_le_add_right (measureReal_biUnion_finset_le _ _) _)
    _ ≤ Real.exp (-2*cap L*d^2)+∑ _k ∈ Finset.range L, Real.exp (-A₁) := by
      apply add_le_add (ht.upper L d hd.le)
      apply Finset.sum_le_sum
      intro k _
      exact (ht.upper k _ (add_nonneg hd.le (screenBoundary_nonneg A₁ k))).trans
        (screen_early_error A₁ d hA₁ hd.le k)
    _ = _ := by simp

end ScreenProbability

end ThresholdHC.CriticalUpper
