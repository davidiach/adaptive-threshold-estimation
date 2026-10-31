import ThresholdHC.StoppingProgram.PrefixInformation

/-! Extending a stopped count flow to a larger cap adds zero states and
preserves the full flow cone, information, and every prior mean. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.Genie
open ThresholdHC.Tier6 (Gap SignLaw)
open ThresholdHC.StoppingProgram

def extendArray {N : ℕ} (M : ℕ) (u : CountState N → ℝ) : CountState M → ℝ :=
  fun s => arrayAt u s.1.val s.2.val

theorem arrayAt_extendArray {N M : ℕ} (hNM : N ≤ M) (u : CountState N → ℝ) (n k : ℕ) :
    arrayAt (extendArray M u) n k = arrayAt u n k := by
  by_cases hn : n ≤ N
  · have hnM : n ≤ M := hn.trans hNM
    by_cases hk : k ≤ n <;> simp [arrayAt,extendArray,hn,hnM,hk]
  · by_cases hnM : n ≤ M <;> by_cases hk : k ≤ n <;> simp [arrayAt,extendArray,hn,hnM,hk]

theorem arrayAt_nonneg {N : ℕ} (u : CountState N → ℝ) (hu : ∀ s, 0 ≤ u s) (n k : ℕ) :
    0 ≤ arrayAt u n k := by
  unfold arrayAt
  split_ifs <;> first | exact hu _ | exact le_rfl

theorem continue_arrayAt_ge_cap {N : ℕ} (f : Flow N) (hf : FlowCone f)
    (n k : ℕ) (hn : N ≤ n) : arrayAt f.continueWeight n k = 0 := by
  by_cases he : n = N
  · subst n
    by_cases hk : k ≤ N
    · let s : CountState N := ⟨⟨N,by omega⟩,⟨k,by change k < N+1; omega⟩⟩
      rw [show arrayAt f.continueWeight N k = f.continueWeight s from arrayAt_state _ s]
      exact hf.terminal s rfl
    · simp [arrayAt,hk]
  · simp [arrayAt,show ¬n ≤ N by omega]

def extendFlow {N : ℕ} (M : ℕ) (f : Flow N) : Flow M :=
  ⟨extendArray M f.stopWeight,extendArray M f.continueWeight,
    extendArray M f.outputWeight,extendArray M f.momentWeight⟩

theorem extendFlow_intensity {N M : ℕ} (f : Flow N) : intensity (extendFlow M f) = intensity f := by
  simp [intensity,extendFlow,extendArray,rootState,arrayAt]

theorem extendFlow_cone {N M : ℕ} (hNM : N ≤ M) (f : Flow N) (hf : FlowCone f) :
    FlowCone (extendFlow M f) := by
  constructor
  · intro s
    exact arrayAt_nonneg _ hf.stop_nonneg _ _
  · intro s
    exact arrayAt_nonneg _ hf.continue_nonneg _ _
  · intro s
    exact arrayAt_nonneg _ hf.moment_nonneg _ _
  · simpa [extendFlow,extendArray,rootState,arrayAt] using hf.root_stop
  · simpa [extendFlow,extendArray,rootState,arrayAt] using hf.root_output
  · simpa [extendFlow,extendArray,rootState,arrayAt] using hf.root_moment
  · intro s hs
    exact continue_arrayAt_ge_cap f hf _ _ (by omega)
  · intro s hs
    change arrayAt f.stopWeight s.1.val s.2.val+arrayAt f.continueWeight s.1.val s.2.val =
      ((s.1.val-s.2.val:ℕ):ℝ)/s.1.val*arrayAt (extendArray M f.continueWeight) (s.1.val-1) s.2.val+
      (s.2.val:ℝ)/s.1.val*arrayAt (extendArray M f.continueWeight) (s.1.val-1) (s.2.val-1)
    rw [arrayAt_extendArray hNM,arrayAt_extendArray hNM]
    by_cases hn : s.1.val ≤ N
    · let t : CountState N := ⟨⟨s.1.val,by omega⟩,s.2⟩
      rw [show arrayAt f.stopWeight s.1.val s.2.val = f.stopWeight t from arrayAt_state _ t,
        show arrayAt f.continueWeight s.1.val s.2.val = f.continueWeight t from arrayAt_state _ t]
      exact hf.recursion t hs
    · have hprev : N ≤ s.1.val-1 := by omega
      rw [continue_arrayAt_ge_cap f hf _ _ hprev,continue_arrayAt_ge_cap f hf _ _ hprev]
      simp [arrayAt,hn]
  · intro s
    change (arrayAt f.outputWeight s.1.val s.2.val)^2 ≤
      arrayAt f.stopWeight s.1.val s.2.val*arrayAt f.momentWeight s.1.val s.2.val
    by_cases hn : s.1.val ≤ N
    · let t : CountState N := ⟨⟨s.1.val,by omega⟩,s.2⟩
      rw [show arrayAt f.outputWeight s.1.val s.2.val = f.outputWeight t from arrayAt_state _ t,
        show arrayAt f.stopWeight s.1.val s.2.val = f.stopWeight t from arrayAt_state _ t,
        show arrayAt f.momentWeight s.1.val s.2.val = f.momentWeight t from arrayAt_state _ t]
      exact hf.perspective t
    · simp [arrayAt,hn]

theorem rawLayer_extendArray {N M : ℕ} (hNM : N ≤ M) (u : CountState N → ℝ)
    (v : ℕ → ℕ → ℝ) (n : ℕ) : rawLayer (extendArray M u) v n = rawLayer u v n := by
  simp only [rawLayer,rawArray,arrayAt_extendArray hNM]

theorem rawLayer_above_cap {N : ℕ} (u : CountState N → ℝ) (v : ℕ → ℕ → ℝ)
    (n : ℕ) (hn : N < n) : rawLayer u v n = 0 := by
  simp [rawLayer,rawArray,arrayAt,not_le.mpr hn]

theorem countMean_extendArray {N M : ℕ} (hNM : N ≤ M) (μ : Measure Gap) (q : SignLaw)
    (u : CountState N → ℝ) : countMean μ q (extendArray M u) = countMean μ q u := by
  rw [← rawLayer_countMean μ q (extendArray M u),← rawLayer_countMean μ q u]
  simp_rw [rawLayer_extendArray hNM]
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro n hn hnN
  exact rawLayer_above_cap u _ n (by simp only [Finset.mem_range] at hnN; omega)

end ThresholdHC.Genie
