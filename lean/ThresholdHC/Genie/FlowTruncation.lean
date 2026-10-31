import ThresholdHC.Genie.ExtendedFlowConservation

/-! Stop every surviving path at a smaller positive cap. Paid work can
only decrease; the terminal weight records all arrivals at the new cap. -/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace ThresholdHC.Genie
open ThresholdHC.Tier6 ThresholdHC.StoppingProgram

def truncateFlow {M : ℕ} (N : ℕ) (f : Flow M) : Flow N where
  stopWeight := fun s => arrayAt f.stopWeight s.1.val s.2.val+
    if s.1.val = N then arrayAt f.continueWeight s.1.val s.2.val else 0
  continueWeight := fun s => if s.1.val < N then arrayAt f.continueWeight s.1.val s.2.val else 0
  outputWeight := fun _ => 0
  momentWeight := fun _ => 0

theorem arrayAt_truncate_continue {M : ℕ} (N : ℕ) (f : Flow M) (n k : ℕ) :
    arrayAt (truncateFlow N f).continueWeight n k = if n < N then arrayAt f.continueWeight n k else 0 := by
  by_cases hn : n < N
  · by_cases hk : k ≤ n <;> simp [arrayAt,truncateFlow,hn,show n ≤ N by omega,hk]
  · by_cases hnN : n ≤ N <;> by_cases hk : k ≤ n <;> simp [arrayAt,truncateFlow,hn,hnN,hk]

theorem arrayAt_truncate_stop {M : ℕ} (N : ℕ) (f : Flow M) (n k : ℕ) (hn : n ≤ N) :
    arrayAt (truncateFlow N f).stopWeight n k = arrayAt f.stopWeight n k+
      if n = N then arrayAt f.continueWeight n k else 0 := by
  by_cases hk : k ≤ n <;> simp [arrayAt,truncateFlow,hn,hk]

theorem truncateFlow_intensity {M : ℕ} (N : ℕ) (hN : 0 < N) (f : Flow M) :
    intensity (truncateFlow N f) = intensity f := by
  simp [intensity,truncateFlow,rootState,arrayAt,hN]

theorem truncateFlow_cone {M N : ℕ} (hN : 0 < N) (hNM : N ≤ M) (f : Flow M)
    (hf : FlowCone f) : FlowCone (truncateFlow N f) := by
  constructor
  · intro s
    change 0 ≤ arrayAt f.stopWeight s.1.val s.2.val+_
    apply add_nonneg (arrayAt_nonneg _ hf.stop_nonneg _ _)
    split_ifs <;> first | exact arrayAt_nonneg _ hf.continue_nonneg _ _ | exact le_rfl
  · intro s
    change 0 ≤ if s.1.val < N then _ else 0
    split_ifs <;> first | exact arrayAt_nonneg _ hf.continue_nonneg _ _ | exact le_rfl
  · intro s; exact le_rfl
  · simpa [truncateFlow,rootState,arrayAt,hN.ne',Ne.symm hN.ne'] using hf.root_stop
  · rfl
  · rfl
  · intro s hs
    simp [truncateFlow,hs]
  · intro s hs
    have hsN : s.1.val ≤ N := by have h := s.1.isLt; omega
    have hprev : s.1.val-1 < N := by omega
    change (arrayAt f.stopWeight s.1.val s.2.val+_)+_ = _
    rw [arrayAt_truncate_continue,arrayAt_truncate_continue,ite_eq_left hprev,ite_eq_left hprev]
    have he : (arrayAt f.stopWeight s.1.val s.2.val+
        if s.1.val = N then arrayAt f.continueWeight s.1.val s.2.val else 0)+
        (if s.1.val < N then arrayAt f.continueWeight s.1.val s.2.val else 0) =
        arrayAt f.stopWeight s.1.val s.2.val+arrayAt f.continueWeight s.1.val s.2.val := by
      by_cases hn : s.1.val = N
      · simp [hn]
      · simp [hn,show s.1.val < N by omega]
    dsimp only [truncateFlow]
    rw [he]
    let t : CountState M := ⟨⟨s.1.val,by omega⟩,s.2⟩
    rw [show arrayAt f.stopWeight s.1.val s.2.val = f.stopWeight t from arrayAt_state _ t,
      show arrayAt f.continueWeight s.1.val s.2.val = f.continueWeight t from arrayAt_state _ t]
    exact hf.recursion t hs
  · intro s
    simp [truncateFlow]

theorem raw_truncate_continue_le {M : ℕ} (N : ℕ) (f : Flow M) (hf : FlowCone f) (n k : ℕ) :
    rawArray (truncateFlow N f).continueWeight n k ≤ rawArray f.continueWeight n k := by
  unfold rawArray
  rw [arrayAt_truncate_continue]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  split_ifs
  · exact le_rfl
  · exact arrayAt_nonneg _ hf.continue_nonneg _ _

theorem truncateFlow_work_le {M N : ℕ} (hNM : N ≤ M) (μ : Measure Gap) (q : SignLaw)
    (f : Flow M) (hf : FlowCone f) :
    countMean μ q (truncateFlow N f).continueWeight ≤ countMean μ q f.continueWeight := by
  rw [←rawLayer_countMean,←rawLayer_countMean]
  calc
    _ ≤ ∑ n ∈ Finset.range (N+1), rawLayer f.continueWeight (prefixCoefficient μ q) n := by
      apply Finset.sum_le_sum
      intro n _
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_right (raw_truncate_continue_le N f hf n k) (prefixCoefficient_nonneg μ q n k)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      (fun n _ _ => Finset.sum_nonneg (fun k _ =>
        mul_nonneg (rawArray_nonneg _ hf.continue_nonneg _ _) (prefixCoefficient_nonneg μ q _ _)))

theorem raw_truncate_stop {M : ℕ} (N : ℕ) (f : Flow M) (n k : ℕ) (hn : n ≤ N) :
    rawArray (truncateFlow N f).stopWeight n k = rawArray f.stopWeight n k+
      if n = N then rawArray f.continueWeight n k else 0 := by
  unfold rawArray
  rw [arrayAt_truncate_stop N f n k hn,mul_add]
  split_ifs <;> simp

theorem eRaw_truncate_stop_before {M : ℕ} (N : ℕ) (f : Flow M)
    (v : ℕ → ℕ → ℝ≥0∞) (n : ℕ) (hn : n < N) :
    eRawLayer (truncateFlow N f).stopWeight v n = eRawLayer f.stopWeight v n := by
  unfold eRawLayer
  simp only [raw_truncate_stop N f n _ hn.le,show n ≠ N by omega,ite_false,add_zero]

theorem eRaw_truncate_stop_terminal {M : ℕ} (N : ℕ) (f : Flow M) (hf : FlowCone f)
    (v : ℕ → ℕ → ℝ≥0∞) :
    eRawLayer (truncateFlow N f).stopWeight v N =
      eRawLayer f.stopWeight v N+eRawLayer f.continueWeight v N := by
  unfold eRawLayer
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [raw_truncate_stop N f N k le_rfl,ite_eq_left rfl,
    ENNReal.ofReal_add (rawArray_nonneg _ hf.stop_nonneg _ _) (rawArray_nonneg _ hf.continue_nonneg _ _),add_mul]

end ThresholdHC.Genie
