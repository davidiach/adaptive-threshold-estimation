import ThresholdHC.Genie.FlowTruncation
import ThresholdHC.StoppingProgram.FlowCostMoment

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ThresholdHC.FiniteCapTruncation
open ThresholdHC.Tier6 ThresholdHC.StoppingProgram ThresholdHC.Genie

/-- Keep the old outputs at every retained stopping state. Newly forced stops
at the cap have zero output and contribute no additional second moment. -/
def capFlow {M : ℕ} (N : ℕ) (f : Flow M) : Flow N :=
  { truncateFlow N f with
    outputWeight := fun s => arrayAt f.outputWeight s.1.val s.2.val
    momentWeight := fun s => arrayAt f.momentWeight s.1.val s.2.val }

theorem capFlow_cone {M N : ℕ} (hN : 0 < N) (hNM : N ≤ M)
    (f : Flow M) (hf : FlowCone f) : FlowCone (capFlow N f) := by
  have ht := truncateFlow_cone hN hNM f hf
  refine ⟨ht.stop_nonneg, ht.continue_nonneg, ?_, ht.root_stop, ?_, ?_,
    ht.terminal, ht.recursion, ?_⟩
  · intro s
    exact arrayAt_nonneg _ hf.moment_nonneg _ _
  · simpa [capFlow, rootState, arrayAt] using hf.root_output
  · simpa [capFlow, rootState, arrayAt] using hf.root_moment
  · intro s
    have hs : s.1.val ≤ M := (Nat.le_of_lt_succ s.1.isLt).trans hNM
    let t : CountState M := ⟨⟨s.1.val, Nat.lt_succ_of_le hs⟩, s.2⟩
    have hstop : f.stopWeight t ≤ (truncateFlow N f).stopWeight s := by
      change f.stopWeight t ≤ arrayAt f.stopWeight s.1.val s.2.val + _
      rw [show arrayAt f.stopWeight s.1.val s.2.val = f.stopWeight t from arrayAt_state _ t]
      apply le_add_of_nonneg_right
      split_ifs
      · exact arrayAt_nonneg _ hf.continue_nonneg _ _
      · exact le_refl _
    change (arrayAt f.outputWeight s.1.val s.2.val)^2 ≤
      (truncateFlow N f).stopWeight s * arrayAt f.momentWeight s.1.val s.2.val
    rw [show arrayAt f.outputWeight s.1.val s.2.val = f.outputWeight t from arrayAt_state _ t,
      show arrayAt f.momentWeight s.1.val s.2.val = f.momentWeight t from arrayAt_state _ t]
    exact (hf.perspective t).trans (mul_le_mul_of_nonneg_right hstop (hf.moment_nonneg t))

theorem capFlow_work_le {M N : ℕ} (hNM : N ≤ M) (μ : Measure Gap)
    (q : SignLaw) (f : Flow M) (hf : FlowCone f) :
    countMean μ q (capFlow N f).continueWeight ≤ countMean μ q f.continueWeight :=
  truncateFlow_work_le hNM μ q f hf

def liftState {M N : ℕ} (hNM : N ≤ M) (s : CountState N) : CountState M :=
  ⟨⟨s.1.val, Nat.lt_succ_of_le ((Nat.le_of_lt_succ s.1.isLt).trans hNM)⟩, s.2⟩

theorem liftState_injective {M N : ℕ} (hNM : N ≤ M) :
    Function.Injective (liftState hNM) := by
  let lower (s : CountState M) : CountState N :=
    if h : s.1.val ≤ N then ⟨⟨s.1.val, Nat.lt_succ_of_le h⟩, s.2⟩ else rootState N
  have hl : Function.LeftInverse lower (liftState hNM) := by
    intro s
    simp [lower, liftState, Nat.le_of_lt_succ s.1.isLt]
  exact hl.injective

/-- Capping keeps exactly the terms at depths at most N in every linear mean. -/
theorem kept_countMean {M N : ℕ} (hNM : N ≤ M) (μ : Measure Gap)
    (q : SignLaw) (u : CountState M → ℝ) :
    countMean μ q (fun s : CountState N => arrayAt u s.1.val s.2.val) =
      ∑ s ∈ (Finset.univ.filter fun s : CountState M => s.1.val ≤ N),
        countCoefficient μ q s * u s := by
  unfold countMean
  apply Finset.sum_bij (fun s _ => liftState hNM s)
  · intro s _
    simp [liftState, Nat.le_of_lt_succ s.1.isLt]
  · intro s _ t _ he
    exact liftState_injective hNM he
  · intro s hs
    have hn := (Finset.mem_filter.mp hs).2
    refine ⟨⟨⟨s.1.val, Nat.lt_succ_of_le hn⟩, s.2⟩, Finset.mem_univ _, ?_⟩
    rfl
  · intro s _
    have he := arrayAt_state u (liftState hNM s)
    change arrayAt u s.1.val s.2.val = u (liftState hNM s) at he
    change countCoefficient μ q s * arrayAt u s.1.val s.2.val = _
    rw [he]
    rfl

end ThresholdHC.FiniteCapTruncation

