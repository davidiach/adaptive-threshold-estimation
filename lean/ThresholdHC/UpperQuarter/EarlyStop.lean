import ThresholdHC.UpperQuarter.VoteChange
import ThresholdHC.UpperSign.EarlyStop

/-! Consecutive classifiers on the tape disagree with probability at most one
quarter plus the early-stop bound of the smaller one, at every level.

If the cap-`2^L` classifier runs to its cap, the cap-`2^(L+1)` classifier agrees
with it unless the majority votes after `n = 2^L` and `2*n` flips differ
(`UpperSign.decision_ne_imp`). With `N₁` and `N₂` the successes of the two
blocks of `n` flips, those votes are `n < 2*N₁` and `n < N₁ + N₂`, and they
differ with probability at most `1/4` (`count_voteChange_le`). This holds for
`L = 0` as well, where the smaller classifier has no early checks. -/
noncomputable section
namespace ThresholdHC.UpperQuarter
open MeasureTheory ProbabilityTheory Finset ThresholdHC.Tier2 ThresholdHC.UpperSign

section Tape
open Real Uniform713

/-- On the tape, consecutive classifiers disagree with probability at most one
quarter plus the early-stop bound of the smaller one. -/
theorem disagree_tape_quarter (L : ℕ) (p : unitInterval) {d : ℝ}
    (hearly : (tapeMeasure p).real {ω | ∃ k < L, Tier2.Model.threshold1 (cap k) (cap L) <
      |dyadicMean observations k ω - 1/2|} ≤ earlyBound L d) :
    (tapeMeasure p).real {ω | Tier2.Model.decision (fun k => dyadicMean observations k ω) (L + 1) ≠
      Tier2.Model.decision (fun k => dyadicMean observations k ω) L} ≤ 1 / 4 + earlyBound L d := by
  set μ := tapeMeasure p
  set n := 2 ^ L with hn
  have hsub : {ω | Tier2.Model.decision (fun k => dyadicMean observations k ω) (L + 1) ≠
      Tier2.Model.decision (fun k => dyadicMean observations k ω) L} ⊆
      {ω | ∃ k < L, Tier2.Model.threshold1 (cap k) (cap L) <
        |dyadicMean observations k ω - 1/2|} ∪
      {ω | (n < 2 * successes 0 n ω ∧ successes 0 n ω + successes n n ω ≤ n) ∨
        (2 * successes 0 n ω ≤ n ∧ n < successes 0 n ω + successes n n ω)} := by
    intro ω hω
    by_cases hno : ∀ k < L, |dyadicMean observations k ω - 1/2| ≤
        Tier2.Model.threshold1 (cap k) (cap L)
    · right
      have hs := decision_ne_imp (fun k => dyadicMean observations k ω) L hno hω
      simp only [Set.mem_ofPred_eq]
      have hnr : (2 : ℝ) ^ L = (n : ℝ) := by rw [hn]; push_cast; ring
      have hn0 : (0 : ℝ) < n := by rw [← hnr]; positivity
      have hpow : (2 : ℝ) ^ (L + 1) = 2 * n := by rw [pow_succ, hnr]; ring
      rw [dyadicMean_eq, dyadicMean_succ_eq, hpow] at hs
      rw [hnr] at hs
      rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left
        rw [lt_div_iff₀ hn0] at h1
        rw [lt_div_iff₀ (by positivity)] at h2
        have ha : n < 2 * successes 0 n ω := by
          have : (n : ℝ) < 2 * successes 0 n ω := by linarith
          exact_mod_cast this
        have hb : successes 0 n ω + successes n n ω ≤ n := by
          have : (successes 0 n ω : ℝ) + successes n n ω ≤ n := by
            push Not at h2
            linarith
          exact_mod_cast this
        exact ⟨ha, hb⟩
      · right
        rw [lt_div_iff₀ hn0] at h1
        rw [lt_div_iff₀ (by positivity)] at h2
        have ha : 2 * successes 0 n ω ≤ n := by
          have : 2 * (successes 0 n ω : ℝ) ≤ n := by push Not at h1; linarith
          exact_mod_cast this
        have hb : n < successes 0 n ω + successes n n ω := by
          have : (n : ℝ) < successes 0 n ω + successes n n ω := by linarith
          exact_mod_cast this
        exact ⟨ha, hb⟩
    · left
      push Not at hno
      exact hno
  calc
    _ ≤ μ.real ({ω | ∃ k < L, Tier2.Model.threshold1 (cap k) (cap L) <
          |dyadicMean observations k ω - 1/2|} ∪
        {ω | (n < 2 * successes 0 n ω ∧ successes 0 n ω + successes n n ω ≤ n) ∨
          (2 * successes 0 n ω ≤ n ∧ n < successes 0 n ω + successes n n ω)}) :=
      measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ earlyBound L d + 1 / 4 := add_le_add hearly (count_voteChange_le n p)
    _ = _ := by ring

end Tape

end ThresholdHC.UpperQuarter
