import Mathlib

/-! A decreasing sequence of upper-semicontinuous functions on one compact
space admits a common limiting maximizer. -/

noncomputable section
open Set
open scoped ENNReal
namespace ThresholdHC.Genie

theorem compact_decreasing_maximum {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [Nonempty X] (f : ℕ → X → ℝ≥0∞)
    (hf : ∀ n, UpperSemicontinuous (f n)) (hmono : ∀ x, Antitone (fun n => f n x)) :
    ∃ x : X, (⨅ n : ℕ, ⨆ y : X, f n y) = ⨅ n : ℕ, f n x := by
  let M : ℝ≥0∞ := ⨅ n : ℕ, ⨆ y : X, f n y
  let S (n : ℕ) : Set X := (f n) ⁻¹' Ici M
  have hclosed (n : ℕ) : IsClosed (S n) := (hf n).isClosed_preimage M
  have hnonempty (n : ℕ) : (S n).Nonempty := by
    obtain ⟨x,hx,hmax⟩ := UpperSemicontinuousOn.exists_isMaxOn
      (s := (univ : Set X)) Set.univ_nonempty isCompact_univ ((hf n).upperSemicontinuousOn univ)
    refine ⟨x,?_⟩
    exact (iInf_le (fun m : ℕ => ⨆ y : X, f m y) n).trans
      (iSup_le (fun y => hmax (Set.mem_univ y)))
  have hdecreasing (n : ℕ) : S (n+1) ⊆ S n := by
    intro x hx
    exact hx.trans (hmono x (by omega))
  obtain ⟨x,hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    S hdecreasing hnonempty (hclosed 0).isCompact hclosed
  refine ⟨x,le_antisymm ?_ ?_⟩
  · apply le_iInf
    intro n
    exact Set.mem_iInter.mp hx n
  · exact iInf_mono (fun n => le_iSup (f n) x)

end ThresholdHC.Genie
