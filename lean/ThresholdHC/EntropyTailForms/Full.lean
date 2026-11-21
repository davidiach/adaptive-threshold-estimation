import ThresholdHC.EntropyTailForms.Hard
import ThresholdHC.EntropyTail.Law

/-! The targets of the entropy-tail forms group: the fixed-core split, the
equality of forms (61) and (62) before and after the cap, Theorem 13.2 with
ordered constants `0 < c < C` in both forms, and hard assignments in form (62).
The ordered constants come from `EntropyTail.entropy_tail_law` by shrinking the
lower constant to `min c (C/2)`. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.EntropyTailForms
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTail

/-- At fixed `σ`, each remaining magnitude goes to the cheaper of `1` and `h/d`. -/
theorem fixed_core_split : FixedCoreSplitStatement := iInf_split_eq_tailCost

/-- The infima of (61) and (62) agree for every finite law. -/
theorem three_piece_inf : ThreePieceInfStatement := iInf_selection_eq_threePiece

/-- (61) = (62) with the cap at `ρ`. -/
theorem three_piece_form : ThreePieceFormStatement := selection_eq_threePieceSelection

/-- Theorem 13.2 with universal constants `0 < c < C`. -/
theorem ordered_law : OrderedLawStatement := by
  obtain ⟨c, C, hc, hC, hlaw⟩ := entropy_tail_law
  refine ⟨min c (C / 2), C, lt_min hc (by linarith), (min_le_right _ _).trans_lt (by linarith),
    ?_⟩
  intro ρ B hρ hρ4 hB μ _
  obtain ⟨hl, hu⟩ := hlaw ρ B hρ hρ4 hB μ
  exact ⟨(mul_le_mul' (ENNReal.ofReal_le_ofReal (min_le_left _ _)) le_rfl).trans hl, hu⟩

/-- Theorem 13.2 in the three-piece form (62). -/
theorem three_piece_law : ThreePieceLawStatement := by
  obtain ⟨c, C, hc, hcC, hlaw⟩ := ordered_law
  refine ⟨c, C, hc, hcC, ?_⟩
  intro ρ B hρ hρ4 hB μ _
  rw [← three_piece_form μ ρ B]
  exact hlaw ρ B hρ hρ4 hB μ

/-- Hard measurable assignments suffice in form (62). -/
theorem hard_three_piece : HardThreePieceStatement := iInf_threePiece_eq_hard

/-- Lemma 13.1, second sentence: a finite atomic law has a hard minimizer of (62). -/
theorem finite_hard_three_piece : FiniteHardThreePieceStatement := finite_hard_minimizer

end ThresholdHC.EntropyTailForms
