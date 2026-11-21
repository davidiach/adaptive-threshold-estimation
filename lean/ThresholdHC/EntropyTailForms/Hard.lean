import ThresholdHC.EntropyTailForms.Pieces
import ThresholdHC.BandwiseSuffix.Full

/-! Hard assignments in form (62). A hard core `σ = μ|S` together with the
cheapest split of its remainder gives a measurable partition `S, T, Z` of the
gaps, with `T` the magnitudes `d ≥ h` and `Z` the magnitudes `d < h` outside
`S`. Lemma 13.1 for form (61) then transfers to form (62), and the finite
attainment theorem of the bandwise-suffix group gives a hard minimizer of (62)
for a finite atomic law. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.EntropyTailForms
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTail

/-- A measurable partition `S, T, Z` of the gaps decomposes every measure. -/
theorem partition_restrict_sum (μ : Measure Gap) {S T Z : Set Gap}
    (hT : MeasurableSet T) (hZ : MeasurableSet Z) (hST : Disjoint S T) (hSZ : Disjoint S Z)
    (hTZ : Disjoint T Z) (hU : S ∪ T ∪ Z = Set.univ) :
    μ.restrict S + μ.restrict T + μ.restrict Z = μ := by
  rw [← Measure.restrict_union hST hT, ← Measure.restrict_union (Disjoint.union_left hSZ hTZ) hZ,
    hU, Measure.restrict_univ]

/-- A hard core `μ|S` and the cheapest split of its remainder form a hard partition. -/
theorem hard_split (μ : Measure Gap) [IsFiniteMeasure μ] {S : Set Gap} (hS : MeasurableSet S)
    (ρ B : ℝ) :
    MeasurableSet ({d : Gap | 1 / Real.sqrt B ≤ (d : ℝ)} ∩ Sᶜ) ∧
      MeasurableSet ({d : Gap | (d : ℝ) < 1 / Real.sqrt B} ∩ Sᶜ) ∧
      Disjoint S ({d : Gap | 1 / Real.sqrt B ≤ (d : ℝ)} ∩ Sᶜ) ∧
      Disjoint S ({d : Gap | (d : ℝ) < 1 / Real.sqrt B} ∩ Sᶜ) ∧
      Disjoint ({d : Gap | 1 / Real.sqrt B ≤ (d : ℝ)} ∩ Sᶜ)
        ({d : Gap | (d : ℝ) < 1 / Real.sqrt B} ∩ Sᶜ) ∧
      S ∪ ({d : Gap | 1 / Real.sqrt B ≤ (d : ℝ)} ∩ Sᶜ) ∪
          ({d : Gap | (d : ℝ) < 1 / Real.sqrt B} ∩ Sᶜ) = Set.univ ∧
      threePieceObjective ρ B (μ.restrict S)
          (μ.restrict ({d : Gap | 1 / Real.sqrt B ≤ (d : ℝ)} ∩ Sᶜ))
          (μ.restrict ({d : Gap | (d : ℝ) < 1 / Real.sqrt B} ∩ Sᶜ)) =
        selectionObjective μ ρ B (μ.restrict S) := by
  set h := 1 / Real.sqrt B
  have hres : μ - μ.restrict S = μ.restrict Sᶜ := by
    conv_lhs => lhs; rw [← Measure.restrict_compl_add_restrict hS (μ := μ)]
    exact Measure.add_sub_cancel
  refine ⟨(measurableSet_ge_gap h).inter hS.compl, (measurableSet_lt_gap h).inter hS.compl,
    Set.disjoint_left.2 fun x hx hx' => hx'.2 hx, Set.disjoint_left.2 fun x hx hx' => hx'.2 hx,
    Set.disjoint_left.2 fun x hx hx' => ?_, ?_, ?_⟩
  · have h1 : h ≤ (x : ℝ) := hx.1
    have h2 : (x : ℝ) < h := hx'.1
    exact (not_lt_of_ge h1) h2
  · ext x
    by_cases hxS : x ∈ S
    · simp [hxS]
    · by_cases hx : h ≤ (x : ℝ)
      · simp [hxS, hx]
      · simp [hxS, hx, lt_of_not_ge hx]
  · obtain ⟨-, heq⟩ := threePiece_attained (Measure.restrict_le_self (s := S) (μ := μ)) ρ B
    rw [hres, Measure.restrict_restrict (measurableSet_ge_gap h),
      Measure.restrict_restrict (measurableSet_lt_gap h)] at heq
    exact heq

/-- Hard measurable assignments suffice in form (62). -/
theorem iInf_threePiece_eq_hard : HardThreePieceStatement := by
  intro ρ B hρ hρ4 hB μ _
  refine le_antisymm ?_ ?_
  · refine le_iInf fun S => le_iInf fun T => le_iInf fun Z => le_iInf fun hP => ?_
    obtain ⟨-, hT, hZ, hST, hSZ, hTZ, hU⟩ := hP
    exact iInf_le_of_le _ (iInf_le_of_le _ (iInf_le_of_le _
      (iInf_le_of_le (partition_restrict_sum μ hT hZ hST hSZ hTZ hU) le_rfl)))
  · rw [← iInf_selection_eq_threePiece μ ρ B, hard_selection ρ B hρ hρ4 hB μ]
    refine le_iInf₂ fun S hS => ?_
    obtain ⟨hT, hZ, hST, hSZ, hTZ, hU, heq⟩ := hard_split μ hS ρ B
    rw [← heq]
    exact iInf_le_of_le S (iInf_le_of_le _ (iInf_le_of_le _
      (iInf_le_of_le ⟨hS, hT, hZ, hST, hSZ, hTZ, hU⟩ le_rfl)))

/-- Lemma 13.1, second sentence, in form (62). -/
theorem finite_hard_minimizer : FiniteHardThreePieceStatement := by
  intro μ _ hF ρ B hρ hρ4 hB
  obtain ⟨S, -, -, hmin, hcap⟩ := BandwiseSuffix.bandwise_suffix μ hF hρ hρ4 hB
  obtain ⟨hT, hZ, hST, hSZ, hTZ, hU, heq⟩ := hard_split μ S.measurableSet ρ B
  refine ⟨S, _, _, S.measurableSet, hT, hZ, hST, hSZ, hTZ, hU,
    partition_restrict_sum μ hT hZ hST hSZ hTZ hU, ?_, ?_⟩
  · intro σ τ ζ hsum
    rw [heq]
    exact (hmin σ (core_le_of_add hsum).1).trans (selectionObjective_le_threePiece hsum ρ B)
  · rw [← selection_eq_threePieceSelection μ ρ B, heq, hcap]

end ThresholdHC.EntropyTailForms
