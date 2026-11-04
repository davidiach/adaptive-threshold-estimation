import ThresholdHC.BandwiseSuffix.Search
open MeasureTheory ThresholdHC.Tier6 ThresholdHC.EntropyTail
open ThresholdHC.BandwiseSuffix
open scoped ENNReal BigOperators
example (μ : Measure Gap) [IsProbabilityMeasure μ] (hs : μ.support.Finite) {ρ B : ℝ} (hρ : 0 < ρ) (hr : ρ ≤ 1/4) (hb : 0 < B) : ∃ S : Finset Gap, (S : Set Gap) ⊆ μ.support ∧ ∀ σ : Measure Gap, σ ≤ μ → selectionObjective μ ρ B (μ.restrict S) ≤ selectionObjective μ ρ B σ := exists_optimal_hard μ hs hρ hr hb
example (μ : Measure Gap) [IsProbabilityMeasure μ] (S : Finset Gap) {ρ B : ℝ} (hb : 0 < B) {j : ℕ} {x y : Gap} (hlt : x < y) (hx : x ∈ S) (hy : y ∉ S) (hxj : x ∈ band j) (hyj : y ∈ band j) (hxm : 0 < μ {x}) (hym : 0 < μ {y}) (hf : selectionObjective μ ρ B (μ.restrict S) ≠ ⊤) : ∃ τ : Measure Gap, τ ≤ μ ∧ selectionObjective μ ρ B τ < selectionObjective μ ρ B (μ.restrict S) := improve_inversion μ S hb hlt hx hy hxj hyj hxm hym hf
example : BandwiseSuffixStatement := bandwise_suffix
example (F : Finset Gap) : (suffixChoices F).card ≤ ∏ j ∈ F.image bandIndex, ((slice F j).card + 1) := suffixChoices_card_le F
example (μ : Measure Gap) [IsProbabilityMeasure μ] (hs : μ.support.Finite) {ρ B : ℝ} (hρ : 0 < ρ) (hr : ρ ≤ 1/4) (hB : 0 < B) : ∃ S ∈ suffixChoices hs.toFinset, ∀ σ : Measure Gap, σ ≤ μ → selectionObjective μ ρ B (μ.restrict S) ≤ selectionObjective μ ρ B σ := search_attains μ hs hρ hr hB
#print axioms ThresholdHC.BandwiseSuffix.BandwiseSuffixStatement
#print axioms ThresholdHC.BandwiseSuffix.IsBandSuffix
#print axioms ThresholdHC.BandwiseSuffix.bandIndex
#print axioms ThresholdHC.BandwiseSuffix.bandwise_suffix
#print axioms ThresholdHC.BandwiseSuffix.exists_optimal_hard
#print axioms ThresholdHC.BandwiseSuffix.improve_inversion
#print axioms ThresholdHC.BandwiseSuffix.improving_exchange
#print axioms ThresholdHC.BandwiseSuffix.mem_index_band
#print axioms ThresholdHC.BandwiseSuffix.mem_suffixChoices
#print axioms ThresholdHC.BandwiseSuffix.optimal_is_suffix
#print axioms ThresholdHC.BandwiseSuffix.packet
#print axioms ThresholdHC.BandwiseSuffix.packet_bandCost
#print axioms ThresholdHC.BandwiseSuffix.packet_le_restrict
#print axioms ThresholdHC.BandwiseSuffix.packet_strict_gain
#print axioms ThresholdHC.BandwiseSuffix.packet_tailCost
#print axioms ThresholdHC.BandwiseSuffix.saving
#print axioms ThresholdHC.BandwiseSuffix.saving_strictMono
#print axioms ThresholdHC.BandwiseSuffix.search_attains
#print axioms ThresholdHC.BandwiseSuffix.slice
#print axioms ThresholdHC.BandwiseSuffix.slices_comparable
#print axioms ThresholdHC.BandwiseSuffix.suffixChoices
#print axioms ThresholdHC.BandwiseSuffix.suffixChoices_card_le
#print axioms ThresholdHC.BandwiseSuffix.support_atom_pos
