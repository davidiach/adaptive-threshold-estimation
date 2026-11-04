import ThresholdHC.SelectionStability.FiniteApproximation
open ThresholdHC.SelectionStability
example : TVStatement := total_variation_stability
example : RoundingStatement := band_preserving_rounding
open MeasureTheory Set ThresholdHC.Tier6 ThresholdHC.EntropyTail
example (μ : Measure Gap) [IsProbabilityMeasure μ] {η r : ℝ} (hη : 0 < η) (hr : 1 < r) : ∃ (ν : Measure Gap) (T : Gap → Gap), IsProbabilityMeasure ν ∧ Measurable T ∧ tvDist μ ν / 2 ≤ η ∧ (∀ d : Gap, (d:ℝ) ≤ (T d:ℝ) ∧ (T d:ℝ) ≤ r*(d:ℝ)) ∧ (∀ j, T ⁻¹' band j = band j) ∧ (ν.map T).support.Finite := finite_approximation_exists μ hη hr
example (μ ν : Measure Gap) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (T : Gap → Gap) (hm : Measurable T) {r η ρ B L U : ℝ} (hr : 1 ≤ r) (hρ : 0 < ρ) (hrho : ρ ≤ 1/4) (hb : 0 < B) (hη : tvDist μ ν / 2 ≤ η) (hd : ∀ d : Gap, (d:ℝ) ≤ (T d:ℝ) ∧ (T d:ℝ) ≤ r*(d:ℝ)) (hj : ∀ j, T ⁻¹' band j = band j) (hl : L ≤ (selection (ν.map T) ρ B).toReal) (hu : (selection (ν.map T) ρ B).toReal ≤ U) : max 0 (L-η) ≤ (selection μ ρ B).toReal ∧ (selection μ ρ B).toReal ≤ min ρ (r*U+η) := transfer_enclosure μ ν T hm hr hρ hrho hb hη hd hj hl hu
example (μ ν : Measure Gap) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (T : Gap → Gap) (hm : Measurable T) {r η ρ B : ℝ} (hr : 1 ≤ r) (hρ : 0 < ρ) (hrho : ρ ≤ 1/4) (hb : 0 < B) (hη : tvDist μ ν / 2 ≤ η) (hd : ∀ d : Gap, (d:ℝ) ≤ (T d:ℝ) ∧ (T d:ℝ) ≤ r*(d:ℝ)) (hj : ∀ j, T ⁻¹' band j = band j) : let Q := (ThresholdHC.EntropyTailQuantile.closedQuantileValue (ν.map T) ρ B).toReal; max 0 (5/8*Q-η) ≤ (selection μ ρ B).toReal ∧ (selection μ ρ B).toReal ≤ min ρ (r*Q+η) := quantile_enclosure μ ν T hm hr hρ hrho hb hη hd hj
#print axioms ThresholdHC.SelectionStability.RoundingStatement
#print axioms ThresholdHC.SelectionStability.TVStatement
#print axioms ThresholdHC.SelectionStability.band_preserving_rounding
#print axioms ThresholdHC.SelectionStability.common_part
#print axioms ThresholdHC.SelectionStability.finite_approximation_exists
#print axioms ThresholdHC.SelectionStability.finite_rounding_grid
#print axioms ThresholdHC.SelectionStability.gamma_le_scaled
#print axioms ThresholdHC.SelectionStability.index_eq_iff
#print axioms ThresholdHC.SelectionStability.map_costs
#print axioms ThresholdHC.SelectionStability.map_objective
#print axioms ThresholdHC.SelectionStability.measurable_index
#print axioms ThresholdHC.SelectionStability.quantile_enclosure
#print axioms ThresholdHC.SelectionStability.rounding_kernels
#print axioms ThresholdHC.SelectionStability.selection_le_tv
#print axioms ThresholdHC.SelectionStability.total_variation_stability
#print axioms ThresholdHC.SelectionStability.transfer_enclosure
#print axioms ThresholdHC.SelectionStability.transfer_hard
#print axioms ThresholdHC.SelectionStability.trim_small_gaps
