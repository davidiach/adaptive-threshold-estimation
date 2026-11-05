import ThresholdHC.QuantileOptimality.AtomicCost

noncomputable section
open MeasureTheory Real Set
open scoped ENNReal BigOperators
namespace ThresholdHC.QuantileOptimality
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.BandwiseSuffix (packet)

theorem packet_support_subset (e : ℝ) (d : Gap) : (packet e d).support ⊆ {d} := by
  apply Measure.support_subset_of_isClosed isClosed_singleton
  unfold packet
  apply Measure.ae_smul_measure
  simp

theorem packet_support_finite (e : ℝ) (d : Gap) : (packet e d).support.Finite :=
  (Set.finite_singleton d).subset (packet_support_subset e d)

theorem packet_sum_support_finite {ι : Type*} (s : Finset ι) (e : ι → ℝ) (d : ι → Gap) :
    (∑ i ∈ s, packet (e i) (d i)).support.Finite := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi,Measure.support_add]
    exact (packet_support_finite (e i) (d i)).union ih

theorem packet_support_lower (e : ℝ) (d : Gap) :
    ∀ᵐ x : Gap ∂packet e d, (d : ℝ) ≤ (x : ℝ) := by
  unfold packet
  apply Measure.ae_smul_measure
  simp

end ThresholdHC.QuantileOptimality
