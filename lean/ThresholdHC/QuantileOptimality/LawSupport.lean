import ThresholdHC.QuantileOptimality.Law
import ThresholdHC.QuantileOptimality.AtomicQuantile

noncomputable section
open MeasureTheory Real Set
open scoped ENNReal BigOperators
namespace ThresholdHC.QuantileOptimality
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTailQuantile
open ThresholdHC.BandwiseSuffix (packet)

theorem coreGap_gt_edge {m n : ℕ} (hn : m+2 ≤ n) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (j : Fin m) : bandEdge n < (coreGap hn η hη hη1 j : ℝ) :=
  aboveGap_gt_boundary _ hη hη1

theorem coreGap_lt_half {m n : ℕ} (hn : m+2 ≤ n) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (j : Fin m) : (coreGap hn η hη hη1 j : ℝ) < 1/2 := by
  apply aboveGap_lt_half
  simp only [Fin.val_castLE]
  omega

theorem packet_sum_support_lower {ι : Type*} (s : Finset ι) (e : ι → ℝ) (d : ι → Gap)
    {t : ℝ} (ht : ∀ i, t ≤ (d i : ℝ)) :
    ∀ᵐ z : Gap ∂(∑ i ∈ s, packet (e i) (d i)), t ≤ (z : ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi,ae_add_measure_iff]
    exact ⟨(packet_support_lower (e i) (d i)).mono (fun z hz => (ht i).trans hz),ih⟩

theorem realizingLaw_support_lower {m n : ℕ} (hn : m+2 ≤ n) (x : Option (Fin m) → ℝ)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ∀ᵐ z : Gap ∂realizingLaw hn x η hη hη1, bandEdge n ≤ (z : ℝ) := by
  rw [realizingLaw,ae_add_measure_iff,ae_add_measure_iff]
  refine ⟨⟨packet_support_lower _ _,?_⟩,?_⟩
  · exact packet_sum_support_lower _ _ _ (fun j => (coreGap_gt_edge hn hη hη1 j).le)
  · exact (packet_support_lower (4*easyMass m x η) (edgeGap 0)).mono
      (fun z hz => (bandEdge_antitone (Nat.zero_le n)).trans hz)

theorem realizingLaw_support_finite {m n : ℕ} (hn : m+2 ≤ n) (x : Option (Fin m) → ℝ)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    (realizingLaw hn x η hη hη1).support.Finite := by
  rw [realizingLaw,Measure.support_add,Measure.support_add]
  exact ((packet_support_finite _ _).union (packet_sum_support_finite _ _ _)).union
    (packet_support_finite _ _)

theorem keptMeasure_le_law {m n : ℕ} (hn : m+2 ≤ n) (x : Option (Fin m) → ℝ)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    keptMeasure n x η ≤ realizingLaw hn x η hη hη1 := by
  have he : realizingLaw hn x η hη hη1 = keptMeasure n x η+skippedAtoms hn x η hη hη1 := by
    unfold realizingLaw keptMeasure
    abel
  rw [he]
  exact le_add_of_nonneg_right bot_le

theorem boundaryAtom_le_law {m n : ℕ} (hn : m+2 ≤ n) (x : Option (Fin m) → ℝ)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    boundaryAtom n x ≤ realizingLaw hn x η hη hη1 := by
  unfold realizingLaw
  exact (le_add_of_nonneg_right bot_le).trans (le_add_of_nonneg_right bot_le)

theorem boundaryAtom_mass_at_edge {m : ℕ} (n : ℕ) {x : Option (Fin m) → ℝ}
    (hx : ∀ i, 0 ≤ x i) :
    (boundaryAtom n x).real {edgeGap n} = chosenRarity m x*(1+x none) := by
  have he : (boundaryAtom n x).real {edgeGap n}=(boundaryAtom n x).real univ := by
    simp [boundaryAtom,packet,measureReal_def]
  rw [he,boundaryAtom_mass n hx]

theorem realizingLaw_atom_lower {m n : ℕ} (hn : m+2 ≤ n) {x : Option (Fin m) → ℝ}
    (hx : ∀ i, 0 ≤ x i) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    chosenRarity m x ≤ (realizingLaw hn x η hη hη1).real {edgeGap n} := by
  have hm := ENNReal.toReal_mono (measure_ne_top (realizingLaw hn x η hη hη1) {edgeGap n})
    (boundaryAtom_le_law hn x hη hη1 {edgeGap n})
  change (boundaryAtom n x).real {edgeGap n} ≤ (realizingLaw hn x η hη hη1).real {edgeGap n} at hm
  rw [boundaryAtom_mass_at_edge n hx] at hm
  have hp := mul_nonneg (chosenRarity_pos hx).le (hx none)
  nlinarith only [hm,hp]

theorem realizingLaw_quantileTail {m n : ℕ} (hn : m+2 ≤ n) {x : Option (Fin m) → ℝ}
    (hx : ∀ i, 0 ≤ x i) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    quantileTail (realizingLaw hn x η hη hη1) (chosenRarity m x) =
      ENNReal.ofReal (chosenRarity m x) • Measure.dirac (edgeGap n) := by
  have : IsProbabilityMeasure (realizingLaw hn x η hη hη1) := realizingLaw_probability hn hx hη hη1
  exact quantileTail_at_min_atom _ (chosenRarity_pos hx) (by linarith [chosenRarity_le_quarter hx])
    (edgeGap n) (realizingLaw_support_lower hn x hη hη1) (realizingLaw_atom_lower hn hx hη hη1)

end ThresholdHC.QuantileOptimality
