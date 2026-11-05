import ThresholdHC.QuantileOptimality.LawSupport

noncomputable section
open MeasureTheory Real Set
open scoped ENNReal BigOperators
namespace ThresholdHC.QuantileOptimality
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTailQuantile
open ThresholdHC.BandwiseSuffix (packet)

abbrev boundaryCore {m : ℕ} (n : ℕ) (x : Option (Fin m) → ℝ) : Measure Gap :=
  packet (inverseScale n x*x none) (edgeGap n)

abbrev realizingCore {m n : ℕ} (hn : m+2 ≤ n) (x : Option (Fin m) → ℝ)
    (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) : Measure Gap :=
  boundaryCore n x+skippedAtoms hn x η hη hη1+easyAtom x η

theorem tail_packet_identity {m : ℕ} (n : ℕ) (x : Option (Fin m) → ℝ) :
    packet (inverseScale n x) (edgeGap n)=ENNReal.ofReal (chosenRarity m x) • Measure.dirac (edgeGap n) := by
  unfold packet
  congr 2
  change chosenRarity m x/(bandEdge n)^2*(bandEdge n)^2=chosenRarity m x
  field_simp [(bandEdge_pos n).ne']

theorem boundaryAtom_split {m : ℕ} (n : ℕ) {x : Option (Fin m) → ℝ} (hx : ∀ i, 0 ≤ x i) :
    boundaryAtom n x=packet (inverseScale n x) (edgeGap n)+boundaryCore n x := by
  unfold boundaryAtom boundaryCore
  rw [show inverseScale n x*(1+x none)=inverseScale n x+inverseScale n x*x none by ring,
    packet_add (inverseScale_pos n hx).le (mul_nonneg (inverseScale_pos n hx).le (hx none))]

theorem realizingLaw_split {m n : ℕ} (hn : m+2 ≤ n) {x : Option (Fin m) → ℝ}
    (hx : ∀ i, 0 ≤ x i) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    realizingLaw hn x η hη hη1 = packet (inverseScale n x) (edgeGap n)+realizingCore hn x η hη hη1 := by
  rw [realizingLaw,realizingCore,boundaryAtom_split n hx]
  abel

theorem realizingLaw_quantileCore {m n : ℕ} (hn : m+2 ≤ n) {x : Option (Fin m) → ℝ}
    (hx : ∀ i, 0 ≤ x i) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    quantileCore (realizingLaw hn x η hη hη1) (chosenRarity m x)=realizingCore hn x η hη hη1 := by
  rw [quantileCore,realizingLaw_quantileTail hn hx hη hη1,← tail_packet_identity,
    realizingLaw_split hn hx hη hη1,add_comm,Measure.add_sub_cancel]

theorem boundaryCore_le_realizingCore {m n : ℕ} (hn : m+2 ≤ n) (x : Option (Fin m) → ℝ)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    boundaryCore n x ≤ realizingCore hn x η hη hη1 := by
  unfold realizingCore
  exact (le_add_of_nonneg_right bot_le).trans (le_add_of_nonneg_right bot_le)

theorem skipped_packet_le_realizingCore {m n : ℕ} (hn : m+2 ≤ n) (x : Option (Fin m) → ℝ)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (j : Fin m) :
    packet (inverseScale n x*x (some j)) (coreGap hn η hη hη1 j) ≤ realizingCore hn x η hη hη1 := by
  have hsum : packet (inverseScale n x*x (some j)) (coreGap hn η hη hη1 j) ≤
      skippedAtoms hn x η hη hη1 := by
    unfold skippedAtoms
    exact Finset.single_le_sum
      (f := fun i : Fin m => packet (inverseScale n x*x (some i)) (coreGap hn η hη hη1 i))
      (fun _ _ => bot_le) (Finset.mem_univ j)
  apply hsum.trans
  unfold realizingCore
  exact (le_add_of_nonneg_left bot_le).trans (le_add_of_nonneg_right bot_le)

end ThresholdHC.QuantileOptimality
