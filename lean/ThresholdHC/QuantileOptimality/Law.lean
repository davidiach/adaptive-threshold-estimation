import ThresholdHC.QuantileOptimality.PacketCalculus
import ThresholdHC.QuantileOptimality.Masses

noncomputable section
open MeasureTheory Real Set
open scoped ENNReal BigOperators
namespace ThresholdHC.QuantileOptimality
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTailQuantile
open ThresholdHC.BandwiseSuffix (packet)

def coreGap {m n : ℕ} (hn : m+2 ≤ n) (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) (j : Fin m) : Gap :=
  aboveGap (Fin.castLE (by omega : m ≤ n) j) η hη hη1

def inverseScale {m : ℕ} (n : ℕ) (x : Option (Fin m) → ℝ) : ℝ :=
  chosenRarity m x/(bandEdge n)^2

abbrev boundaryAtom {m : ℕ} (n : ℕ) (x : Option (Fin m) → ℝ) : Measure Gap :=
  packet (inverseScale n x*(1+x none)) (edgeGap n)

abbrev skippedAtoms {m n : ℕ} (hn : m+2 ≤ n) (x : Option (Fin m) → ℝ)
    (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) : Measure Gap :=
  ∑ j : Fin m, packet (inverseScale n x*x (some j)) (coreGap hn η hη hη1 j)

abbrev easyAtom {m : ℕ} (x : Option (Fin m) → ℝ) (η : ℝ) : Measure Gap :=
  packet (4*easyMass m x η) (edgeGap 0)

abbrev realizingLaw {m n : ℕ} (hn : m+2 ≤ n) (x : Option (Fin m) → ℝ)
    (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) : Measure Gap :=
  boundaryAtom n x+skippedAtoms hn x η hη hη1+easyAtom x η

abbrev keptMeasure {m : ℕ} (n : ℕ) (x : Option (Fin m) → ℝ) (η : ℝ) : Measure Gap :=
  boundaryAtom n x+easyAtom x η

theorem inverseScale_pos {m : ℕ} (n : ℕ) {x : Option (Fin m) → ℝ} (hx : ∀ i, 0 ≤ x i) :
    0 < inverseScale n x :=
  div_pos (chosenRarity_pos hx) (sq_pos_of_pos (bandEdge_pos n))

theorem boundaryAtom_mass {m : ℕ} (n : ℕ) {x : Option (Fin m) → ℝ} (hx : ∀ i, 0 ≤ x i) :
    (boundaryAtom n x).real univ=chosenRarity m x*(1+x none) := by
  rw [boundaryAtom,packet_real_mass (mul_nonneg (inverseScale_pos n hx).le (by linarith [hx none]))]
  change (chosenRarity m x/(bandEdge n)^2*(1+x none))*(bandEdge n)^2=_
  field_simp [(bandEdge_pos n).ne']

theorem skippedAtoms_mass {m n : ℕ} (hn : m+2 ≤ n) {x : Option (Fin m) → ℝ}
    (hx : ∀ i, 0 ≤ x i) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    (skippedAtoms hn x η hη hη1).real univ =
      chosenRarity m x*(∑ j : Fin m, x (some j)*((2 : ℝ)^j.val*(1+η))^2) := by
  rw [skippedAtoms,packet_sum_mass _ _ _ (fun j => mul_nonneg (inverseScale_pos n hx).le (hx (some j))),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  change (chosenRarity m x/(bandEdge n)^2*x (some j))*
      (bandEdge n*(2 : ℝ)^j.val*(1+η))^2 = _
  field_simp [(bandEdge_pos n).ne']

theorem easyAtom_mass {m : ℕ} {x : Option (Fin m) → ℝ} (hx : ∀ i, 0 ≤ x i)
    {η : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1) :
    (easyAtom x η).real univ=easyMass m x η := by
  have he : 0 ≤ easyMass m x η := by linarith [(easyMass_bounds hx hη hη1).1]
  rw [easyAtom,packet_real_mass (mul_nonneg (by norm_num) he)]
  norm_num [edgeGap,bandEdge]
  ring

theorem realizingLaw_mass {m n : ℕ} (hn : m+2 ≤ n) {x : Option (Fin m) → ℝ}
    (hx : ∀ i, 0 ≤ x i) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    (realizingLaw hn x η hη hη1).real univ=1 := by
  rw [realizingLaw,measureReal_add_apply,measureReal_add_apply,boundaryAtom_mass n hx,
    skippedAtoms_mass hn hx hη hη1,easyAtom_mass hx hη.le hη1]
  unfold easyMass massScale
  ring

theorem realizingLaw_probability {m n : ℕ} (hn : m+2 ≤ n) {x : Option (Fin m) → ℝ}
    (hx : ∀ i, 0 ≤ x i) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    IsProbabilityMeasure (realizingLaw hn x η hη hη1) := by
  constructor
  rw [← ENNReal.ofReal_toReal (measure_ne_top (realizingLaw hn x η hη hη1) univ)]
  change ENNReal.ofReal ((realizingLaw hn x η hη hη1).real univ)=1
  rw [realizingLaw_mass hn hx hη hη1]
  norm_num

end ThresholdHC.QuantileOptimality
