import ThresholdHC.QuantileOptimality.KeptPrice

noncomputable section
open MeasureTheory Real Set
open scoped ENNReal BigOperators
namespace ThresholdHC.QuantileOptimality
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTailQuantile ThresholdHC.OptimalQuantile

theorem budgetScale_invSquare {h : ℝ} (hh : 0 < h) : budgetScale (h⁻¹^2)=h := by
  rw [budgetScale,sqrt_sq (inv_nonneg.mpr hh.le),inv_inv]

theorem kept_selectionCost_bound {m n : ℕ} (hn : m+2 ≤ n) {x : Option (Fin m) → ℝ}
    (hx : ∀ i, 0 ≤ x i) {η h : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hh : 0 ≤ h) (hsmall : h ≤ bandEdge n) :
    selectionCost (realizingLaw hn x η hη hη1) (keptMeasure n x η) (chosenRarity m x) h ≤
      ENNReal.ofReal ((h*chosenRarity m x/bandEdge n)*
        (sqrt (finiteEnvelope (chosenRarity m x) (1+x none) (bandEdge n))+(1+η)*dyadicCost m x)) := by
  have hρ := chosenRarity_pos hx
  have hA : 0 ≤ 1+x none := by linarith [hx none]
  have hF := finiteEnvelope_nonneg (t := bandEdge n) hρ hA
  have hE := keptMeasure_entropy_bound n hx hη.le hη1
  have hrare := mul_le_mul_of_nonneg_left
    (sqrt_le_sqrt (mul_le_mul_of_nonneg_left hE hρ.le)) hh
  change h*sqrt (chosenRarity m x*(measureCostEntropy (keptMeasure n x η)).toReal) ≤
    h*sqrt (chosenRarity m x*(chosenRarity m x/(bandEdge n)^2*
      finiteEnvelope (chosenRarity m x) (1+x none) (bandEdge n))) at hrare
  rw [atom_root_identity hρ (bandEdge_pos n) hF] at hrare
  have hfin := (measureCostEntropy_lt_top_of_support (keptMeasure n x η) (bandEdge_pos n)
    (keptMeasure_support_lower n x η)).ne
  rw [selectionCost,entropy_root_eq_ofReal hfin hρ.le hh,realizingLaw_sub_kept hn x hη hη1,
    ← ENNReal.ofReal_add (mul_nonneg hh (sqrt_nonneg _)) (tailModulus_nonneg _ hh)]
  apply ENNReal.ofReal_le_ofReal
  rw [skippedAtoms_tailModulus hn hx hη hη1 hh hsmall]
  simp only [div_eq_mul_inv] at hrare ⊢
  nlinarith only [hrare]

theorem selection_bound_explicit_budget {m n : ℕ} (hn : m+2 ≤ n) {x : Option (Fin m) → ℝ}
    (hx : ∀ i, 0 ≤ x i) {η h : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hh : 0 < h) (hsmall : h ≤ bandEdge n) :
    ThresholdHC.EntropyTail.selection (realizingLaw hn x η hη hη1) (chosenRarity m x) (h⁻¹^2) ≤
      ENNReal.ofReal ((h*chosenRarity m x/bandEdge n)*
        (sqrt (finiteEnvelope (chosenRarity m x) (1+x none) (bandEdge n))+(1+η)*dyadicCost m x)) := by
  have : IsProbabilityMeasure (realizingLaw hn x η hη hη1) := realizingLaw_probability hn hx hη hη1
  rw [← ThresholdHC.EntropyTail.quantile_selectionValue_eq]
  have hsel : selectionValue (realizingLaw hn x η hη hη1) (chosenRarity m x) (h⁻¹^2) ≤
      selectionCost (realizingLaw hn x η hη hη1) (keptMeasure n x η) (chosenRarity m x) (budgetScale (h⁻¹^2)) :=
    (min_le_right _ _).trans (iInf₂_le (keptMeasure n x η) (keptMeasure_le_law hn x hη hη1))
  rw [budgetScale_invSquare hh] at hsel
  exact hsel.trans (kept_selectionCost_bound hn hx hη hη1 hh.le hsmall)

end ThresholdHC.QuantileOptimality
