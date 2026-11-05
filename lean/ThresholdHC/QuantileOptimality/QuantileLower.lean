import ThresholdHC.QuantileOptimality.CoreEntropy
import ThresholdHC.QuantileOptimality.SelectionUpper

noncomputable section
open MeasureTheory Real Set
open scoped ENNReal BigOperators
namespace ThresholdHC.QuantileOptimality
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTailQuantile ThresholdHC.OptimalQuantile
open ThresholdHC.BandwiseSuffix (packet)

theorem realizing_tailModulus {m n : ℕ} (hn : m+2 ≤ n) {x : Option (Fin m) → ℝ}
    (hx : ∀ i, 0 ≤ x i) {η h : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hsmall : h ≤ bandEdge n) :
    tailModulus (quantileTail (realizingLaw hn x η hη hη1) (chosenRarity m x)) h =
      h*chosenRarity m x/bandEdge n := by
  rw [realizingLaw_quantileTail hn hx hη hη1,← tail_packet_identity n x,
    packet_tailModulus_of_small (inverseScale_pos n hx).le _ hsmall]
  change (chosenRarity m x/(bandEdge n)^2)*h*bandEdge n=h*chosenRarity m x/bandEdge n
  field_simp [(bandEdge_pos n).ne']

theorem quantile_lower_explicit_budget {m n : ℕ} (hn : m+2 ≤ n) {x : Option (Fin m) → ℝ}
    (hx : ∀ i, 0 ≤ x i) {η h : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hh : 0 < h) (hsmall : h ≤ bandEdge n)
    (hclip : (h*chosenRarity m x/bandEdge n)*(1+sqrt (costEntropy x)) ≤ chosenRarity m x) :
    ENNReal.ofReal ((h*chosenRarity m x/bandEdge n)*(1+sqrt (costEntropy x))) ≤
      closedQuantileValue (realizingLaw hn x η hη hη1) (chosenRarity m x) (h⁻¹^2) := by
  have hρ := chosenRarity_pos hx
  have ht := bandEdge_pos n
  have hG := costEntropy_nonneg hx
  let T := h*chosenRarity m x/bandEdge n
  have hT : 0 ≤ T := div_nonneg (mul_nonneg hh.le hρ.le) ht.le
  have hscaled : 0 ≤ inverseScale n x*costEntropy x := mul_nonneg (inverseScale_pos n hx).le hG
  have hrare : ENNReal.ofReal (T*sqrt (costEntropy x)) ≤ ENNReal.ofReal h*
      (ENNReal.ofReal (chosenRarity m x)*
        measureCostEntropy (quantileCore (realizingLaw hn x η hη hη1) (chosenRarity m x)))^(1/(2 : ℝ)) := by
    calc
      _ = ENNReal.ofReal h*(ENNReal.ofReal (chosenRarity m x)*
          ENNReal.ofReal (inverseScale n x*costEntropy x))^(1/(2 : ℝ)) := by
        rw [entropy_root_eq_ofReal ENNReal.ofReal_ne_top hρ.le hh.le,ENNReal.toReal_ofReal hscaled]
        congr 1
        unfold inverseScale
        rw [atom_root_identity hρ ht hG]
        dsimp only [T]
        ring
      _ ≤ _ := by
        gcongr
        exact quantileCore_entropy_lower hn hx hη hη1
  rw [closedQuantileValue,budgetScale_invSquare hh]
  apply le_min (ENNReal.ofReal_le_ofReal hclip)
  rw [realizing_tailModulus hn hx hη hη1 hsmall]
  change ENNReal.ofReal (T*(1+sqrt (costEntropy x))) ≤ ENNReal.ofReal T+_
  rw [mul_add,mul_one,ENNReal.ofReal_add hT (mul_nonneg hT (sqrt_nonneg _))]
  exact add_le_add le_rfl hrare

end ThresholdHC.QuantileOptimality
