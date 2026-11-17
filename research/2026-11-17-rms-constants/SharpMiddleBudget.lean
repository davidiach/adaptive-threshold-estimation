import SharpGridIntegral
import SharpGridPrices
import SharpGridSum
import SharpWindowReal

/-! The complete critical single-gap lower bound in the original adaptive
population model, including the certified middle range. -/
noncomputable section
namespace ThresholdHC.SharpRMS
open MeasureTheory Tier6 Window
open scoped ENNReal

theorem middle_minimax_lower (g : Gap) (B : ℝ) (h0 : 2/5 ≤ 2*g.val)
    (h1 : 2*g.val ≤ 39/40) (hb : (2*g.val)^2*B=4) :
    ENNReal.ofReal (1/6:ℝ) ≤ minimaxRisk (Measure.dirac g) B := by
  let s := 2*g.val
  obtain ⟨u,uw,up,area⟩ := real_window_endpoint s h0 h1
  let h := (u:ℝ)/biasDenominator
  have ww : (0:ℝ)<biasDenominator := by norm_num [biasDenominator]
  have hp : 0<u := by
    by_contra! hz
    have : u=0 := by omega
    rw [this] at up
    simp only [Nat.cast_zero,zero_div] at up
    linarith only [h0,up]
  let V := fun i : Fin bins => (rectangleHeight (i.val+1) u biasDenominator:ℝ)/scale
  apply minimax_from_rectangles g B h up ((div_lt_one ww).mpr (by exact_mod_cast uw)) hb
    bins (by decide) V (fun _ => by dsimp [V]; positivity)
  · change (h/s)^2*((∑ i : Fin bins, (rectangleHeight (i.val+1) u biasDenominator:ℝ)/(scale:ℝ))/(bins:ℝ)) ≤ 2/3
    rw [upperSum_real]
    exact area
  · intro i t mem ht
    exact grid_price u biasDenominator hp uw i t mem ht

/-- Every critical point mass at every positive flip bias s≤1. The infimum
includes arbitrary measurable random seeds and unbounded adaptive stopping. -/
theorem critical_minimax_lower (g : Gap) (B : ℝ) (hb : (2*g.val)^2*B=4) :
    ENNReal.ofReal (1/6:ℝ) ≤ minimaxRisk (Measure.dirac g) B := by
  by_cases weak : 2*g.val ≤ 2/5
  · apply le_trans _ (weak_gap_minimax_lower g B weak hb)
    apply ENNReal.ofReal_le_ofReal
    exact (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  by_cases mid : 2*g.val ≤ 39/40
  · exact middle_minimax_lower g B (le_of_not_ge weak) mid hb
  by_cases strong : 2*g.val < 1
  · exact near_perfect_minimax_lower g B (le_of_not_ge mid) strong hb
  have endgap : 2*g.val = 1 := by linarith [g.property.2]
  rw [endgap] at hb
  norm_num at hb
  rw [hb]
  exact four_budget_minimax_lower _ 4 (by norm_num) le_rfl

end ThresholdHC.SharpRMS
