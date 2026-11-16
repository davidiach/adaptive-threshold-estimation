import ThresholdHC.FiniteSelectionApproximation.Menus

noncomputable section
open MeasureTheory
open scoped Classical BigOperators ENNReal
namespace ThresholdHC.FiniteSelectionApproximation
open ThresholdHC.Tier6 ThresholdHC.EntropyTail ThresholdHC.BandwiseSuffix
open ThresholdHC.BandCostSelection ThresholdHC.GapLawMenus ThresholdHC.EntropyTailQuantile

def tailRemainder (μ : Measure Gap) (B : ℝ) (xs : List (Finset Gap)) : ℝ :=
  (tailCost μ (1/Real.sqrt B)).toReal-traceSaved (saving μ (1/Real.sqrt B)) xs

def positiveFloor (ρ B r : ℝ) : ℝ :=
  min ρ (min (Real.sqrt (ρ*r/B)) (min 1 (2/Real.sqrt B)))

theorem positiveFloor_pos {ρ B r : ℝ} (hρ : 0 < ρ) (hB : 0 < B) (hr : 0 < r) :
    0 < positiveFloor ρ B r := by unfold positiveFloor; positivity

theorem menuObjective_form (μ : Measure Gap) (ρ B : ℝ) (xs : List (Finset Gap)) :
    menuObjective μ ρ B xs = min ρ
      (1/Real.sqrt B*Real.sqrt (ρ*multisetEntropy (traceKey (cost μ) xs))+tailRemainder μ B xs) := by
  unfold menuObjective tailRemainder
  congr 1
  ring

theorem tailRemainder_nonneg (μ : Measure Gap) [IsProbabilityMeasure μ]
    (hF : μ.support.Finite) (B : ℝ) {xs : List (Finset Gap)}
    (hx : xs ∈ enumerate (lawMenus μ hF)) : 0 ≤ tailRemainder μ B xs := by
  have he := trace_saving μ (1/Real.sqrt B) hF.toFinset (occupiedBands hF.toFinset)
    (Finset.nodup_toList _) hx
  have hm : tailCost (μ.restrict (traceSet xs)) (1/Real.sqrt B) ≤ tailCost μ (1/Real.sqrt B) :=
    lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl)
  unfold tailRemainder
  rw [he]
  exact sub_nonneg.mpr (ENNReal.toReal_mono (tailCost_ne_top μ _) hm)

theorem menuObjective_nonneg (μ : Measure Gap) [IsProbabilityMeasure μ]
    (hF : μ.support.Finite) {ρ : ℝ} (hρ : 0 ≤ ρ) (B : ℝ) {xs : List (Finset Gap)}
    (hx : xs ∈ enumerate (lawMenus μ hF)) : 0 ≤ menuObjective μ ρ B xs := by
  rw [menuObjective_form]
  exact le_min hρ (add_nonneg (by positivity) (tailRemainder_nonneg μ hF B hx))

theorem selection_le_menu (μ : Measure Gap) [IsProbabilityMeasure μ]
    (hF : μ.support.Finite) {ρ : ℝ} (hρ : 0 ≤ ρ) (B : ℝ) {xs : List (Finset Gap)}
    (hx : xs ∈ enumerate (lawMenus μ hF)) : (selection μ ρ B).toReal ≤ menuObjective μ ρ B xs := by
  have hm := menuObjective_eq μ hF.toFinset (occupiedBands hF.toFinset)
    (Finset.nodup_toList _) hx hρ B
  have hs : selection μ ρ B ≤ ENNReal.ofReal (menuObjective μ ρ B xs) := by
    rw [hm]
    exact le_min (selection_le_rho μ ρ B) (selection_le_objective Measure.restrict_le_self ρ B)
  simpa only [ENNReal.toReal_ofReal (menuObjective_nonneg μ hF hρ B hx)] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hs

theorem saving_le_cost (μ : Measure Gap) [IsFiniteMeasure μ] {h : ℝ} (hh : 0 ≤ h) (S : Finset Gap) :
    saving μ h S ≤ cost μ S := by
  rw [saving_atomic μ S hh,cost_atomic]
  apply Finset.sum_le_sum
  intro d _
  apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
  exact (min_le_left _ _).trans (by have := four_le_inv_sq d; linarith)

theorem traceSaved_mono {α : Type*} {a b : α → ℝ} (hab : ∀ x, a x ≤ b x) (xs : List α) :
    traceSaved a xs ≤ traceSaved b xs := by
  induction xs with
  | nil => simp [traceSaved]
  | cons x xs ih => simpa [traceSaved] using add_le_add (hab x) ih

theorem zero_cost_objective (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ)
    {xs : List (Finset Gap)} (hz : traceSaved (cost μ) xs = 0) :
    menuObjective μ ρ B xs = min ρ (tailCost μ (1/Real.sqrt B)).toReal := by
  have hs : traceSaved (saving μ (1/Real.sqrt B)) xs = 0 := by
    apply le_antisymm
    · exact (traceSaved_mono (saving_le_cost μ (by positivity)) xs).trans hz.le
    · exact SelectionApproximation.trace_nonneg (fun _ => ENNReal.toReal_nonneg) xs
  let v := fun i : Fin xs.length => cost μ (xs.get i)
  have hv : v = fun _ => 0 := eq_zero_of_costTotal_eq_zero (fun _ => ENNReal.toReal_nonneg)
    ((traceTotal (cost μ) xs).trans hz)
  have hg : multisetEntropy (traceKey (cost μ) xs) = 0 := by
    rw [← traceEntropy]
    change EntropyTailQuantile.costEntropy v = 0
    rw [hv,costEntropy_zero]
  rw [menuObjective,hg,hs]
  simp

/-- The explicit positive floor needed for endpoint refinement includes the
zero-cost selection and applies to the original capped objective. -/
theorem menuObjective_floor (μ : Measure Gap) [IsProbabilityMeasure μ]
    (hF : μ.support.Finite) {ρ B : ℝ} (hρ : 0 < ρ) (hB : 0 < B)
    {xs : List (Finset Gap)} (hx : xs ∈ enumerate (lawMenus μ hF)) :
    positiveFloor ρ B (minCost (cost μ) (lawMenus μ hF)) ≤ menuObjective μ ρ B xs := by
  let r := minCost (cost μ) (lawMenus μ hF)
  have hr : 0 < r := minCost_pos _ _
  rcases trace_zero_or_lower (fun _ => ENNReal.toReal_nonneg) hx with hz | hlo
  · rw [zero_cost_objective μ ρ B hz]
    have htail := tailCost_lower μ (show 0 ≤ 1/Real.sqrt B by positivity)
    rw [measure_univ,mul_one] at htail
    have hreal : min 1 (2/Real.sqrt B) ≤ (tailCost μ (1/Real.sqrt B)).toReal := by
      have ht := ENNReal.toReal_mono (tailCost_ne_top μ _) htail
      rw [ENNReal.toReal_ofReal (by positivity)] at ht
      simpa only [mul_one_div] using ht
    exact le_min (min_le_left _ _) (((min_le_right _ _).trans (min_le_right _ _)).trans hreal)
  · have hG : r ≤ multisetEntropy (traceKey (cost μ) xs) := hlo.trans (by
      rw [← traceTotal,← traceEntropy]
      exact costTotal_le_costEntropy (fun _ => ENNReal.toReal_nonneg))
    have hp : Real.sqrt (ρ*r/B) ≤ 1/Real.sqrt B*Real.sqrt (ρ*multisetEntropy (traceKey (cost μ) xs)) := by
      rw [Real.sqrt_div (mul_nonneg hρ.le hr.le),div_eq_mul_inv,mul_comm (Real.sqrt (ρ*r))]
      simpa only [one_div] using mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hG hρ.le)) (show 0 ≤ (Real.sqrt B)⁻¹ by positivity)
    rw [menuObjective_form]
    apply le_min (min_le_left _ _)
    exact ((min_le_right _ _).trans (min_le_left _ _)).trans (hp.trans
      (le_add_of_nonneg_right (tailRemainder_nonneg μ hF B hx)))

end ThresholdHC.FiniteSelectionApproximation
