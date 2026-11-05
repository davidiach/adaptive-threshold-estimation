import ThresholdHC.GapLawMenus.Costs

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal Classical
namespace ThresholdHC.GapLawMenus
open ThresholdHC.Tier6 ThresholdHC.EntropyTail ThresholdHC.BandwiseSuffix
open ThresholdHC.BandCostSelection

theorem multisetEntropy_map_nonneg {α : Type*} (f : α → ℝ) (hf : ∀ x, 0 ≤ f x)
    (xs : List α) : 0 ≤ multisetEntropy (↑(xs.map f)) := by
  have he : List.ofFn (fun i : Fin xs.length => f (xs.get i)) = xs.map f := by
    rw [← Function.comp_def,← List.map_ofFn,List.ofFn_get]
  rw [← he,multisetEntropy_ofFn]
  exact ThresholdHC.EntropyTailQuantile.costEntropy_nonneg (fun _ => hf _)

def menuObjective (μ : Measure Gap) (ρ B : ℝ) (xs : List (Finset Gap)) : ℝ :=
  min ρ (1/Real.sqrt B * Real.sqrt (ρ*multisetEntropy (traceKey (cost μ) xs)) +
    (tailCost μ (1/Real.sqrt B)).toReal - traceSaved (saving μ (1/Real.sqrt B)) xs)

/-- The real menu objective is the original capped measure objective exactly. -/
theorem menuObjective_eq (μ : Measure Gap) [IsProbabilityMeasure μ]
    (F : Finset Gap) (js : List ℕ) (hj : js.Nodup)
    {xs : List (Finset Gap)} (hx : xs ∈ enumerate (menus F js))
    {ρ : ℝ} (hr : 0 ≤ ρ) (B : ℝ) :
    ENNReal.ofReal (menuObjective μ ρ B xs) =
      min (ENNReal.ofReal ρ) (selectionObjective μ ρ B (μ.restrict (traceSet xs))) := by
  have hg : 0 ≤ multisetEntropy (traceKey (cost μ) xs) :=
    multisetEntropy_map_nonneg (cost μ) (fun _ => ENNReal.toReal_nonneg) xs
  rw [objective_eq_ofReal Measure.restrict_le_self hr hg (trace_gamma μ F js hj hx)]
  rw [menuObjective,ENNReal.ofReal_min,trace_saving μ (1/Real.sqrt B) F js hj hx]
  congr 2
  ring

/-- Compressing the concrete finite-law suffix menus retains an actual selection
whose original entropy-tail value is K, against all fractional submeasures. -/
theorem compressed_attains (μ : Measure Gap) [IsProbabilityMeasure μ]
    (hF : μ.support.Finite) (js : List ℕ) (hj : js.Nodup)
    (hcover : ∀ d ∈ hF.toFinset, bandIndex d ∈ js)
    {ρ B : ℝ} (hr : 0 < ρ) (hu : ρ ≤ 1/4) (hB : 0 < B) :
    ∃ xs ∈ solve (cost μ) (saving μ (1/Real.sqrt B)) (menus hF.toFinset js),
      traceSet xs ∈ suffixChoices hF.toFinset ∧
      selection μ ρ B = ENNReal.ofReal (menuObjective μ ρ B xs) := by
  obtain ⟨xs,hxs,hmin⟩ := menu_attains μ hF js hcover hr hu hB
  have hopt : selection μ ρ B =
      min (ENNReal.ofReal ρ) (selectionObjective μ ρ B (μ.restrict (traceSet xs))) := by
    apply le_antisymm
    · exact le_min (selection_le_rho μ ρ B)
        (selection_le_objective Measure.restrict_le_self ρ B)
    · exact min_le_min le_rfl (le_iInf₂ hmin)
  obtain ⟨ys,hys,hdom⟩ := solve_objective_dominates (cost μ)
    (saving μ (1/Real.sqrt B)) (menus hF.toFinset js)
    (fun a => 1/Real.sqrt B * Real.sqrt (ρ*multisetEntropy a))
    (tailCost μ (1/Real.sqrt B)).toReal ρ hxs
  have hys' := solve_subset (cost μ) (saving μ (1/Real.sqrt B)) _ hys
  refine ⟨ys,hys,trace_suffix _ _ hys',?_⟩
  apply le_antisymm
  · rw [menuObjective_eq μ _ _ hj hys' hr.le B]
    exact le_min (selection_le_rho μ ρ B)
      (selection_le_objective Measure.restrict_le_self ρ B)
  · have h := ENNReal.ofReal_le_ofReal hdom
    change ENNReal.ofReal (menuObjective μ ρ B ys) ≤ ENNReal.ofReal (menuObjective μ ρ B xs) at h
    rw [menuObjective_eq μ _ _ hj hxs hr.le B,← hopt] at h
    exact h

def occupiedBands (F : Finset Gap) : List ℕ := (F.image bandIndex).toList

/-- No covering list or abstract menu model is supplied: the actual finite gap
support constructs the menus and the cost-compressed solver attains K. -/
theorem finite_law_solver (μ : Measure Gap) [IsProbabilityMeasure μ]
    (hF : μ.support.Finite) {ρ B : ℝ}
    (hr : 0 < ρ) (hu : ρ ≤ 1/4) (hB : 0 < B) :
    ∃ xs ∈ solve (cost μ) (saving μ (1/Real.sqrt B))
        (menus hF.toFinset (occupiedBands hF.toFinset)),
      traceSet xs ∈ suffixChoices hF.toFinset ∧
      selection μ ρ B = ENNReal.ofReal (menuObjective μ ρ B xs) := by
  apply compressed_attains μ hF (occupiedBands hF.toFinset)
  · exact Finset.nodup_toList _
  · intro d hd
    exact Finset.mem_toList.mpr (Finset.mem_image_of_mem _ hd)
  · exact hr
  · exact hu
  · exact hB

end ThresholdHC.GapLawMenus

