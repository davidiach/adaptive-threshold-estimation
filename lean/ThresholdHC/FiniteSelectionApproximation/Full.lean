import ThresholdHC.FiniteSelectionApproximation.Specification
import ThresholdHC.FiniteSelectionApproximation.Compression

noncomputable section
open MeasureTheory
open scoped Classical ENNReal
namespace ThresholdHC.FiniteSelectionApproximation
open ThresholdHC.Tier6 ThresholdHC.EntropyTail ThresholdHC.BandwiseSuffix
open ThresholdHC.BandCostSelection ThresholdHC.GapLawMenus ThresholdHC.SelectionApproximation

/-- Compression is now compared to the original `K`, whose infimum ranges over
all fractional submeasures. The retained state is a feasible bandwise suffix. -/
theorem finite_law_near_optimal (μ : Measure Gap) [IsProbabilityMeasure μ]
    (hF : μ.support.Finite) {ρ B ε : ℝ} (hρ : 0 < ρ) (hρu : ρ ≤ 1/4)
    (hB : 0 < B) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ ys ∈ lawFrontier μ hF B ε, ys ∈ enumerate (lawMenus μ hF) ∧
      menuObjective μ ρ B ys ≤ beta ε*(selection μ ρ B).toReal := by
  obtain ⟨xs,hx,_,hK⟩ := finite_law_solver μ hF hρ hρu hB
  have hx' := solve_subset (cost μ) (saving μ (1/Real.sqrt B)) _ hx
  have hKr : (selection μ ρ B).toReal = menuObjective μ ρ B xs := by
    rw [hK,ENNReal.toReal_ofReal (menuObjective_nonneg μ hF hρ.le B hx')]
  obtain ⟨hm,hR⟩ := lawMenus_input μ hF
  obtain ⟨ys,hy,hy',hs,hg⟩ := retained_entropy (cost μ) (saving μ (1/Real.sqrt B))
    (fun _ => ENNReal.toReal_nonneg) (lawMenus μ hF) hm hε hε1 hR hx'
  refine ⟨ys,hy,hy',?_⟩
  rw [hKr,menuObjective_form,menuObjective_form]
  exact capped_objective_comparison hρ.le hB hε hε1
    (multisetEntropy_map_nonneg (cost μ) (fun _ => ENNReal.toReal_nonneg) xs) hg
    (tailRemainder_nonneg μ hF B hx') (sub_le_sub_left hs _)

/-- The assembled finite-law `(1+ε)` theorem, including the original-objective
endpoint certificate, its finite precision bound, the suffix witness, and `Q*S`. -/
theorem finite_law_approximation : FiniteLawApproximationStatement := by
  intro μ _ hF ρ B ε hρ hρu hB hε hε1
  dsimp
  let F := lawFrontier μ hF B ε
  let J := menuObjective μ ρ B
  let r := minCost (cost μ) (lawMenus μ hF)
  have hr : 0 < r := minCost_pos _ _
  obtain ⟨v,hv,_,hvK⟩ := finite_law_near_optimal μ hF hρ hρu hB hε hε1
  have hne : F.Nonempty := ⟨v,hv⟩
  have feasible {xs : List (Finset Gap)} (hx : xs ∈ F) : xs ∈ enumerate (lawMenus μ hF) :=
    trimSolve_subset _ _ _ _ _ hx
  have hfloor : ∀ xs ∈ F, positiveFloor ρ B r ≤ J xs :=
    fun xs hx => menuObjective_floor μ hF hρ hB (feasible hx)
  have hK : ∀ xs ∈ F, (selection μ ρ B).toReal ≤ J xs :=
    fun xs hx => selection_le_menu μ hF hρ.le B (feasible hx)
  obtain ⟨N,hN,xs,hxs,l,u,hw,hl,hu,hl0,hlK,hKJ,hJu,huε⟩ := endpoint_certificate F hne J
    (positiveFloor_pos hρ hB hr) hε hε1 hfloor hK ⟨v,hv,hvK⟩
  refine ⟨N,hN,xs,hxs,l,u,trace_suffix _ _ (feasible hxs),
    menuObjective_eq μ hF.toFinset (occupiedBands hF.toFinset) (Finset.nodup_toList _)
      (feasible hxs) hρ.le B,hu,?_,?_,hl0,hlK,hKJ,hJu,huε,?_,?_⟩
  · intro ys hy
    rw [hu,hw]
    exact (upperWitness_spec F hne J N).2 ys hy
  · intro ys hy
    rw [hl]
    exact (endpoint_minima F hne J N).1 ys hy
  · obtain ⟨hm,hR⟩ := lawMenus_input μ hF
    exact every_stage_card (cost μ) (saving μ (1/Real.sqrt B)) (fun _ => ENNReal.toReal_nonneg)
      (lawMenus μ hF) hm ∅ (cost_empty μ) (lawMenus_empty_option μ hF) hε hε1 hR
  · obtain ⟨hm,hR⟩ := lawMenus_input μ hF
    exact (all_extensions_bound (cost μ) (saving μ (1/Real.sqrt B)) (fun _ => ENNReal.toReal_nonneg)
      (lawMenus μ hF) hm ∅ (cost_empty μ) (lawMenus_empty_option μ hF) hε hε1 hR).trans
      (Nat.mul_le_mul_right _ (lawMenus_option_count μ hF))

end ThresholdHC.FiniteSelectionApproximation
