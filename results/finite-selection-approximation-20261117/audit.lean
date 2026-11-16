import ThresholdHC.FiniteSelectionApproximation.Full
open MeasureTheory ThresholdHC.Tier6 ThresholdHC.EntropyTail ThresholdHC.BandwiseSuffix
open ThresholdHC.GapLawMenus ThresholdHC.BandCostSelection ThresholdHC.SelectionApproximation
open ThresholdHC.FiniteSelectionApproximation
open scoped ENNReal Classical
example : FiniteLawApproximationStatement := finite_law_approximation
example (r : ℝ) (M : ℕ) (hr : 0 < r) (hM : 0 < M) :
    ValidBins (1+1/(M:ℝ)) (binKey r M) := binKey_valid hr hM

example (r x : ℚ) (M : ℕ) : rationalKey r M x = binKey (r:ℝ) M (x:ℝ) :=
  rationalKey_cast r x M

example : rationalKey (1/4) 2 0 = none := by decide
example : rationalKey (1/4) 2 (3/8) = some (0,1) := by norm_num [rationalKey, Int.log]
example : rationalKey (1/4) 2 (1/16) = some (-2,0) := by norm_num [rationalKey, Int.log]

example (m n : ℕ) (R ε : ℝ) (hm : 0 < m) (hn : n ≤ m) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    let L := 4+(⌈Real.logb 2 R⌉₊:ℝ)
    let M := ⌈16*(m:ℝ)*L/ε⌉₊
    let η := (1+1/(M:ℝ))^n-1
    0 ≤ η ∧ η ≤ 1 ∧ L*η ≤ ε/8 := compression_error hm hn hε hε1

example (μ : Measure Gap) [IsProbabilityMeasure μ] (hF : μ.support.Finite)
    (ρ B : ℝ) (hρ : 0 < ρ) (hB : 0 < B) (xs : List (Finset Gap))
    (hx : xs ∈ enumerate (lawMenus μ hF)) :
    min ρ (min (Real.sqrt (ρ*minCost (cost μ) (lawMenus μ hF)/B))
      (min 1 (2/Real.sqrt B))) ≤ menuObjective μ ρ B xs :=
  menuObjective_floor μ hF hρ hB hx

example (μ : Measure Gap) [IsProbabilityMeasure μ] (hF : μ.support.Finite) :
    ((lawMenus μ hF).map Finset.card).sum ≤ hF.toFinset.card+(occupiedBands hF.toFinset).length :=
  lawMenus_option_count μ hF

example (μ : Measure Gap) [IsProbabilityMeasure μ] (hF : μ.support.Finite)
    (ρ B ε : ℝ) (hρ : 0 < ρ) (hρu : ρ ≤ 1/4) (hB : 0 < B) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ ys ∈ lawFrontier μ hF B ε, ys ∈ enumerate (lawMenus μ hF) ∧
      menuObjective μ ρ B ys ≤ (1+ε/4)*(selection μ ρ B).toReal :=
  finite_law_near_optimal μ hF hρ hρu hB hε hε1

example {α : Type*} (F : Finset α) (hne : F.Nonempty) (J : α → ℝ)
    (d b : ℝ) (hd : 0 < d) (hb : 1 < b) (hlower : ∀ x ∈ F, d ≤ J x) :
    ∃ N ≤ ⌈(b+1)/((b-1)*d)⌉₊+1,
      (upperEndpoint N (J (upperWitness F hne J N)):ℝ) ≤ b*(leastLower F hne J N:ℝ) :=
  refinement_terminates F hne J hd hb hlower

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (hF : μ.support.Finite)
    (ρ B ε : ℝ), 0 < ρ → ρ ≤ 1/4 → 0 < B → 0 < ε → ε ≤ 1 →
    let ms := lawMenus μ hF
    let r := minCost (cost μ) ms
    let R := maxCost (cost μ) ms/r
    let L := 4+(⌈Real.logb 2 R⌉₊:ℝ)
    let M := ⌈16*(ms.length:ℝ)*L/ε⌉₊
    let S := 1+M^2*(1+⌊Real.logb 2 R⌋₊)*(1+⌊Real.logb 2 (L*R)⌋₊)
    let Q := hF.toFinset.card+(occupiedBands hF.toFinset).length
    let J := menuObjective μ ρ B
    let K := (selection μ ρ B).toReal
    ∃ N ≤ sufficientPrecision (positiveFloor ρ B r) (1+ε/4),
      ∃ xs ∈ lawFrontier μ hF B ε, ∃ l u : ℚ,
        traceSet xs ∈ suffixChoices hF.toFinset ∧
        ENNReal.ofReal (J xs) = min (ENNReal.ofReal ρ)
          (selectionObjective μ ρ B (μ.restrict (traceSet xs))) ∧
        u = upperEndpoint N (J xs) ∧
        (∀ ys ∈ lawFrontier μ hF B ε, u ≤ upperEndpoint N (J ys)) ∧
        (∀ ys ∈ lawFrontier μ hF B ε, (l:ℝ) ≤ J ys) ∧
        0 < (l:ℝ) ∧ (l:ℝ)/(1+ε/4) ≤ K ∧ K ≤ J xs ∧ J xs ≤ (u:ℝ) ∧
        (u:ℝ) ≤ (1+ε)*((l:ℝ)/(1+ε/4)) ∧
        (∀ rest, rest.IsSuffix ms →
          (trimSolve (binKey r M) (cost μ) (summary (cost μ) r ε)
            (saving μ (1/Real.sqrt B)) rest).card ≤ S) ∧
        extensionCount (binKey r M) (cost μ) (summary (cost μ) r ε)
          (saving μ (1/Real.sqrt B)) ms ≤ Q*S :=
  finite_law_approximation
#print axioms ThresholdHC.FiniteSelectionApproximation.FiniteLawApproximationStatement
#print axioms ThresholdHC.FiniteSelectionApproximation.all_extensions_bound
#print axioms ThresholdHC.FiniteSelectionApproximation.beta
#print axioms ThresholdHC.FiniteSelectionApproximation.beta_bounds
#print axioms ThresholdHC.FiniteSelectionApproximation.binKey
#print axioms ThresholdHC.FiniteSelectionApproximation.binKey_cell
#print axioms ThresholdHC.FiniteSelectionApproximation.binKey_eq_none
#print axioms ThresholdHC.FiniteSelectionApproximation.binKey_mem_positive
#print axioms ThresholdHC.FiniteSelectionApproximation.binKey_valid
#print axioms ThresholdHC.FiniteSelectionApproximation.binKey_zero
#print axioms ThresholdHC.FiniteSelectionApproximation.capped_objective_comparison
#print axioms ThresholdHC.FiniteSelectionApproximation.cellCount
#print axioms ThresholdHC.FiniteSelectionApproximation.cellCount_pos
#print axioms ThresholdHC.FiniteSelectionApproximation.complete_trace
#print axioms ThresholdHC.FiniteSelectionApproximation.compression_error
#print axioms ThresholdHC.FiniteSelectionApproximation.cost_empty
#print axioms ThresholdHC.FiniteSelectionApproximation.dyadic_bounds
#print axioms ThresholdHC.FiniteSelectionApproximation.empty_suffix
#print axioms ThresholdHC.FiniteSelectionApproximation.endpoint_bounds
#print axioms ThresholdHC.FiniteSelectionApproximation.endpoint_certificate
#print axioms ThresholdHC.FiniteSelectionApproximation.endpoint_minima
#print axioms ThresholdHC.FiniteSelectionApproximation.every_stage_card
#print axioms ThresholdHC.FiniteSelectionApproximation.extensionCount
#print axioms ThresholdHC.FiniteSelectionApproximation.extensionCount_bound
#print axioms ThresholdHC.FiniteSelectionApproximation.feasible_key_bound
#print axioms ThresholdHC.FiniteSelectionApproximation.finite_law_approximation
#print axioms ThresholdHC.FiniteSelectionApproximation.finite_law_near_optimal
#print axioms ThresholdHC.FiniteSelectionApproximation.frontier
#print axioms ThresholdHC.FiniteSelectionApproximation.lawFrontier
#print axioms ThresholdHC.FiniteSelectionApproximation.lawMenus
#print axioms ThresholdHC.FiniteSelectionApproximation.lawMenus_empty_option
#print axioms ThresholdHC.FiniteSelectionApproximation.lawMenus_input
#print axioms ThresholdHC.FiniteSelectionApproximation.lawMenus_option_count
#print axioms ThresholdHC.FiniteSelectionApproximation.le_menuMax
#print axioms ThresholdHC.FiniteSelectionApproximation.leastLower
#print axioms ThresholdHC.FiniteSelectionApproximation.logScale
#print axioms ThresholdHC.FiniteSelectionApproximation.logScale_derivative
#print axioms ThresholdHC.FiniteSelectionApproximation.logScale_ge_four
#print axioms ThresholdHC.FiniteSelectionApproximation.lowerEndpoint
#print axioms ThresholdHC.FiniteSelectionApproximation.maxCost
#print axioms ThresholdHC.FiniteSelectionApproximation.maxCost_nonneg
#print axioms ThresholdHC.FiniteSelectionApproximation.mem_options
#print axioms ThresholdHC.FiniteSelectionApproximation.menuMax
#print axioms ThresholdHC.FiniteSelectionApproximation.menuMax_le_maxCost
#print axioms ThresholdHC.FiniteSelectionApproximation.menuMax_nonneg
#print axioms ThresholdHC.FiniteSelectionApproximation.menuObjective_floor
#print axioms ThresholdHC.FiniteSelectionApproximation.menuObjective_form
#print axioms ThresholdHC.FiniteSelectionApproximation.menuObjective_nonneg
#print axioms ThresholdHC.FiniteSelectionApproximation.minCost
#print axioms ThresholdHC.FiniteSelectionApproximation.minCost_le
#print axioms ThresholdHC.FiniteSelectionApproximation.minCost_pos
#print axioms ThresholdHC.FiniteSelectionApproximation.one_band_options
#print axioms ThresholdHC.FiniteSelectionApproximation.options
#print axioms ThresholdHC.FiniteSelectionApproximation.positiveCosts
#print axioms ThresholdHC.FiniteSelectionApproximation.positiveFloor
#print axioms ThresholdHC.FiniteSelectionApproximation.positiveFloor_pos
#print axioms ThresholdHC.FiniteSelectionApproximation.positiveKeys
#print axioms ThresholdHC.FiniteSelectionApproximation.positiveKeys_card
#print axioms ThresholdHC.FiniteSelectionApproximation.positive_support_cost
#print axioms ThresholdHC.FiniteSelectionApproximation.precision_error
#print axioms ThresholdHC.FiniteSelectionApproximation.rationalKey
#print axioms ThresholdHC.FiniteSelectionApproximation.rationalKey_cast
#print axioms ThresholdHC.FiniteSelectionApproximation.refinement_terminates
#print axioms ThresholdHC.FiniteSelectionApproximation.retained_entropy
#print axioms ThresholdHC.FiniteSelectionApproximation.saving_le_cost
#print axioms ThresholdHC.FiniteSelectionApproximation.selection_le_menu
#print axioms ThresholdHC.FiniteSelectionApproximation.self_suffix
#print axioms ThresholdHC.FiniteSelectionApproximation.slice_eq_fiber
#print axioms ThresholdHC.FiniteSelectionApproximation.slice_eq_self_of_subset
#print axioms ThresholdHC.FiniteSelectionApproximation.stateCount
#print axioms ThresholdHC.FiniteSelectionApproximation.stateKeys
#print axioms ThresholdHC.FiniteSelectionApproximation.stateKeys_card
#print axioms ThresholdHC.FiniteSelectionApproximation.sufficientPrecision
#print axioms ThresholdHC.FiniteSelectionApproximation.summary
#print axioms ThresholdHC.FiniteSelectionApproximation.summaryKey_mem
#print axioms ThresholdHC.FiniteSelectionApproximation.summary_nonneg
#print axioms ThresholdHC.FiniteSelectionApproximation.tailRemainder
#print axioms ThresholdHC.FiniteSelectionApproximation.tailRemainder_nonneg
#print axioms ThresholdHC.FiniteSelectionApproximation.traceEntropy
#print axioms ThresholdHC.FiniteSelectionApproximation.traceSaved_mono
#print axioms ThresholdHC.FiniteSelectionApproximation.traceTotal
#print axioms ThresholdHC.FiniteSelectionApproximation.trace_le_maxCost
#print axioms ThresholdHC.FiniteSelectionApproximation.trace_mem_options
#print axioms ThresholdHC.FiniteSelectionApproximation.trace_summary_bounds
#print axioms ThresholdHC.FiniteSelectionApproximation.trace_zero_or_lower
#print axioms ThresholdHC.FiniteSelectionApproximation.trimSolve_card_bound
#print axioms ThresholdHC.FiniteSelectionApproximation.upperEndpoint
#print axioms ThresholdHC.FiniteSelectionApproximation.upperLog
#print axioms ThresholdHC.FiniteSelectionApproximation.upperLog_bounds
#print axioms ThresholdHC.FiniteSelectionApproximation.upperLog_nonneg
#print axioms ThresholdHC.FiniteSelectionApproximation.upperWitness
#print axioms ThresholdHC.FiniteSelectionApproximation.upperWitness_spec
#print axioms ThresholdHC.FiniteSelectionApproximation.zero_cost_objective
