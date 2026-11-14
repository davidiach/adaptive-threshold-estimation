
import ThresholdHC.RobustContinuation.RobustPlannerOutput
noncomputable section
set_option linter.unusedVariables false
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
open ThresholdHC.RobustContinuation
open ThresholdHC.Tier6 (Gap SignLaw AdaptiveEstimator signMean squaredRisk experimentLaw
  populationOutput)
open ThresholdHC.ObservableSimulation ThresholdHC.EntropyTailUpper ThresholdHC.RareAboveTwo
open ThresholdHC.EntropyTailQuantile ThresholdHC.EntropyTailAssembly
open ThresholdHC.EntropyTailSampling ThresholdHC.EntropyTailExecution
open ThresholdHC.KnownLawPlanner ThresholdHC.ArbitraryLawAdaptation

example : ∀ (η : Measure Gap) [IsProbabilityMeasure η] (w : ℕ → ℝ≥0) (hw : HasSum w 1) {c : ℝ}
    (hc : 0 < c) {ρ : ℝ} (hρc : ρ ≤ c) (κ : ℕ → ℕ) (l : ℕ),
    (robustFamily η w hw hc hρc κ l).cost =
      raceCost (negativeBankTest w (levelEpsilon l))
        (positiveBankTest η w (ρ*levelEpsilon l/c)) (2 * κ l) ∧
    (robustFamily η w hw hc hρc κ l).value =
      raceValue (negativeBankTest w (levelEpsilon l))
        (positiveBankTest η w (ρ*levelEpsilon l/c)) (2 * κ l) := by
  intros; exact ⟨rfl, rfl⟩
example : ∀ (η : Measure Gap) [IsProbabilityMeasure η] (σ : Measure Gap) [IsFiniteMeasure σ]
    {t : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) (hN : bandEdge N < t) {c : ℝ}
    (hc : 0 < c) {ρ : ℝ} (hρc : ρ ≤ c) (κ : ℕ → ℕ) {J : ℕ} (r : Fin (J+1) → ℝ≥0),
    robustPlanEstimator η σ ht hs hN hc hρc κ r =
      plannedEstimator r (fun i => incrementCall (robustFamily η (referenceWeights σ)
        (referenceWeights_probability σ ht hs hN) hc hρc κ) i.val) := by
  intros; rfl
example : ∀ (η : Measure Gap) [IsProbabilityMeasure η] (weights : ℕ → ℝ≥0) (hw : HasSum weights 1) {ρ c : ℝ} (hc : 0 < c) (hρc : ρ ≤ c) (l L : ℕ) (ω : ℕ → Bool),
    0 < raceCost (negativeBankTest weights (levelEpsilon l))
      (positiveBankTest η weights (ρ*levelEpsilon l/c)) L ω := @robust_raceCost_pos
example : ∀ (η : Measure Gap) [IsProbabilityMeasure η] (w : ℕ → ℝ≥0) (hw : HasSum w 1) {c : ℝ} (hc : 0 < c) {ρ : ℝ} (hρc : ρ ≤ c) (κ : ℕ → ℕ) (l : ℕ) (ω : ℕ → Bool),
    ((robustFamily η w hw hc hρc κ l).cost ω:ℝ) ≤ 2 * 4 ^ κ l := @robustFamily_cost_bound
example : ∀ (η : Measure Gap) [IsProbabilityMeasure η] (w : ℕ → ℝ≥0) (hw : HasSum w 1) {c : ℝ} (hc : 0 < c) {ρ : ℝ} (hρc : ρ ≤ c) (κ : ℕ → ℕ) (l : ℕ) (ω : ℕ → Bool),
    (robustFamily η w hw hc hρc κ l).value ω = 0 ∨ (robustFamily η w hw hc hρc κ l).value ω = 1 := @robustFamily_binary
example : ∀ (η : Measure Gap) [IsProbabilityMeasure η] (ν ζ : Measure Gap) [IsFiniteMeasure ν] [IsFiniteMeasure ζ] {c : ℝ} (hc : 0 < c) (hdesign : ν+ζ = ENNReal.ofReal c • η) (π : Measure (Gap × Gap)) [IsFiniteMeasure π] (hup : ∀ᵐ z ∂π, (z.1:ℝ) ≤ z.2) (href : π.map Prod.fst = ENNReal.ofReal c • η) (μ₀ : Measure Gap) [IsFiniteMeasure μ₀] (μ : Measure Gap) [IsProbabilityMeasure μ] (hμ : μ = π.map Prod.snd + μ₀) (w : ℕ → ℝ≥0) (hw : HasSum w 1) {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ c) (q : SignLaw) (hq : RarePrior μ ρ q) (κ : ℕ → ℕ) (l : ℕ) (hκ : eta ν (4 ^ κ l) ≤ levelAccuracy ρ l/8) (hz : ζ.real univ + μ₀.real univ ≤ levelAccuracy ρ l/8),
    |(∫ ω, (robustFamily η w hw hc hρc κ l).value ω ∂originalPopulationTapeLaw μ q)-
      signMean μ q.val| ≤ levelAccuracy ρ l := @robustFamily_bias
example : ∀ (η : Measure Gap) [IsProbabilityMeasure η] (ν ζ : Measure Gap) [IsFiniteMeasure ν] [IsFiniteMeasure ζ] {c : ℝ} (hc : 0 < c) (hdesign : ν+ζ = ENNReal.ofReal c • η) (π : Measure (Gap × Gap)) [IsFiniteMeasure π] (hup : ∀ᵐ z ∂π, (z.1:ℝ) ≤ z.2) (href : π.map Prod.fst = ENNReal.ofReal c • η) (μ₀ : Measure Gap) [IsFiniteMeasure μ₀] (μ : Measure Gap) [IsProbabilityMeasure μ] (hμ : μ = π.map Prod.snd + μ₀) (w : ℕ → ℝ≥0) (hw : HasSum w 1) {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ c) (q : SignLaw) (hq : RarePrior μ ρ q) (κ : ℕ → ℕ) (l : ℕ) (hκ : ∀ j, j ≤ l → eta ν (4 ^ κ j) ≤ levelAccuracy ρ j/8) (hz : ζ.real univ + μ₀.real univ ≤ levelAccuracy ρ l/8),
    (∫ ω, ((incrementCall (robustFamily η w hw hc hρc κ) l).value ω)^2
      ∂originalPopulationTapeLaw μ q) ≤ 17*levelAccuracy ρ l := @robustFamily_second
example : ∀ (η : Measure Gap) [IsProbabilityMeasure η] (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] {c : ℝ} (hc : 0 < c) (hdesign : σ+τ+ζ = ENNReal.ofReal c • η) (π : Measure (Gap × Gap)) [IsFiniteMeasure π] (hup : ∀ᵐ z ∂π, (z.1:ℝ) ≤ z.2) (href : π.map Prod.fst = ENNReal.ofReal c • η) (μ₀ : Measure Gap) [IsFiniteMeasure μ₀] (μ : Measure Gap) [IsProbabilityMeasure μ] (hμ : μ = π.map Prod.snd + μ₀) {t ρ : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) (hN : bandEdge N < t) (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ) (hρ : 0 < ρ) (hρc : ρ ≤ c) (hz : ζ.real univ ≤ ρ) (q : SignLaw) (hq : RarePrior μ ρ q) (κ : ℕ → ℕ) (l : ℕ),
    (∫ ω, ((robustFamily η (referenceWeights σ) (referenceWeights_probability σ ht hs hN)
      hc hρc κ l).cost ω:ℝ) ∂originalPopulationTapeLaw μ q) ≤
      planLevelWork τ ρ (costEntropy (fun j : Fin N => bandCost σ j.val))
      (ζ.real univ + μ₀.real univ) l (κ l) := @robustFamily_work
example : ∀ (η : Measure Gap) [IsProbabilityMeasure η] (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] {c : ℝ} (hc : 0 < c) (hdesign : σ+τ+ζ = ENNReal.ofReal c • η) (π : Measure (Gap × Gap)) [IsFiniteMeasure π] (hup : ∀ᵐ z ∂π, (z.1:ℝ) ≤ z.2) (href : π.map Prod.fst = ENNReal.ofReal c • η) (μ₀ : Measure Gap) [IsFiniteMeasure μ₀] (μ : Measure Gap) [IsProbabilityMeasure μ] (hμ : μ = π.map Prod.snd + μ₀) {t ρ : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) (hN : bandEdge N < t) (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ) (hρ : 0 < ρ) (hρc : ρ ≤ c) (hz : ζ.real univ ≤ ρ) (q : SignLaw) (hq : RarePrior μ ρ q) (κ : ℕ → ℕ) (l : ℕ),
    (∫ ω, ((robustFamily η (referenceWeights σ) (referenceWeights_probability σ ht hs hN)
      hc hρc κ l).cost ω:ℝ) ∂originalPopulationTapeLaw μ q) ≤
      planLevelPrice τ ρ (costEntropy (fun j : Fin N => bandCost σ j.val))
      (ζ.real univ + μ₀.real univ) l (κ l) := @robustFamily_price
example : ∀ (η : Measure Gap) [IsProbabilityMeasure η] (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] {c : ℝ} (hc : 0 < c) (hdesign : σ+τ+ζ = ENNReal.ofReal c • η) (π : Measure (Gap × Gap)) [IsFiniteMeasure π] (hup : ∀ᵐ z ∂π, (z.1:ℝ) ≤ z.2) (href : π.map Prod.fst = ENNReal.ofReal c • η) (μ₀ : Measure Gap) [IsFiniteMeasure μ₀] (μ : Measure Gap) [IsProbabilityMeasure μ] (hμ : μ = π.map Prod.snd + μ₀) {t ρ B : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) (hN : bandEdge N < t) (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ) (hρ : 0 < ρ) (hρc : ρ ≤ c) (hz : ζ.real univ ≤ ρ) (κ : ℕ → ℕ) (C : ℕ → ℝ) (hC : ∀ l, planLevelPrice τ ρ (costEntropy (fun j : Fin N => bandCost σ j.val)) (ζ.real univ + μ₀.real univ) l (κ l) ≤ C l) {J : ℕ} (r : Fin (J+1) → ℝ≥0) (hwork : ∑ i : Fin (J+1), (r i:ℝ) * adjacentCost C i.val ≤ B),
    RareBudget μ (robustPlanEstimator η σ ht hs hN hc hρc κ r) ρ B := @robust_plan_budget
example : ∀ (η : Measure Gap) [IsProbabilityMeasure η] (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] {c : ℝ} (hc : 0 < c) (hdesign : σ+τ+ζ = ENNReal.ofReal c • η) (π : Measure (Gap × Gap)) [IsFiniteMeasure π] (hup : ∀ᵐ z ∂π, (z.1:ℝ) ≤ z.2) (href : π.map Prod.fst = ENNReal.ofReal c • η) (μ₀ : Measure Gap) [IsFiniteMeasure μ₀] (μ : Measure Gap) [IsProbabilityMeasure μ] (hμ : μ = π.map Prod.snd + μ₀) {t ρ : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) (hN : bandEdge N < t) (hρ : 0 < ρ) (hρc : ρ ≤ c) (κ : ℕ → ℕ) {J : ℕ} (hκ : ∀ l, l ≤ J → eta (σ+τ) (4 ^ κ l) ≤ levelAccuracy ρ l/8) (hzJ : ζ.real univ + μ₀.real univ ≤ levelAccuracy ρ J/8) (r : Fin (J+1) → ℝ≥0) (hr : ∀ i, 0 < (r i:ℝ)) (q : SignLaw) (hq : RarePrior μ ρ q),
    squaredRisk (experimentLaw μ (robustPlanEstimator η σ ht hs hN hc hρc κ r) q)
      (populationOutput (robustPlanEstimator η σ ht hs hN hc hρc κ r)) (signMean μ q.val) ≤
      ENNReal.ofReal (planCertificate ρ r) := @robust_plan_squaredRisk
example : ∀ (η : Measure Gap) [IsProbabilityMeasure η] (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] {c : ℝ} (hc : 0 < c) (hdesign : σ+τ+ζ = ENNReal.ofReal c • η) (π : Measure (Gap × Gap)) [IsFiniteMeasure π] (hup : ∀ᵐ z ∂π, (z.1:ℝ) ≤ z.2) (href : π.map Prod.fst = ENNReal.ofReal c • η) (μ₀ : Measure Gap) [IsFiniteMeasure μ₀] (μ : Measure Gap) [IsProbabilityMeasure μ] (hμ : μ = π.map Prod.snd + μ₀) {t ρ : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) (hN : bandEdge N < t) (hρ : 0 < ρ) (hρc : ρ ≤ c) (κ : ℕ → ℕ) {J : ℕ} (hκ : ∀ l, l ≤ J → eta (σ+τ) (4 ^ κ l) ≤ levelAccuracy ρ l/8) (hzJ : ζ.real univ + μ₀.real univ ≤ levelAccuracy ρ J/8) (r : Fin (J+1) → ℝ≥0) (hr : ∀ i, 0 < (r i:ℝ)),
    rareRisk μ (robustPlanEstimator η σ ht hs hN hc hρc κ r) ρ ≤
      ENNReal.ofReal (Real.sqrt (planCertificate ρ r)) := @robust_plan_rareRisk
example : ∀ {σ τ ζ : Measure Gap} {N : ℕ} (E : SplitEnclosure σ τ ζ N) {ρ z : ℝ} (hρ : 0 < ρ) (hz : z ≤ E.unresolved) (l k : ℕ),
    planLevelPrice τ ρ (costEntropy (fun j : Fin N => bandCost σ j.val)) z l k ≤
      E.price ρ l k := @planLevelPrice_le_price
example : ∀ (η : Measure Gap) [IsProbabilityMeasure η] (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] {c : ℝ} (hc : 0 < c) (hdesign : σ+τ+ζ = ENNReal.ofReal c • η) (π : Measure (Gap × Gap)) [IsFiniteMeasure π] (hup : ∀ᵐ z ∂π, (z.1:ℝ) ≤ z.2) (href : π.map Prod.fst = ENNReal.ofReal c • η) (μ₀ : Measure Gap) [IsFiniteMeasure μ₀] (μ : Measure Gap) [IsProbabilityMeasure μ] (hμ : μ = π.map Prod.snd + μ₀) {t ρ B : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) (hN : bandEdge N < t) (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ) (hρ : 0 < ρ) (hρc : ρ ≤ c) (E : SplitEnclosure σ τ ζ N) (hE₀ : ζ.real univ + μ₀.real univ ≤ E.unresolved) (κ : ℕ → ℕ) {J : ℕ} (hκ : ∀ l, l ≤ J → E.resolvedError (4 ^ κ l) ≤ levelAccuracy ρ l/8) (hzJ : E.unresolved ≤ levelAccuracy ρ J/8) (r : Fin (J+1) → ℝ≥0) (hr : ∀ i, 0 < (r i:ℝ)) (hwork : ∑ i : Fin (J+1), (r i:ℝ) * adjacentCost (fun l => E.price ρ l (κ l)) i.val ≤ B),
    RareBudget μ (robustPlanEstimator η σ ht hs hN hc hρc κ r) ρ B ∧
      rareRisk μ (robustPlanEstimator η σ ht hs hN hc hρc κ r) ρ ≤
      ENNReal.ofReal (Real.sqrt (planCertificate ρ r)) := @robust_enclosed_plan_valid
example : ∀ (η : Measure Gap) [IsProbabilityMeasure η] (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] {c : ℝ} (hc : 0 < c) (hdesign : σ+τ+ζ = ENNReal.ofReal c • η) (π : Measure (Gap × Gap)) [IsFiniteMeasure π] (hup : ∀ᵐ z ∂π, (z.1:ℝ) ≤ z.2) (href : π.map Prod.fst = ENNReal.ofReal c • η) (μ₀ : Measure Gap) [IsFiniteMeasure μ₀] (μ : Measure Gap) [IsProbabilityMeasure μ] (hμ : μ = π.map Prod.snd + μ₀) {t ρ : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) (hN : bandEdge N < t) (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ) (hρ : 0 < ρ) (hρc : ρ ≤ c) (hz : ζ.real univ ≤ ρ) (E : SplitEnclosure σ τ ζ N) (hE₀ : ζ.real univ + μ₀.real univ ≤ E.unresolved) (κ : ℕ → ℕ) (J : ℕ) (i : Fin (J+1)),
    0 < planCost E ρ κ J i := @robust_planCost_pos
example : ∀ (η : Measure Gap) [IsProbabilityMeasure η] (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] {c : ℝ} (hc : 0 < c) (hdesign : σ+τ+ζ = ENNReal.ofReal c • η) (π : Measure (Gap × Gap)) [IsFiniteMeasure π] (hup : ∀ᵐ z ∂π, (z.1:ℝ) ≤ z.2) (href : π.map Prod.fst = ENNReal.ofReal c • η) (μ₀ : Measure Gap) [IsFiniteMeasure μ₀] (μ : Measure Gap) [IsProbabilityMeasure μ] (hμ : μ = π.map Prod.snd + μ₀) {t ρ B : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) (hN : bandEdge N < t) (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ) (hρ : 0 < ρ) (hρc : ρ ≤ c) (hB : 0 < B) (E : SplitEnclosure σ τ ζ N) (hE₀ : ζ.real univ + μ₀.real univ ≤ E.unresolved) (hvan : EnvelopeVanishes E.resolvedError) {J : ℕ} (hzJ : E.unresolved ≤ levelAccuracy ρ J/8) (w : Fin (J+1) → ℝ) (hw : ∀ i, 0 < w i),
    RareBudget μ (robustPlanEstimator η σ ht hs hN hc hρc
      (searchCaps E.resolvedError hvan hρ)
      (planRates B (planCost E ρ (searchCaps E.resolvedError hvan hρ) J) w)) ρ B ∧
      rareRisk μ (robustPlanEstimator η σ ht hs hN hc hρc
      (searchCaps E.resolvedError hvan hρ)
      (planRates B (planCost E ρ (searchCaps E.resolvedError hvan hρ) J) w)) ρ ≤
      ENNReal.ofReal (Real.sqrt (planCertificate ρ
      (planRates B (planCost E ρ (searchCaps E.resolvedError hvan hρ) J) w))) := @robust_searched_plan_valid
example : ∀ (η : Measure Gap) [IsProbabilityMeasure η] {z₀ : ℝ} (hz1 : z₀ ≤ 1) (π : Measure (Gap × Gap)) [IsFiniteMeasure π] (href : π.map Prod.fst = ENNReal.ofReal (1 - z₀) • η) (μ₀ : Measure Gap) [IsFiniteMeasure μ₀] (μ : Measure Gap) [IsProbabilityMeasure μ] (hμ : μ = π.map Prod.snd + μ₀),
    μ₀.real univ = z₀ := @uncoupled_mass
example :
    1 + 4 * max 4096 (224000 * Real.sqrt 2) = plannedCoefficient 28000 := @plannedCoefficient_eq
example : ∀ (η : Measure Gap) [IsProbabilityMeasure η] (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] {z₀ ρ B : ℝ} {N : ℕ} (hz0 : 0 ≤ z₀) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) (hcore : σ = ENNReal.ofReal (1 - z₀) • quantileCore η (conditionalRarity ρ z₀)) (htail : τ+ζ = ENNReal.ofReal (1 - z₀) • quantileTail η (conditionalRarity ρ z₀)) (hτs : ∀ᵐ d : Gap ∂τ, budgetScale B ≤ (d:ℝ)) (hζs : ∀ᵐ d : Gap ∂ζ, (d:ℝ) ≤ budgetScale B) (hN : bandEdge N < quantileThreshold η (conditionalRarity ρ z₀)) (E : SplitEnclosure σ τ ζ N) (hE : E.Tight (z₀ + ζ.real univ)) (w : Fin (planTerminal hρ B E.unresolved + 1) → ℝ) (hlow : ∀ i, Real.sqrt (17*levelAccuracy ρ i.val / planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ) (planTerminal hρ B E.unresolved) i) ≤ w i) (hup : ∀ i, w i ≤ 2 * Real.sqrt (17*levelAccuracy ρ i.val / planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ) (planTerminal hρ B E.unresolved) i)),
    ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R),
      ∀ (π : Measure (Gap × Gap)) (μ₀ μ : Measure Gap) [IsFiniteMeasure π]
      [IsFiniteMeasure μ₀] [IsProbabilityMeasure μ],
      (∀ᵐ z ∂π, (z.1:ℝ) ≤ z.2) → π.map Prod.fst = ENNReal.ofReal (1 - z₀) • η →
      μ = π.map Prod.snd + μ₀ →
      RareBudget μ A ρ B ∧
      rareRisk μ A ρ ≤
      ENNReal.ofReal (plannedCoefficient 28000) * zeroSelection (zeroAtomLaw z₀ η) ρ B := @robust_zero_atom_planner_rate
example : ∀ (η : Measure Gap) [IsProbabilityMeasure η] {z₀ ρ B : ℝ} (hz0 : 0 ≤ z₀) (hzρ : z₀ < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B),
    ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R),
      ∀ (π : Measure (Gap × Gap)) (μ₀ μ : Measure Gap) [IsFiniteMeasure π]
      [IsFiniteMeasure μ₀] [IsProbabilityMeasure μ],
      (∀ᵐ z ∂π, (z.1:ℝ) ≤ z.2) → π.map Prod.fst = ENNReal.ofReal (1 - z₀) • η →
      μ = π.map Prod.snd + μ₀ →
      RareBudget μ A ρ B ∧
      rareRisk μ A ρ ≤
      ENNReal.ofReal (plannedCoefficient 28000) * zeroSelection (zeroAtomLaw z₀ η) ρ B := @robust_planner_rate
#print axioms ThresholdHC.RobustContinuation.planLevelPrice_le_price
#print axioms ThresholdHC.RobustContinuation.plannedCoefficient_eq
#print axioms ThresholdHC.RobustContinuation.robustFamily
#print axioms ThresholdHC.RobustContinuation.robustFamily_bias
#print axioms ThresholdHC.RobustContinuation.robustFamily_binary
#print axioms ThresholdHC.RobustContinuation.robustFamily_cost_bound
#print axioms ThresholdHC.RobustContinuation.robustFamily_price
#print axioms ThresholdHC.RobustContinuation.robustFamily_second
#print axioms ThresholdHC.RobustContinuation.robustFamily_work
#print axioms ThresholdHC.RobustContinuation.robustPlanEstimator
#print axioms ThresholdHC.RobustContinuation.robust_enclosed_plan_valid
#print axioms ThresholdHC.RobustContinuation.robust_planCost_pos
#print axioms ThresholdHC.RobustContinuation.robust_plan_budget
#print axioms ThresholdHC.RobustContinuation.robust_plan_rareRisk
#print axioms ThresholdHC.RobustContinuation.robust_plan_squaredRisk
#print axioms ThresholdHC.RobustContinuation.robust_planner_rate
#print axioms ThresholdHC.RobustContinuation.robust_raceCost_pos
#print axioms ThresholdHC.RobustContinuation.robust_searched_plan_valid
#print axioms ThresholdHC.RobustContinuation.robust_zero_atom_planner_rate
#print axioms ThresholdHC.RobustContinuation.uncoupled_mass
