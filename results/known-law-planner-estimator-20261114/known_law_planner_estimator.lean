
import ThresholdHC.KnownLawPlanner.PlannerEstimator
noncomputable section
set_option linter.unusedVariables false
open MeasureTheory Set Real
open scoped NNReal ENNReal BigOperators
open ThresholdHC.KnownLawPlanner
open ThresholdHC.Tier6 (Gap AdaptiveEstimator)
open ThresholdHC.EntropyTailQuantile ThresholdHC.EntropyTailUpper
open ThresholdHC.EntropyTailAssembly ThresholdHC.EntropyTailExecution
open ThresholdHC.RareAboveTwo ThresholdHC.ArbitraryLawAdaptation

example : ∀ (σ τ ζ : Measure Gap) {ρ : ℝ} (hcore : σ = quantileCore (σ+τ+ζ) ρ),
    ∀ᵐ d : Gap ∂σ, quantileThreshold (σ+τ+ζ) ρ ≤ (d:ℝ) := @core_support_of_eq
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1),
    ∃ N : ℕ, bandEdge N < quantileThreshold μ ρ := @exists_bandEdge_lt
example : ∀ (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)] {ρ : ℝ} {N : ℕ} (hρ : 0 < ρ)
    (hρ4 : ρ ≤ 1/4) (hcore : σ = quantileCore (σ+τ+ζ) ρ)
    (hN : bandEdge N < quantileThreshold (σ+τ+ζ) ρ) (E : SplitEnclosure σ τ ζ N)
    (hvan : EnvelopeVanishes E.resolvedError) (B : ℝ)
    (w : Fin (planTerminal hρ B E.unresolved + 1) → ℝ)
    (ht : 0 < quantileThreshold (σ+τ+ζ) ρ)
    (hs : ∀ᵐ d : Gap ∂σ, quantileThreshold (σ+τ+ζ) ρ ≤ (d:ℝ)),
    quantilePlanEstimator σ τ ζ hρ hρ4 hcore hN E hvan B w =
      planEstimator σ τ ζ ht hs hN hρ hρ4 (searchCaps E.resolvedError hvan hρ) (planRates B (planCost E ρ (searchCaps E.resolvedError hvan hρ) (planTerminal hρ B E.unresolved)) w) :=
  by intros; rfl
example : ∀ {σ τ ζ : Measure Gap} {N : ℕ} (E : SplitEnclosure σ τ ζ N) {ρ : ℝ}
    (hρ : 0 < ρ) (hvan : EnvelopeVanishes E.resolvedError) (B : ℝ)
    (w : Fin (planTerminal hρ B E.unresolved + 1) → ℝ),
    RunsPlan E hρ hvan B w ↔
      2048 * E.unresolved ≤ ρ ∧ sqrt (planCertificate ρ (planRates B (planCost E ρ (searchCaps E.resolvedError hvan hρ) (planTerminal hρ B E.unresolved)) w)) ≤ ρ/2 :=
  by intros; exact Iff.rfl
example : ∀ (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] {ρ : ℝ}
    (hρ : 0 < ρ) (B : ℝ) (N : ℕ) (i : Fin (planTerminal hρ B (ζ.real univ) + 1)),
    exactWeights σ τ ζ hρ B N i =
      sqrt (17*levelAccuracy ρ i.val /
        planCost (SplitEnclosure.exact σ τ ζ N) ρ
          (searchCaps (eta (σ+τ)) (eta_vanishes (σ+τ)) hρ) (planTerminal hρ B (ζ.real univ)) i) :=
  by intros; rfl
example : ∀ (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)] {ρ B C : ℝ} {N : ℕ} (hρ : 0 < ρ)
    (hρ4 : ρ ≤ 1/4) (hB : 0 < B) (hcore : σ = quantileCore (σ+τ+ζ) ρ)
    (hτs : ∀ᵐ d : Gap ∂τ, budgetScale B ≤ (d:ℝ))
    (hN : bandEdge N < quantileThreshold (σ+τ+ζ) ρ) (E : SplitEnclosure σ τ ζ N)
    (hvan : EnvelopeVanishes E.resolvedError)
    (w : Fin (planTerminal hρ B E.unresolved + 1) → ℝ)
    (hw : 2048 * E.unresolved ≤ ρ → ∀ i, 0 < w i)
    (hplan : 2048 * E.unresolved ≤ ρ →
      ENNReal.ofReal (min (ρ/2) (sqrt (planCertificate ρ (planRates B (planCost E ρ (searchCaps E.resolvedError hvan hρ) (planTerminal hρ B E.unresolved)) w)))) ≤
        ENNReal.ofReal C * ThresholdHC.EntropyTail.selection (σ+τ+ζ) ρ B)
    (hfall : ρ < 2048 * E.unresolved → ENNReal.ofReal (ρ/2) ≤ ENNReal.ofReal C * ThresholdHC.EntropyTail.selection (σ+τ+ζ) ρ B),
    (RunsPlan E hρ hvan B w →
      RareBudget (σ+τ+ζ) (quantilePlanEstimator σ τ ζ hρ hρ4 hcore hN E hvan B w) ρ B ∧
      rareRisk (σ+τ+ζ) (quantilePlanEstimator σ τ ζ hρ hρ4 hcore hN E hvan B w) ρ ≤
        ENNReal.ofReal C * ThresholdHC.EntropyTail.selection (σ+τ+ζ) ρ B) ∧
    (¬ RunsPlan E hρ hvan B w →
      RareBudget (σ+τ+ζ) (constantEstimator (ρ/2)) ρ B ∧
      rareRisk (σ+τ+ζ) (constantEstimator (ρ/2)) ρ ≤ ENNReal.ofReal C * ThresholdHC.EntropyTail.selection (σ+τ+ζ) ρ B) :=
  @planner_output_of_rates
example : ∀ (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)] {ρ B : ℝ} {N : ℕ} (hρ : 0 < ρ)
    (hρ4 : ρ ≤ 1/4) (hB : 0 < B) (hcore : σ = quantileCore (σ+τ+ζ) ρ) (htail : τ+ζ = quantileTail (σ+τ+ζ) ρ) (hτs : ∀ᵐ d : Gap ∂τ, budgetScale B ≤ (d:ℝ)) (hζs : ∀ᵐ d : Gap ∂ζ, (d:ℝ) ≤ budgetScale B)
    (hN : bandEdge N < quantileThreshold (σ+τ+ζ) ρ),
    (RunsPlan (SplitEnclosure.exact σ τ ζ N) hρ (eta_vanishes (σ+τ)) B (exactWeights σ τ ζ hρ B N) →
      RareBudget (σ+τ+ζ) (quantilePlanEstimator σ τ ζ hρ hρ4 hcore hN (SplitEnclosure.exact σ τ ζ N) (eta_vanishes (σ+τ)) B (exactWeights σ τ ζ hρ B N)) ρ B ∧
      rareRisk (σ+τ+ζ) (quantilePlanEstimator σ τ ζ hρ hρ4 hcore hN (SplitEnclosure.exact σ τ ζ N) (eta_vanishes (σ+τ)) B (exactWeights σ τ ζ hρ B N)) ρ ≤ ENNReal.ofReal 44801 * ThresholdHC.EntropyTail.selection (σ+τ+ζ) ρ B) ∧
    (¬ RunsPlan (SplitEnclosure.exact σ τ ζ N) hρ (eta_vanishes (σ+τ)) B (exactWeights σ τ ζ hρ B N) →
      RareBudget (σ+τ+ζ) (constantEstimator (ρ/2)) ρ B ∧
      rareRisk (σ+τ+ζ) (constantEstimator (ρ/2)) ρ ≤ ENNReal.ofReal 44801 * ThresholdHC.EntropyTail.selection (σ+τ+ζ) ρ B) :=
  @exact_planner_output
example : ∀ (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)] {ρ B θ : ℝ} {N : ℕ} (hρ : 0 < ρ)
    (hρ4 : ρ ≤ 1/4) (hB : 0 < B) (hθ : 0 ≤ θ) (hcore : σ = quantileCore (σ+τ+ζ) ρ) (htail : τ+ζ = quantileTail (σ+τ+ζ) ρ) (hτs : ∀ᵐ d : Gap ∂τ, budgetScale B ≤ (d:ℝ)) (hζs : ∀ᵐ d : Gap ∂ζ, (d:ℝ) ≤ budgetScale B)
    (hN : bandEdge N < quantileThreshold (σ+τ+ζ) ρ)
    (E : SplitEnclosure σ τ ζ N) (hE : E.Tight (ζ.real univ))
    (w : Fin (planTerminal hρ B E.unresolved + 1) → ℝ)
    (hlow : ∀ i, sqrt (17*levelAccuracy ρ i.val / planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ) (planTerminal hρ B E.unresolved) i) ≤ w i)
    (hup : ∀ i, w i ≤ θ * sqrt (17*levelAccuracy ρ i.val / planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ) (planTerminal hρ B E.unresolved) i)),
    (RunsPlan E hρ hE.vanishes B w →
      RareBudget (σ+τ+ζ) (quantilePlanEstimator σ τ ζ hρ hρ4 hcore hN E hE.vanishes B w) ρ B ∧
      rareRisk (σ+τ+ζ) (quantilePlanEstimator σ τ ζ hρ hρ4 hcore hN E hE.vanishes B w) ρ ≤ ENNReal.ofReal (1 + 8/5 * max 4096 (224000 * sqrt θ)) * ThresholdHC.EntropyTail.selection (σ+τ+ζ) ρ B) ∧
    (¬ RunsPlan E hρ hE.vanishes B w →
      RareBudget (σ+τ+ζ) (constantEstimator (ρ/2)) ρ B ∧
      rareRisk (σ+τ+ζ) (constantEstimator (ρ/2)) ρ ≤ ENNReal.ofReal (1 + 8/5 * max 4096 (224000 * sqrt θ)) * ThresholdHC.EntropyTail.selection (σ+τ+ζ) ρ B) :=
  @tight_planner_output
#print axioms ThresholdHC.KnownLawPlanner.RunsPlan
#print axioms ThresholdHC.KnownLawPlanner.core_support_of_eq
#print axioms ThresholdHC.KnownLawPlanner.exactWeights
#print axioms ThresholdHC.KnownLawPlanner.exact_planner_output
#print axioms ThresholdHC.KnownLawPlanner.exists_bandEdge_lt
#print axioms ThresholdHC.KnownLawPlanner.planner_output_of_rates
#print axioms ThresholdHC.KnownLawPlanner.quantilePlanEstimator
#print axioms ThresholdHC.KnownLawPlanner.tight_planner_output
