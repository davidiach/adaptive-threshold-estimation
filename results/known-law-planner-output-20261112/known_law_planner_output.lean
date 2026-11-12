
import ThresholdHC.KnownLawPlanner.PlannerOutput
noncomputable section
set_option linter.unusedVariables false
open MeasureTheory Set Real
open scoped NNReal ENNReal BigOperators
open ThresholdHC.KnownLawPlanner
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTailQuantile ThresholdHC.EntropyTailUpper
open ThresholdHC.EntropyTailAssembly ThresholdHC.EntropyTailExecution
open ThresholdHC.RareAboveTwo ThresholdHC.ArbitraryLawAdaptation

example : ∀ (σ τ ζ : Measure Gap) (N : ℕ) {z₀ : ℝ} (hz₀ : 0 ≤ z₀),
    (SplitEnclosure.exactZero σ τ ζ N hz₀).entropy =
      costEntropy (fun j : Fin N => bandCost σ j.val) ∧
    (SplitEnclosure.exactZero σ τ ζ N hz₀).tailInverse = (∫ d : Gap, (d:ℝ)⁻¹ ∂τ) ∧
    (SplitEnclosure.exactZero σ τ ζ N hz₀).unresolved = z₀ + ζ.real univ ∧
    (SplitEnclosure.exactZero σ τ ζ N hz₀).resolvedError = eta (σ+τ) ∧
    (SplitEnclosure.exactZero σ τ ζ N hz₀).tailWork = ordinaryCost τ :=
  fun _ _ _ _ _ _ => ⟨rfl, rfl, rfl, rfl, rfl⟩
example : ∀ (ν : Measure Gap) [IsFiniteMeasure ν] (h : ℝ),
    ∃ τ ζ : Measure Gap, IsFiniteMeasure τ ∧ IsFiniteMeasure ζ ∧ τ+ζ = ν ∧
      (∀ᵐ d : Gap ∂τ, h ≤ (d:ℝ)) ∧ (∀ᵐ d : Gap ∂ζ, (d:ℝ) ≤ h) := @exists_cut
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (B : ℝ),
    ∃ σ τ ζ : Measure Gap, IsFiniteMeasure σ ∧ IsFiniteMeasure τ ∧ IsFiniteMeasure ζ ∧
      σ+τ+ζ = μ ∧ σ = quantileCore μ ρ ∧ τ+ζ = quantileTail μ ρ ∧
      (∀ᵐ d : Gap ∂τ, budgetScale B ≤ (d:ℝ)) ∧ (∀ᵐ d : Gap ∂ζ, (d:ℝ) ≤ budgetScale B) := @exists_quantile_split
example : ∀ (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)] {t ρ B : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) (hN : bandEdge N < t) (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4) (hB : 0 < B) (E : SplitEnclosure σ τ ζ N) (hvan : EnvelopeVanishes E.resolvedError) {J : ℕ} (hzJ : E.unresolved ≤ levelAccuracy ρ J/8) (w : Fin (J+1) → ℝ) (hw : ∀ i, 0 < w i),
    rareMinimaxRisk (σ+τ+ζ) ρ B ≤
      ENNReal.ofReal (min (ρ/2) (sqrt (planCertificate ρ
      (planRates B (planCost E ρ (searchCaps E.resolvedError hvan hρ) J) w)))) := @searched_plan_minimax
example : ∀ (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)] {ρ B θ : ℝ} {N : ℕ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) (hθ : 0 ≤ θ) (hcore : σ = quantileCore (σ+τ+ζ) ρ) (htail : τ+ζ = quantileTail (σ+τ+ζ) ρ) (hτs : ∀ᵐ d : Gap ∂τ, budgetScale B ≤ (d:ℝ)) (hζs : ∀ᵐ d : Gap ∂ζ, (d:ℝ) ≤ budgetScale B) (hN : bandEdge N < quantileThreshold (σ+τ+ζ) ρ) (E : SplitEnclosure σ τ ζ N) (hE : E.Tight (ζ.real univ)) (w : Fin (planTerminal hρ B E.unresolved + 1) → ℝ) (hlow : ∀ i, sqrt (17*levelAccuracy ρ i.val / planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ) (planTerminal hρ B E.unresolved) i) ≤ w i) (hup : ∀ i, w i ≤ θ * sqrt (17*levelAccuracy ρ i.val / planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ) (planTerminal hρ B E.unresolved) i)),
    rareMinimaxRisk (σ+τ+ζ) ρ B ≤
      ENNReal.ofReal (1 + 8/5 * max 4096 (224000 * sqrt θ)) *
      ThresholdHC.EntropyTail.selection (σ+τ+ζ) ρ B := @tight_planner_minimax_rate
example : ∀ (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)] {ρ B : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) (hcore : σ = quantileCore (σ+τ+ζ) ρ) (htail : τ+ζ = quantileTail (σ+τ+ζ) ρ) (hτs : ∀ᵐ d : Gap ∂τ, budgetScale B ≤ (d:ℝ)) (hζs : ∀ᵐ d : Gap ∂ζ, (d:ℝ) ≤ budgetScale B),
    rareMinimaxRisk (σ+τ+ζ) ρ B ≤
      ENNReal.ofReal 44801 * ThresholdHC.EntropyTail.selection (σ+τ+ζ) ρ B := @split_planner_minimax_rate
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ B : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B),
    rareMinimaxRisk μ ρ B ≤ ENNReal.ofReal 44801 * ThresholdHC.EntropyTail.selection μ ρ B := @planner_minimax_rate
example : ∀ (σ τ ζ : Measure Gap) (N : ℕ) {z₀ : ℝ} (hz₀ : 0 ≤ z₀),
    (SplitEnclosure.exactZero σ τ ζ N hz₀).Tight (z₀ + ζ.real univ) := @SplitEnclosure.exactZero_tight
example : ∀ (η : Measure Gap) [IsProbabilityMeasure η] {z₀ ρ : ℝ} (hzρ : z₀ < ρ) (hρ1 : ρ ≤ 1) (B : ℝ),
    ∃ σ τ ζ : Measure Gap, IsFiniteMeasure σ ∧ IsFiniteMeasure τ ∧ IsFiniteMeasure ζ ∧
      σ = ENNReal.ofReal (1 - z₀) • quantileCore η (conditionalRarity ρ z₀) ∧
      τ+ζ = ENNReal.ofReal (1 - z₀) • quantileTail η (conditionalRarity ρ z₀) ∧
      (∀ᵐ d : Gap ∂τ, budgetScale B ≤ (d:ℝ)) ∧ (∀ᵐ d : Gap ∂ζ, (d:ℝ) ≤ budgetScale B) := @exists_zero_atom_split
#print axioms ThresholdHC.KnownLawPlanner.SplitEnclosure.exactZero
#print axioms ThresholdHC.KnownLawPlanner.SplitEnclosure.exactZero_tight
#print axioms ThresholdHC.KnownLawPlanner.exists_cut
#print axioms ThresholdHC.KnownLawPlanner.exists_quantile_split
#print axioms ThresholdHC.KnownLawPlanner.exists_zero_atom_split
#print axioms ThresholdHC.KnownLawPlanner.planner_minimax_rate
#print axioms ThresholdHC.KnownLawPlanner.searched_plan_minimax
#print axioms ThresholdHC.KnownLawPlanner.split_planner_minimax_rate
#print axioms ThresholdHC.KnownLawPlanner.tight_planner_minimax_rate
