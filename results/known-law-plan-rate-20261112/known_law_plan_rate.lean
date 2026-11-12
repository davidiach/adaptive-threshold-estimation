
import ThresholdHC.KnownLawPlanner.PlanQuantileRate
noncomputable section
set_option linter.unusedVariables false
open MeasureTheory Set Real
open scoped NNReal ENNReal BigOperators
open ThresholdHC.KnownLawPlanner
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTailQuantile ThresholdHC.EntropyTailUpper
open ThresholdHC.EntropyTailAssembly ThresholdHC.EntropyTailExecution

example : ∀ (ρ B z : ℝ), planTarget ρ B z = max (128*z) (ρ/(16*(1+sqrt B))) :=
  fun _ _ _ => rfl
example : ∀ {ρ : ℝ} (hρ : 0 < ρ) (B z : ℝ),
    planTerminal hρ B z = Nat.find (exists_planTerminal hρ B z) := by
  intros; rfl
example : ∀ (ν : Measure Gap) [IsFiniteMeasure ν] {ρ : ℝ} (hρ : 0 < ρ) (l : ℕ),
    searchCaps (eta ν) (eta_vanishes ν) hρ l =
      errorCapExponent ν (levelAccuracy ρ l) (levelAccuracy_pos hρ l) := @searchCaps_exact
example : ∀ (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] (N : ℕ) {ρ : ℝ} (hρ : 0 < ρ) (l : ℕ),
    (SplitEnclosure.exact σ τ ζ N).price ρ l
      (searchCaps (eta (σ+τ)) (eta_vanishes (σ+τ)) hρ l) ≤
      levelWorkCertificate σ τ ρ (costEntropy (fun j : Fin N => bandCost σ j.val))
      (ζ.real univ) hρ l := @exact_price_le
example : ∀ (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)] {t ρ : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) (hN : bandEdge N < t) (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4) (J : ℕ) (hzJ : ζ.real univ ≤ levelAccuracy ρ J/8),
    allocationCertificate (fun i : Fin (J+1) => 17*levelAccuracy ρ i.val)
      (planCost (SplitEnclosure.exact σ τ ζ N) ρ
      (searchCaps (eta (σ+τ)) (eta_vanishes (σ+τ)) hρ) J) ≤
      28000*(sqrt (ρ*costEntropy (fun j : Fin N => bandCost σ j.val)) +
      ∫ d : Gap, (d:ℝ)⁻¹ ∂τ) := @exact_plan_spread
example : ∀ {ρ : ℝ} (hρ : 0 < ρ) (B z : ℝ),
    0 < planTarget ρ B z := @planTarget_pos
example : ∀ {ρ : ℝ} (hρ : 0 < ρ) (B z : ℝ),
    ∃ l : ℕ, levelAccuracy ρ l/16 < planTarget ρ B z := @exists_planTerminal
example : ∀ {ρ : ℝ} (hρ : 0 < ρ) (B z : ℝ),
    levelAccuracy ρ (planTerminal hρ B z)/16 < planTarget ρ B z := @planTerminal_spec
example : ∀ {ρ : ℝ} (hρ : 0 < ρ) (B : ℝ) {z : ℝ} (hz : 2048*z ≤ ρ),
    planTarget ρ B z ≤ levelAccuracy ρ (planTerminal hρ B z) := @planTarget_le_terminal
example : ∀ {ρ : ℝ} (hρ : 0 < ρ) (B : ℝ) {z : ℝ} (hz : 2048*z ≤ ρ),
    z ≤ levelAccuracy ρ (planTerminal hρ B z)/128 := @planTerminal_unresolved
example : ∀ {ρ : ℝ} (hρ : 0 < ρ) (B : ℝ) {z : ℝ} (hz0 : 0 ≤ z),
    levelAccuracy ρ (planTerminal hρ B z) < 2048*z + ρ/(1+sqrt B) := @planTerminal_accuracy_lt
example : ∀ (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)] {t ρ B θ : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) (hN : bandEdge N < t) (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4) (hB : 0 < B) (hθ : 0 ≤ θ) (J : ℕ) (hzJ : ζ.real univ ≤ levelAccuracy ρ J/8) (w : Fin (J+1) → ℝ) (hlow : ∀ i, sqrt (17*levelAccuracy ρ i.val / planCost (SplitEnclosure.exact σ τ ζ N) ρ (searchCaps (eta (σ+τ)) (eta_vanishes (σ+τ)) hρ) J i) ≤ w i) (hup : ∀ i, w i ≤ θ * sqrt (17*levelAccuracy ρ i.val / planCost (SplitEnclosure.exact σ τ ζ N) ρ (searchCaps (eta (σ+τ)) (eta_vanishes (σ+τ)) hρ) J i)),
    sqrt (planCertificate ρ (planRates B (planCost (SplitEnclosure.exact σ τ ζ N) ρ
      (searchCaps (eta (σ+τ)) (eta_vanishes (σ+τ)) hρ) J) w)) ≤
      levelAccuracy ρ J + sqrt θ * (28000*(sqrt (ρ*costEntropy
      (fun j : Fin N => bandCost σ j.val)) + ∫ d : Gap, (d:ℝ)⁻¹ ∂τ)) / sqrt B := @exact_plan_rms_le
example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ B : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hB : 0 < B),
    ENNReal.ofReal (ρ/(1+sqrt B)) ≤ ThresholdHC.EntropyTail.selection μ ρ B := @selection_floor
example : ∀ (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)] {ρ B : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) (hcore : σ = quantileCore (σ+τ+ζ) ρ) (htail : τ+ζ = quantileTail (σ+τ+ζ) ρ) (hτs : ∀ᵐ d : Gap ∂τ, budgetScale B ≤ (d:ℝ)) (hζs : ∀ᵐ d : Gap ∂ζ, (d:ℝ) ≤ budgetScale B),
    ∃ K : ℝ, 0 ≤ K ∧ ThresholdHC.EntropyTail.selection (σ+τ+ζ) ρ B = ENNReal.ofReal K ∧
      ρ/(1+sqrt B) ≤ K ∧
      min ρ (ζ.real univ + budgetScale B * (∫ d : Gap, (d:ℝ)⁻¹ ∂τ) +
      budgetScale B * sqrt (ρ * (measureCostEntropy σ).toReal)) ≤ 8/5 * K := @quantile_split_comparison
example : ∀ (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)] {ρ B θ : ℝ} {N : ℕ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) (hθ : 0 ≤ θ) (hcore : σ = quantileCore (σ+τ+ζ) ρ) (htail : τ+ζ = quantileTail (σ+τ+ζ) ρ) (hτs : ∀ᵐ d : Gap ∂τ, budgetScale B ≤ (d:ℝ)) (hζs : ∀ᵐ d : Gap ∂ζ, (d:ℝ) ≤ budgetScale B) (hN : bandEdge N < quantileThreshold (σ+τ+ζ) ρ) (hz : 2048 * ζ.real univ ≤ ρ) (w : Fin (planTerminal hρ B (ζ.real univ) + 1) → ℝ) (hlow : ∀ i, sqrt (17*levelAccuracy ρ i.val / planCost (SplitEnclosure.exact σ τ ζ N) ρ (searchCaps (eta (σ+τ)) (eta_vanishes (σ+τ)) hρ) (planTerminal hρ B (ζ.real univ)) i) ≤ w i) (hup : ∀ i, w i ≤ θ * sqrt (17*levelAccuracy ρ i.val / planCost (SplitEnclosure.exact σ τ ζ N) ρ (searchCaps (eta (σ+τ)) (eta_vanishes (σ+τ)) hρ) (planTerminal hρ B (ζ.real univ)) i)),
    ENNReal.ofReal (min (ρ/2) (sqrt (planCertificate ρ (planRates B
      (planCost (SplitEnclosure.exact σ τ ζ N) ρ
      (searchCaps (eta (σ+τ)) (eta_vanishes (σ+τ)) hρ)
      (planTerminal hρ B (ζ.real univ))) w)))) ≤
      ENNReal.ofReal (1 + 8/5 * max 2048 (28000 * sqrt θ)) *
      ThresholdHC.EntropyTail.selection (σ+τ+ζ) ρ B := @quantile_plan_rate
example : ∀ (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)] {ρ B : ℝ} (θ : ℝ) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) (hcore : σ = quantileCore (σ+τ+ζ) ρ) (htail : τ+ζ = quantileTail (σ+τ+ζ) ρ) (hτs : ∀ᵐ d : Gap ∂τ, budgetScale B ≤ (d:ℝ)) (hζs : ∀ᵐ d : Gap ∂ζ, (d:ℝ) ≤ budgetScale B) (hz : ρ < 2048 * ζ.real univ),
    ENNReal.ofReal (ρ/2) ≤
      ENNReal.ofReal (1 + 8/5 * max 2048 (28000 * sqrt θ)) *
      ThresholdHC.EntropyTail.selection (σ+τ+ζ) ρ B := @quantile_fallback_rate
example : ∀ {ρ c κ r C : ℝ} {K : ℝ≥0∞} (hρ : 0 ≤ ρ) (hκ : κ * sqrt 8 ≤ 6) (hr : r ≤ κ * sqrt (8 * min (ρ^2/4) c)) (hrate : ENNReal.ofReal (min (ρ/2) (sqrt c)) ≤ ENNReal.ofReal C * K),
    ENNReal.ofReal r ≤ ENNReal.ofReal (6 * C) * K := @plan_radius_le
example : ∀ (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)] {ρ B θ κ r : ℝ} {N : ℕ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) (hθ : 0 ≤ θ) (hcore : σ = quantileCore (σ+τ+ζ) ρ) (htail : τ+ζ = quantileTail (σ+τ+ζ) ρ) (hτs : ∀ᵐ d : Gap ∂τ, budgetScale B ≤ (d:ℝ)) (hζs : ∀ᵐ d : Gap ∂ζ, (d:ℝ) ≤ budgetScale B) (hN : bandEdge N < quantileThreshold (σ+τ+ζ) ρ) (hz : 2048 * ζ.real univ ≤ ρ) (w : Fin (planTerminal hρ B (ζ.real univ) + 1) → ℝ) (hlow : ∀ i, sqrt (17*levelAccuracy ρ i.val / planCost (SplitEnclosure.exact σ τ ζ N) ρ (searchCaps (eta (σ+τ)) (eta_vanishes (σ+τ)) hρ) (planTerminal hρ B (ζ.real univ)) i) ≤ w i) (hup : ∀ i, w i ≤ θ * sqrt (17*levelAccuracy ρ i.val / planCost (SplitEnclosure.exact σ τ ζ N) ρ (searchCaps (eta (σ+τ)) (eta_vanishes (σ+τ)) hρ) (planTerminal hρ B (ζ.real univ)) i)) (hκ : κ * sqrt 8 ≤ 6) (hr : r ≤ κ * sqrt (8 * min (ρ^2/4) (planCertificate ρ (planRates B (planCost (SplitEnclosure.exact σ τ ζ N) ρ (searchCaps (eta (σ+τ)) (eta_vanishes (σ+τ)) hρ) (planTerminal hρ B (ζ.real univ))) w)))),
    ENNReal.ofReal r ≤
      ENNReal.ofReal (6 * (1 + 8/5 * max 2048 (28000 * sqrt θ))) *
      ThresholdHC.EntropyTail.selection (σ+τ+ζ) ρ B := @quantile_plan_radius
#print axioms ThresholdHC.KnownLawPlanner.exact_plan_rms_le
#print axioms ThresholdHC.KnownLawPlanner.exact_plan_spread
#print axioms ThresholdHC.KnownLawPlanner.exact_price_le
#print axioms ThresholdHC.KnownLawPlanner.exists_planTerminal
#print axioms ThresholdHC.KnownLawPlanner.planTarget
#print axioms ThresholdHC.KnownLawPlanner.planTarget_le_terminal
#print axioms ThresholdHC.KnownLawPlanner.planTarget_pos
#print axioms ThresholdHC.KnownLawPlanner.planTerminal
#print axioms ThresholdHC.KnownLawPlanner.planTerminal_accuracy_lt
#print axioms ThresholdHC.KnownLawPlanner.planTerminal_spec
#print axioms ThresholdHC.KnownLawPlanner.planTerminal_unresolved
#print axioms ThresholdHC.KnownLawPlanner.plan_radius_le
#print axioms ThresholdHC.KnownLawPlanner.quantile_fallback_rate
#print axioms ThresholdHC.KnownLawPlanner.quantile_plan_radius
#print axioms ThresholdHC.KnownLawPlanner.quantile_plan_rate
#print axioms ThresholdHC.KnownLawPlanner.quantile_split_comparison
#print axioms ThresholdHC.KnownLawPlanner.searchCaps_exact
#print axioms ThresholdHC.KnownLawPlanner.selection_floor
