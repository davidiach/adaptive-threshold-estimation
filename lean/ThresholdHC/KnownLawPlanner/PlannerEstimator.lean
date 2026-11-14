import ThresholdHC.KnownLawPlanner.PlannerOutput

/-! The planner's output as a named estimator.

The theorems of `PlannerOutput` bound the minimax risk, which the existing
upper theorem already bounds by `28000 K`. Here the estimator is the
planner's output itself. On the quantile split and an enclosure of its design
integrals the planner runs its plan when `2048 z̄ ≤ ρ` and the certified risk
of the plan is at most `ρ/2`, and returns the constant `ρ/2` otherwise. In
either branch the returned estimator has expected work at most `B` for every
sign law of rarity `ρ`, and risk at most `C K_{μ,ρ}(B)`:

* `C = 44801` with the exact integrals and the optimal weights;
* `C = 1 + (8/5) max{4096, 8 · 28000 √θ}` for a tight enclosure and weights
  within a factor `θ` of the optimal ones.

The rate theorems bound the smaller of `ρ/2` and the certified risk, so the
comparison with `ρ/2` is part of the planner: without it the plan's own risk
bound can exceed `C K`. -/

noncomputable section
open MeasureTheory Set Real
open scoped NNReal ENNReal BigOperators

namespace ThresholdHC.KnownLawPlanner
open ThresholdHC.Tier6 (Gap AdaptiveEstimator)
open ThresholdHC.EntropyTailQuantile ThresholdHC.EntropyTailUpper
open ThresholdHC.EntropyTailAssembly ThresholdHC.EntropyTailExecution
open ThresholdHC.RareAboveTwo ThresholdHC.ArbitraryLawAdaptation

/-- The core of the quantile split lies above the quantile threshold. -/
theorem core_support_of_eq (σ τ ζ : Measure Gap) {ρ : ℝ}
    (hcore : σ = quantileCore (σ+τ+ζ) ρ) :
    ∀ᵐ d : Gap ∂σ, quantileThreshold (σ+τ+ζ) ρ ≤ (d:ℝ) := by
  have h := quantileCore_support (σ+τ+ζ) ρ
  rw [← hcore] at h
  exact h

/-- Some band edge lies below the quantile threshold. -/
theorem exists_bandEdge_lt (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) : ∃ N : ℕ, bandEdge N < quantileThreshold μ ρ := by
  have ht := (quantileThreshold_properties μ hρ hρ1).1
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one ht (by norm_num : (2:ℝ)⁻¹ < 1)
  exact ⟨N, (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ N)).trans_lt hN⟩

/-- The estimator of the plan computed from an enclosure `E` of the quantile
split with weights `w`: the plan's caps are the carried cap search of the
enclosure's envelope, its terminal level is chosen from the enclosure's
unresolved mass and its counts from the weights. -/
def quantilePlanEstimator (σ τ ζ : Measure Gap)
    [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)]
    {ρ : ℝ} {N : ℕ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hcore : σ = quantileCore (σ+τ+ζ) ρ)
    (hN : bandEdge N < quantileThreshold (σ+τ+ζ) ρ) (E : SplitEnclosure σ τ ζ N)
    (hvan : EnvelopeVanishes E.resolvedError) (B : ℝ)
    (w : Fin (planTerminal hρ B E.unresolved + 1) → ℝ) :
    AdaptiveEstimator (Fin (planTerminal hρ B E.unresolved + 1) → ℕ) :=
  planEstimator σ τ ζ (quantileThreshold_properties (σ+τ+ζ) hρ (by linarith)).1
    (core_support_of_eq σ τ ζ hcore) hN hρ hρ4 (searchCaps E.resolvedError hvan hρ)
    (planRates B (planCost E ρ (searchCaps E.resolvedError hvan hρ)
      (planTerminal hρ B E.unresolved)) w)

/-- The planner's decision: it runs the plan when the unresolved mass is
covered, `2048 z̄ ≤ ρ`, and the plan's certified risk is at most `ρ/2`, the
risk of the constant. Otherwise it returns the constant `ρ/2`. -/
def RunsPlan {σ τ ζ : Measure Gap} {N : ℕ} (E : SplitEnclosure σ τ ζ N) {ρ : ℝ}
    (hρ : 0 < ρ) (hvan : EnvelopeVanishes E.resolvedError) (B : ℝ)
    (w : Fin (planTerminal hρ B E.unresolved + 1) → ℝ) : Prop :=
  2048 * E.unresolved ≤ ρ ∧
    sqrt (planCertificate ρ (planRates B (planCost E ρ (searchCaps E.resolvedError hvan hρ)
      (planTerminal hρ B E.unresolved)) w)) ≤ ρ/2

/-- The planner's output from a rate. If the smaller of `ρ/2` and the plan's
certified risk is at most `C K` outside the fallback, and `ρ/2 ≤ C K` in the
fallback, then the estimator the planner returns has budget `B` and risk at
most `C K`, in both branches. -/
theorem planner_output_of_rates (σ τ ζ : Measure Gap)
    [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)]
    {ρ B C : ℝ} {N : ℕ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B)
    (hcore : σ = quantileCore (σ+τ+ζ) ρ)
    (hτs : ∀ᵐ d : Gap ∂τ, budgetScale B ≤ (d:ℝ))
    (hN : bandEdge N < quantileThreshold (σ+τ+ζ) ρ) (E : SplitEnclosure σ τ ζ N)
    (hvan : EnvelopeVanishes E.resolvedError)
    (w : Fin (planTerminal hρ B E.unresolved + 1) → ℝ)
    (hw : 2048 * E.unresolved ≤ ρ → ∀ i, 0 < w i)
    (hplan : 2048 * E.unresolved ≤ ρ →
      ENNReal.ofReal (min (ρ/2) (sqrt (planCertificate ρ (planRates B
        (planCost E ρ (searchCaps E.resolvedError hvan hρ)
          (planTerminal hρ B E.unresolved)) w)))) ≤
        ENNReal.ofReal C * EntropyTail.selection (σ+τ+ζ) ρ B)
    (hfall : ρ < 2048 * E.unresolved →
      ENNReal.ofReal (ρ/2) ≤ ENNReal.ofReal C * EntropyTail.selection (σ+τ+ζ) ρ B) :
    (RunsPlan E hρ hvan B w →
      RareBudget (σ+τ+ζ) (quantilePlanEstimator σ τ ζ hρ hρ4 hcore hN E hvan B w) ρ B ∧
      rareRisk (σ+τ+ζ) (quantilePlanEstimator σ τ ζ hρ hρ4 hcore hN E hvan B w) ρ ≤
        ENNReal.ofReal C * EntropyTail.selection (σ+τ+ζ) ρ B) ∧
    (¬ RunsPlan E hρ hvan B w →
      RareBudget (σ+τ+ζ) (constantEstimator (ρ/2)) ρ B ∧
      rareRisk (σ+τ+ζ) (constantEstimator (ρ/2)) ρ ≤
        ENNReal.ofReal C * EntropyTail.selection (σ+τ+ζ) ρ B) := by
  have hρ1 : ρ ≤ 1 := by linarith
  have ht := (quantileThreshold_properties (σ+τ+ζ) hρ hρ1).1
  have hs := core_support_of_eq σ τ ζ hcore
  have hτ := inverse_integrable_of_support τ (budgetScale_pos hB) hτs
  refine ⟨fun ⟨hz, hc⟩ => ?_, fun hnot => ?_⟩
  · have hzJ : E.unresolved ≤ levelAccuracy ρ (planTerminal hρ B E.unresolved)/8 := by
      have h := planTerminal_unresolved hρ B hz
      linarith [levelAccuracy_pos hρ (planTerminal hρ B E.unresolved)]
    obtain ⟨hb, hr⟩ := searched_plan_valid σ τ ζ ht hs hN hτ hρ hρ4 hB E hvan hzJ w (hw hz)
    refine ⟨hb, hr.trans ?_⟩
    have h := hplan hz
    rwa [min_eq_right hc] at h
  · refine ⟨constant_rare_budget (σ+τ+ζ) ρ B (ρ/2),
      (half_rarity_risk (σ+τ+ζ) ρ hρ.le).trans ?_⟩
    by_cases hz : 2048 * E.unresolved ≤ ρ
    · have hc : ρ/2 < sqrt (planCertificate ρ (planRates B
          (planCost E ρ (searchCaps E.resolvedError hvan hρ)
            (planTerminal hρ B E.unresolved)) w)) :=
        not_le.mp fun h => hnot ⟨hz, h⟩
      have h := hplan hz
      rwa [min_eq_left hc.le] at h
    · exact hfall (not_le.mp hz)

/-- The optimal weights of the exact plan, `√(17 δ_l / k_l)`. -/
def exactWeights (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] {ρ : ℝ}
    (hρ : 0 < ρ) (B : ℝ) (N : ℕ) :
    Fin (planTerminal hρ B (ζ.real univ) + 1) → ℝ := fun i =>
  sqrt (17*levelAccuracy ρ i.val /
    planCost (SplitEnclosure.exact σ τ ζ N) ρ (searchCaps (eta (σ+τ)) (eta_vanishes (σ+τ)) hρ)
      (planTerminal hρ B (ζ.real univ)) i)

/-- The exact planner's output, named. On the quantile split of a law of
positive gaps, cut at the budget scale, with the exact integrals and the
optimal weights, the planner returns the plan or the constant `ρ/2`. Either
estimator has budget `B` and risk at most `44801 K_{μ,ρ}(B)`. -/
theorem exact_planner_output (σ τ ζ : Measure Gap)
    [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)]
    {ρ B : ℝ} {N : ℕ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B)
    (hcore : σ = quantileCore (σ+τ+ζ) ρ) (htail : τ+ζ = quantileTail (σ+τ+ζ) ρ)
    (hτs : ∀ᵐ d : Gap ∂τ, budgetScale B ≤ (d:ℝ)) (hζs : ∀ᵐ d : Gap ∂ζ, (d:ℝ) ≤ budgetScale B)
    (hN : bandEdge N < quantileThreshold (σ+τ+ζ) ρ) :
    (RunsPlan (SplitEnclosure.exact σ τ ζ N) hρ (eta_vanishes (σ+τ)) B
        (exactWeights σ τ ζ hρ B N) →
      RareBudget (σ+τ+ζ) (quantilePlanEstimator σ τ ζ hρ hρ4 hcore hN
        (SplitEnclosure.exact σ τ ζ N) (eta_vanishes (σ+τ)) B (exactWeights σ τ ζ hρ B N)) ρ B ∧
      rareRisk (σ+τ+ζ) (quantilePlanEstimator σ τ ζ hρ hρ4 hcore hN
        (SplitEnclosure.exact σ τ ζ N) (eta_vanishes (σ+τ)) B (exactWeights σ τ ζ hρ B N)) ρ ≤
        ENNReal.ofReal 44801 * EntropyTail.selection (σ+τ+ζ) ρ B) ∧
    (¬ RunsPlan (SplitEnclosure.exact σ τ ζ N) hρ (eta_vanishes (σ+τ)) B
        (exactWeights σ τ ζ hρ B N) →
      RareBudget (σ+τ+ζ) (constantEstimator (ρ/2)) ρ B ∧
      rareRisk (σ+τ+ζ) (constantEstimator (ρ/2)) ρ ≤
        ENNReal.ofReal 44801 * EntropyTail.selection (σ+τ+ζ) ρ B) := by
  have hρ1 : ρ ≤ 1 := by linarith
  have ht := (quantileThreshold_properties (σ+τ+ζ) hρ hρ1).1
  have hs := core_support_of_eq σ τ ζ hcore
  have hτ := inverse_integrable_of_support τ (budgetScale_pos hB) hτs
  have hC : (1:ℝ) + 8/5 * max 2048 (28000 * sqrt 1) = 44801 := by
    rw [sqrt_one, mul_one, max_eq_right (by norm_num)]
    norm_num
  refine planner_output_of_rates σ τ ζ hρ hρ4 hB hcore hτs hN _ _ _ (fun hz i => ?_)
    (fun hz => ?_) (fun hz => ?_)
  · have hzρ : ζ.real univ ≤ ρ := by
      have h0 : 0 ≤ ζ.real univ := measureReal_nonneg
      change 2048 * ζ.real univ ≤ ρ at hz
      linarith
    exact sqrt_pos.mpr (div_pos (mul_pos (by norm_num) (levelAccuracy_pos hρ i.val))
      (planCost_pos σ τ ζ ht hs hN hτ hρ hρ4 hzρ _ _ _ i))
  · have h := quantile_plan_rate σ τ ζ hρ hρ4 hB (by norm_num : (0:ℝ) ≤ 1) hcore htail
      hτs hζs hN hz (exactWeights σ τ ζ hρ B N) (fun i => le_rfl) (fun i => by rw [one_mul]; exact le_rfl)
    rw [hC] at h
    exact h
  · have h := quantile_fallback_rate σ τ ζ 1 hρ hρ4 hB hcore htail hτs hζs hz
    rw [hC] at h
    exact h

/-- The planner's output from upper bounds, named. For a tight enclosure of
the quantile split and weights within a factor `θ` of the optimal ones, the
planner returns the plan or the constant `ρ/2`, and either estimator has
budget `B` and risk at most `(1 + (8/5) max{4096, 8 · 28000 √θ}) K_{μ,ρ}(B)`.
The weight bounds can hold only when `θ ≥ 1`. -/
theorem tight_planner_output (σ τ ζ : Measure Gap)
    [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)]
    {ρ B θ : ℝ} {N : ℕ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) (hθ : 0 ≤ θ)
    (hcore : σ = quantileCore (σ+τ+ζ) ρ) (htail : τ+ζ = quantileTail (σ+τ+ζ) ρ)
    (hτs : ∀ᵐ d : Gap ∂τ, budgetScale B ≤ (d:ℝ)) (hζs : ∀ᵐ d : Gap ∂ζ, (d:ℝ) ≤ budgetScale B)
    (hN : bandEdge N < quantileThreshold (σ+τ+ζ) ρ)
    (E : SplitEnclosure σ τ ζ N) (hE : E.Tight (ζ.real univ))
    (w : Fin (planTerminal hρ B E.unresolved + 1) → ℝ)
    (hlow : ∀ i, sqrt (17*levelAccuracy ρ i.val /
      planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ)
        (planTerminal hρ B E.unresolved) i) ≤ w i)
    (hup : ∀ i, w i ≤ θ * sqrt (17*levelAccuracy ρ i.val /
      planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ)
        (planTerminal hρ B E.unresolved) i)) :
    (RunsPlan E hρ hE.vanishes B w →
      RareBudget (σ+τ+ζ) (quantilePlanEstimator σ τ ζ hρ hρ4 hcore hN E hE.vanishes B w) ρ B ∧
      rareRisk (σ+τ+ζ) (quantilePlanEstimator σ τ ζ hρ hρ4 hcore hN E hE.vanishes B w) ρ ≤
        ENNReal.ofReal (1 + 8/5 * max 4096 (224000 * sqrt θ)) *
          EntropyTail.selection (σ+τ+ζ) ρ B) ∧
    (¬ RunsPlan E hρ hE.vanishes B w →
      RareBudget (σ+τ+ζ) (constantEstimator (ρ/2)) ρ B ∧
      rareRisk (σ+τ+ζ) (constantEstimator (ρ/2)) ρ ≤
        ENNReal.ofReal (1 + 8/5 * max 4096 (224000 * sqrt θ)) *
          EntropyTail.selection (σ+τ+ζ) ρ B) := by
  have hρ1 : ρ ≤ 1 := by linarith
  have ht := (quantileThreshold_properties (σ+τ+ζ) hρ hρ1).1
  have hs := core_support_of_eq σ τ ζ hcore
  have hτ := inverse_integrable_of_support τ (budgetScale_pos hB) hτs
  refine planner_output_of_rates σ τ ζ hρ hρ4 hB hcore hτs hN E hE.vanishes w
    (fun hz i => ?_) (fun hz => ?_) (fun hz => ?_)
  · have hzρ : ζ.real univ ≤ ρ := by
      have h0 : 0 ≤ ζ.real univ := measureReal_nonneg
      linarith [E.unresolved_le]
    exact lt_of_lt_of_le (sqrt_pos.mpr (div_pos
      (mul_pos (by norm_num) (levelAccuracy_pos hρ i.val))
      (planCost_pos σ τ ζ ht hs hN hτ hρ hρ4 hzρ E _ _ i))) (hlow i)
  · exact tight_quantile_plan_rate σ τ ζ hρ hρ4 hB hθ hcore htail hτs hζs hN E hE hz w hlow hup
  · exact tight_quantile_fallback_rate σ τ ζ θ hρ hρ4 hB hcore htail hτs hζs E hE hz

end ThresholdHC.KnownLawPlanner
