import ThresholdHC.RobustContinuation.RobustPlan
import ThresholdHC.KnownLawPlanner.PlannerOutput

/-! One estimator for every true law above the reference.

The reference law is `α = z₀ δ₀ + (1 - z₀) η`, with `η` a probability law of
positive gaps. The planner works from `α` alone: it takes the zero-atom
quantile design of `α`, an enclosure of its integrals, and weights, and it
returns the plan, or the constant `ρ/2` when the unresolved mass is large or
the plan's certified risk is above `ρ/2`.

A true law `μ` is coupled above `α` when it is the second marginal of a
coupling `π` with first marginal `(1 - z₀) η` and `z.1 ≤ z.2` almost
everywhere, plus a part `μ₀`; then `μ₀` has mass `z₀`. Under every such `μ`
and every sign law with positive fraction at most `ρ`, the planner's
estimator spends at most `B` in expectation and has root-mean-square risk at
most `C₀ K_α(B)`, with `C₀` the planned coefficient at the multilevel
coefficient `28000` and `K_α` the selection functional of the reference.

The estimator is chosen before the true law: the statement is
`∃ estimator, ∀ true law`. The coupling is a hypothesis. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace ThresholdHC.RobustContinuation
open ThresholdHC.Tier6 (Gap AdaptiveEstimator)
open ThresholdHC.EntropyTailUpper ThresholdHC.RareAboveTwo
open ThresholdHC.EntropyTailQuantile ThresholdHC.EntropyTailAssembly
open ThresholdHC.EntropyTailExecution ThresholdHC.KnownLawPlanner
open ThresholdHC.ArbitraryLawAdaptation

/-- The part of a true law that is coupled to no positive reference gap has
the mass the reference law has at zero. -/
theorem uncoupled_mass (η : Measure Gap) [IsProbabilityMeasure η] {z₀ : ℝ} (hz1 : z₀ ≤ 1)
    (π : Measure (Gap × Gap)) [IsFiniteMeasure π]
    (href : π.map Prod.fst = ENNReal.ofReal (1 - z₀) • η) (μ₀ : Measure Gap)
    [IsFiniteMeasure μ₀] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (hμ : μ = π.map Prod.snd + μ₀) : μ₀.real univ = z₀ := by
  have h1 : μ.real univ = 1 := probReal_univ
  have h2 : (π.map Prod.snd).real univ = 1 - z₀ := by
    rw [map_measureReal_apply measurable_snd MeasurableSet.univ, preimage_univ,
      coupling_real_univ π href, measureReal_ennreal_smul_apply, probReal_univ, mul_one,
      ENNReal.toReal_ofReal (by linarith)]
  rw [hμ, measureReal_add_apply, h2] at h1
  linarith

/-- The planned coefficient at `28000` is the factor-two coefficient of the
zero-atom rate. -/
theorem plannedCoefficient_eq :
    1 + 4 * max 4096 (224000 * Real.sqrt 2) = plannedCoefficient 28000 := by
  unfold plannedCoefficient
  rw [show (224000:ℝ) * Real.sqrt 2 = 8 * Real.sqrt 2 * 28000 by ring]

/-- **The planner's estimator under every true law above the reference,
from upper bounds.** For the zero-atom quantile design of the reference,
every tight enclosure and all weights within a factor two of the optimal
ones, there is one estimator, the plan or the constant `ρ/2`, that under
every true law coupled above the reference spends at most `B` in expectation
and has root-mean-square risk at most `C₀ K_α(B)`, over all rare priors. -/
theorem robust_zero_atom_planner_rate (η : Measure Gap) [IsProbabilityMeasure η]
    (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ]
    {z₀ ρ B : ℝ} {N : ℕ} (hz0 : 0 ≤ z₀) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B)
    (hcore : σ = ENNReal.ofReal (1 - z₀) • quantileCore η (conditionalRarity ρ z₀))
    (htail : τ+ζ = ENNReal.ofReal (1 - z₀) • quantileTail η (conditionalRarity ρ z₀))
    (hτs : ∀ᵐ d : Gap ∂τ, budgetScale B ≤ (d:ℝ)) (hζs : ∀ᵐ d : Gap ∂ζ, (d:ℝ) ≤ budgetScale B)
    (hN : bandEdge N < quantileThreshold η (conditionalRarity ρ z₀))
    (E : SplitEnclosure σ τ ζ N) (hE : E.Tight (z₀ + ζ.real univ))
    (w : Fin (planTerminal hρ B E.unresolved + 1) → ℝ)
    (hlow : ∀ i, Real.sqrt (17*levelAccuracy ρ i.val /
      planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ)
        (planTerminal hρ B E.unresolved) i) ≤ w i)
    (hup : ∀ i, w i ≤ 2 * Real.sqrt (17*levelAccuracy ρ i.val /
      planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ)
        (planTerminal hρ B E.unresolved) i)) :
    ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R),
      ∀ (π : Measure (Gap × Gap)) (μ₀ μ : Measure Gap) [IsFiniteMeasure π]
        [IsFiniteMeasure μ₀] [IsProbabilityMeasure μ],
        (∀ᵐ z ∂π, (z.1:ℝ) ≤ z.2) → π.map Prod.fst = ENNReal.ofReal (1 - z₀) • η →
        μ = π.map Prod.snd + μ₀ →
        RareBudget μ A ρ B ∧
          rareRisk μ A ρ ≤
            ENNReal.ofReal (plannedCoefficient 28000) * zeroSelection (zeroAtomLaw z₀ η) ρ B := by
  have hh := budgetScale_pos hB
  have hτ := inverse_integrable_of_support τ hh hτs
  have hconst : ENNReal.ofReal (ρ/2) ≤
      ENNReal.ofReal (plannedCoefficient 28000) * zeroSelection (zeroAtomLaw z₀ η) ρ B →
      ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R),
      ∀ (π : Measure (Gap × Gap)) (μ₀ μ : Measure Gap) [IsFiniteMeasure π]
        [IsFiniteMeasure μ₀] [IsProbabilityMeasure μ],
        (∀ᵐ z ∂π, (z.1:ℝ) ≤ z.2) → π.map Prod.fst = ENNReal.ofReal (1 - z₀) • η →
        μ = π.map Prod.snd + μ₀ →
        RareBudget μ A ρ B ∧
          rareRisk μ A ρ ≤
            ENNReal.ofReal (plannedCoefficient 28000) *
              zeroSelection (zeroAtomLaw z₀ η) ρ B := fun hle =>
    ⟨Unit, inferInstance, constantEstimator (ρ/2), fun π μ₀ μ _ _ _ _ _ _ =>
      ⟨constant_rare_budget μ ρ B (ρ/2), (half_rarity_risk μ ρ hρ.le).trans hle⟩⟩
  rcases lt_or_ge ρ (2048 * E.unresolved) with hz | hz
  · have hf := zero_atom_fallback_rate η σ τ ζ 2 hz0 hρ hρ4 hB hcore htail hτs hζs E hE hz
    rw [plannedCoefficient_eq] at hf
    exact hconst hf
  · have hζ0 : 0 ≤ ζ.real univ := measureReal_nonneg
    have hzE : z₀ + ζ.real univ ≤ E.unresolved := hE.2.2.1
    have hc : 0 < 1 - z₀ := by linarith
    have hρc : ρ ≤ 1 - z₀ := by linarith
    have hr : 0 < conditionalRarity ρ z₀ := div_pos (by linarith) hc
    have hr1 : conditionalRarity ρ z₀ ≤ 1 := (div_le_one hc).mpr (by linarith)
    have ht := (quantileThreshold_properties η hr hr1).1
    have hs : ∀ᵐ d : Gap ∂σ, quantileThreshold η (conditionalRarity ρ z₀) ≤ (d:ℝ) := by
      rw [hcore]
      exact Measure.ae_smul_measure (quantileCore_support η (conditionalRarity ρ z₀)) _
    have hlaw : σ+τ+ζ = ENNReal.ofReal (1 - z₀) • η := by
      rw [add_assoc, htail, hcore, ← smul_add, add_comm, quantileTail_add_core η hr hr1]
    have hzJ : E.unresolved ≤ levelAccuracy ρ (planTerminal hρ B E.unresolved)/8 := by
      have h := planTerminal_unresolved hρ B hz
      linarith [levelAccuracy_pos hρ (planTerminal hρ B E.unresolved)]
    have hrate := zero_atom_plan_rate_dyadic η σ τ ζ hz0 hρ hρ4 hB hcore htail hτs hζs hN E hE
      hz w hlow hup
    rcases le_total (ρ/2) (Real.sqrt (planCertificate ρ (planRates B
        (planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ)
          (planTerminal hρ B E.unresolved)) w))) with hbig | hsmall
    · rw [min_eq_left hbig] at hrate
      exact hconst hrate
    · rw [min_eq_right hsmall] at hrate
      refine ⟨Fin (planTerminal hρ B E.unresolved + 1) → ℕ, inferInstance,
        robustPlanEstimator η σ ht hs hN hc hρc (searchCaps E.resolvedError hE.vanishes hρ)
          (planRates B (planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ)
            (planTerminal hρ B E.unresolved)) w), ?_⟩
      intro π μ₀ μ _ _ _ hup' href hμ
      have hμ₀ := uncoupled_mass η (by linarith) π href μ₀ μ hμ
      have hE₀ : ζ.real univ + μ₀.real univ ≤ E.unresolved := by
        rw [hμ₀]
        linarith
      have hzρ : ζ.real univ ≤ ρ := by linarith
      have hk := robust_planCost_pos η σ τ ζ hc hlaw π hup' href μ₀ μ hμ ht hs hN hτ hρ hρc hzρ
        E hE₀ (searchCaps E.resolvedError hE.vanishes hρ) (planTerminal hρ B E.unresolved)
      have hw : ∀ i, 0 < w i := fun i =>
        lt_of_lt_of_le (Real.sqrt_pos.mpr (div_pos
          (mul_pos (by norm_num) (levelAccuracy_pos hρ i.val)) (hk i))) (hlow i)
      obtain ⟨hb, hrisk⟩ := robust_searched_plan_valid η σ τ ζ hc hlaw π hup' href μ₀ μ hμ ht hs
        hN hτ hρ hρc hB E hE₀ hE.vanishes hzJ w hw
      exact ⟨hb, hrisk.trans hrate⟩

/-- **The exact planner's estimator under every true law above the
reference.** For every reference law `α = z₀ δ₀ + (1 - z₀) η` with
`0 ≤ z₀ < ρ ≤ 1/4` and every budget `B > 0`, there is one estimator that
observes flips only and, under every true law coupled above `α`, spends at
most `B` in expectation and has root-mean-square risk at most
`C₀ K_α(B)`, over all rare priors. It is the output of the planner run on
the zero-atom quantile design of `α` with the exact integrals and the
optimal weights. -/
theorem robust_planner_rate (η : Measure Gap) [IsProbabilityMeasure η] {z₀ ρ B : ℝ}
    (hz0 : 0 ≤ z₀) (hzρ : z₀ < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) :
    ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R),
      ∀ (π : Measure (Gap × Gap)) (μ₀ μ : Measure Gap) [IsFiniteMeasure π]
        [IsFiniteMeasure μ₀] [IsProbabilityMeasure μ],
        (∀ᵐ z ∂π, (z.1:ℝ) ≤ z.2) → π.map Prod.fst = ENNReal.ofReal (1 - z₀) • η →
        μ = π.map Prod.snd + μ₀ →
        RareBudget μ A ρ B ∧
          rareRisk μ A ρ ≤
            ENNReal.ofReal (plannedCoefficient 28000) * zeroSelection (zeroAtomLaw z₀ η) ρ B := by
  have hρ : 0 < ρ := lt_of_le_of_lt hz0 hzρ
  have hc : 0 < 1 - z₀ := by linarith
  have hr : 0 < conditionalRarity ρ z₀ := div_pos (by linarith) hc
  have hr1 : conditionalRarity ρ z₀ ≤ 1 := (div_le_one hc).mpr (by linarith)
  have ht := (quantileThreshold_properties η hr hr1).1
  obtain ⟨σ, τ, ζ, hσf, hτf, hζf, hcore, htail, hτs, hζs⟩ :=
    exists_zero_atom_split η hzρ (by linarith) B
  obtain ⟨N, hN⟩ : ∃ N : ℕ, bandEdge N < quantileThreshold η (conditionalRarity ρ z₀) := by
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one ht (by norm_num : (2:ℝ)⁻¹ < 1)
    exact ⟨N, (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ N)).trans_lt hN⟩
  exact robust_zero_atom_planner_rate η σ τ ζ hz0 hρ hρ4 hB hcore htail hτs hζs hN
    (SplitEnclosure.exactZero σ τ ζ N hz0) (SplitEnclosure.exactZero_tight σ τ ζ N hz0) _
    (fun i => le_rfl) (fun i => by linarith [Real.sqrt_nonneg (17*levelAccuracy ρ i.val /
      planCost (SplitEnclosure.exactZero σ τ ζ N hz0) ρ
        (searchCaps (SplitEnclosure.exactZero σ τ ζ N hz0).resolvedError
          (SplitEnclosure.exactZero_tight σ τ ζ N hz0).vanishes hρ)
        (planTerminal hρ B (SplitEnclosure.exactZero σ τ ζ N hz0).unresolved) i)])

end ThresholdHC.RobustContinuation
