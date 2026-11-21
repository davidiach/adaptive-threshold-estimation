import ThresholdHC.RobustContinuation.CDFBridge
import ThresholdHC.KnownLawPlanner.PlannerEstimator

/-! Target statements for the literal forms of the robust continuation.

Source: `paper/v6/arbitrary-law-adaptation.tex`, subsection
`sec:arbitrary-law-adaptation`, subsubsection `Robust use of the known-law
estimator` (lines 266-321; the same text is section 4 of
`docs/ARBITRARY_LAW_ADAPTATION.md`, lines 294-353). The subsubsection has no
LaTeX label of its own.
* Lines 276-278: couple `D₀ ∼ α` and `D₁ ∼ μ` with `D₀ ≤ D₁`, choose the
  sign by the true sign law at `D₁`; its conditional law at `D₀` defines an
  admissible reference sign allocation with the same positive fraction.
* Lines 294-303, display `(UA15)`: with `T_bank^s` the first correct-sign
  bank crossing and `T_ord^s` the first correct ordinary boundary crossing,
  capped at the terminal length, wrong crossings ignored, both times decrease
  under the sign-directed coupling and the race work is at most
  `2 min(T_bank,1^s, T_ord,1^s) ≤ 2 min(T_bank,0^s, T_ord,0^s)`.
* Lines 315-316: the global rarity surcharge uses the induced reference sign
  allocation, whose total positive mass is still at most `ρ`.
* The estimator is chosen from the reference alone, before the true law
  (`lean/ThresholdHC/RobustContinuation/RobustPlannerOutput.lean`, module
  docstring). The audited `robust_planner_rate` and `cdf_robust_planner_rate`
  state this with an existential estimator; here the estimators are named.

Formalization choices.
* (i) The planner returns either the named plan estimator
  `robustQuantilePlanEstimator` (seed type `Fin (J+1) → ℕ`) or the constant
  `ρ/2` (seed type `Unit`). The dispatch predicate is
  `KnownLawPlanner.RunsPlan`, computed from the reference design alone. The
  statements have the two-branch form of `KnownLawPlanner.exact_planner_output`:
  they do not produce a single estimator object of one seed type.
* (i-a) and (i-b) keep the split `σ τ ζ N` as a parameter constrained by the
  quantile-split hypotheses and assume `z₀ < ρ`, which the named plan branch
  needs to build the quantile threshold. The case `ρ ≤ z₀` is covered by
  `RobustLargeAtomOutputStatement`: the constant `ρ/2` meets the bound.
* (i-c) names the split as well: `robustCore`, `robustUpperTail`,
  `robustLowerTail` (the restrictions of the scaled quantile tail to gaps at
  least the budget scale and to the complement) and `robustSplitBands`, the
  least band index below the quantile threshold. The enclosure is the exact
  zero-atom enclosure and the weights are the optimal ones. Only `η z₀ ρ B`
  and the hypotheses `0 ≤ z₀ < ρ ≤ 1/4`, `0 < B` remain.
* (ii) Gaps are positive, so the allocation `inducedSignLaw π q` lives on the
  positive reference part `η`; it is the Radon-Nikodym version of the
  conditional law of `q(D₁)` given `D₀`, truncated at one, and it is
  characterized by the integral identity for every measurable `F`. The
  reference zero atom carries the uncoupled part `μ₀`, so the same positive
  fraction reads `(1 - z₀) signMean η q₀ + ∫ q dμ₀ = signMean μ q`.
  Admissibility is `RarePrior η (ρ/(1 - z₀)) q₀`, together with the sharp
  form `(1 - z₀) signMean η q₀ + ∫ q dμ₀ ≤ ρ`. The global surcharge itself is
  not re-derived.
* (iii) The statements are pathwise. `bankCorrectTime` is `ℕ∞`-valued and
  uncapped (`⊤` when no correct crossing occurs) on the even flips;
  `ordinaryCorrectTime` is capped at `2^L` through the terminal check, uses
  the boundary `threshold1 (cap k) (cap L)` of `classifierStop`, and reads the
  odd flips. Times count rounds and `raceCost = 2 · raceRounds` counts flips.
  The sign-directed order is `SignOrdered`. The coupled forms are stated for
  success parameters `p₀ p` ordered by the sign, with common uniform tapes,
  and specialized to gaps `d₀ ≤ d` and to the fair coin of the reference zero
  atom. The integrated bound of the ordinary tail and the recovery of the
  level-work certificate by integrating `(UA15)` are not stated. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace ThresholdHC.RobustContinuationForms
open ThresholdHC.Tier6 (Gap SignLaw AdaptiveEstimator signMean)
open ThresholdHC.EntropyTailUpper ThresholdHC.RareAboveTwo
open ThresholdHC.EntropyTailQuantile ThresholdHC.EntropyTailAssembly
open ThresholdHC.EntropyTailExecution ThresholdHC.KnownLawPlanner
open ThresholdHC.ArbitraryLawAdaptation ThresholdHC.RobustContinuation

/-! ### (i) The named robust planner -/

/-- The plan branch of the robust planner, named. It is built from the
reference design alone: the quantile threshold of `η` at the conditional
rarity, the band weights of `σ`, the cap search of the enclosure's envelope,
its terminal level and the counts from the weights `w`. -/
def robustQuantilePlanEstimator (η : Measure Gap) [IsProbabilityMeasure η]
    (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] {z₀ ρ : ℝ} {N : ℕ}
    (hz0 : 0 ≤ z₀) (hzρ : z₀ < ρ) (hρ4 : ρ ≤ 1/4)
    (hcore : σ = ENNReal.ofReal (1 - z₀) • quantileCore η (conditionalRarity ρ z₀))
    (hN : bandEdge N < quantileThreshold η (conditionalRarity ρ z₀))
    (E : SplitEnclosure σ τ ζ N) (hvan : EnvelopeVanishes E.resolvedError) (B : ℝ)
    (w : Fin (planTerminal (hz0.trans_lt hzρ) B E.unresolved + 1) → ℝ) :
    AdaptiveEstimator (Fin (planTerminal (hz0.trans_lt hzρ) B E.unresolved + 1) → ℕ) :=
  robustPlanEstimator η σ
    (quantileThreshold_properties η (ρ := conditionalRarity ρ z₀)
      (show 0 < conditionalRarity ρ z₀ from div_pos (show (0:ℝ) < ρ - z₀ by linarith)
        (show (0:ℝ) < 1 - z₀ by linarith))
      (show conditionalRarity ρ z₀ ≤ 1 from
        (div_le_one (show (0:ℝ) < 1 - z₀ by linarith)).mpr (by linarith))).1
    (by
      rw [hcore]
      exact Measure.ae_smul_measure (quantileCore_support η (conditionalRarity ρ z₀)) _)
    hN (c := 1 - z₀) (show (0:ℝ) < 1 - z₀ by linarith) (show ρ ≤ 1 - z₀ by linarith)
    (searchCaps E.resolvedError hvan (hz0.trans_lt hzρ))
    (planRates B (planCost E ρ (searchCaps E.resolvedError hvan (hz0.trans_lt hzρ))
      (planTerminal (hz0.trans_lt hzρ) B E.unresolved)) w)

/-- The optimal weights `√(17 δ_l / k_l)` of the exact zero-atom enclosure. -/
def robustExactWeights (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ]
    {z₀ ρ : ℝ} (hz0 : 0 ≤ z₀) (hρ : 0 < ρ) (B : ℝ) (N : ℕ) :
    Fin (planTerminal hρ B (SplitEnclosure.exactZero σ τ ζ N hz0).unresolved + 1) → ℝ :=
  fun i => Real.sqrt (17 * levelAccuracy ρ i.val /
    planCost (SplitEnclosure.exactZero σ τ ζ N hz0) ρ
      (searchCaps (SplitEnclosure.exactZero σ τ ζ N hz0).resolvedError
        (SplitEnclosure.exactZero_tight σ τ ζ N hz0).vanishes hρ)
      (planTerminal hρ B (SplitEnclosure.exactZero σ τ ζ N hz0).unresolved) i)

/-- The core of the named reference design: `1 - z₀` times the quantile core
of `η` at the conditional rarity. -/
def robustCore (η : Measure Gap) (z₀ ρ : ℝ) : Measure Gap :=
  ENNReal.ofReal (1 - z₀) • quantileCore η (conditionalRarity ρ z₀)

/-- The resolved tail of the named reference design: the scaled quantile tail
on gaps at least the budget scale. -/
def robustUpperTail (η : Measure Gap) (z₀ ρ B : ℝ) : Measure Gap :=
  (ENNReal.ofReal (1 - z₀) • quantileTail η (conditionalRarity ρ z₀)).restrict
    {d : Gap | budgetScale B ≤ (d:ℝ)}

/-- The positive unresolved part of the named reference design: the scaled
quantile tail on gaps below the budget scale. -/
def robustLowerTail (η : Measure Gap) (z₀ ρ B : ℝ) : Measure Gap :=
  (ENNReal.ofReal (1 - z₀) • quantileTail η (conditionalRarity ρ z₀)).restrict
    {d : Gap | budgetScale B ≤ (d:ℝ)}ᶜ

instance robustCore_finite (η : Measure Gap) [IsFiniteMeasure η] (z₀ ρ : ℝ) :
    IsFiniteMeasure (robustCore η z₀ ρ) := by
  have : IsFiniteMeasure (quantileCore η (conditionalRarity ρ z₀)) :=
    isFiniteMeasure_of_le η Measure.sub_le
  exact (quantileCore η (conditionalRarity ρ z₀)).smul_finite ENNReal.ofReal_ne_top

instance robustUpperTail_finite (η : Measure Gap) [IsFiniteMeasure η] (z₀ ρ B : ℝ) :
    IsFiniteMeasure (robustUpperTail η z₀ ρ B) := by
  have : IsFiniteMeasure (ENNReal.ofReal (quantileBoundaryFraction η (conditionalRarity ρ z₀)) •
      η.restrict {d : Gap | (d:ℝ) = quantileThreshold η (conditionalRarity ρ z₀)}) :=
    Measure.smul_finite _ ENNReal.ofReal_ne_top
  have : IsFiniteMeasure (quantileTail η (conditionalRarity ρ z₀)) := by
    unfold quantileTail
    infer_instance
  have : IsFiniteMeasure (ENNReal.ofReal (1 - z₀) • quantileTail η (conditionalRarity ρ z₀)) :=
    Measure.smul_finite _ ENNReal.ofReal_ne_top
  unfold robustUpperTail
  infer_instance

instance robustLowerTail_finite (η : Measure Gap) [IsFiniteMeasure η] (z₀ ρ B : ℝ) :
    IsFiniteMeasure (robustLowerTail η z₀ ρ B) := by
  have : IsFiniteMeasure (ENNReal.ofReal (quantileBoundaryFraction η (conditionalRarity ρ z₀)) •
      η.restrict {d : Gap | (d:ℝ) = quantileThreshold η (conditionalRarity ρ z₀)}) :=
    Measure.smul_finite _ ENNReal.ofReal_ne_top
  have : IsFiniteMeasure (quantileTail η (conditionalRarity ρ z₀)) := by
    unfold quantileTail
    infer_instance
  have : IsFiniteMeasure (ENNReal.ofReal (1 - z₀) • quantileTail η (conditionalRarity ρ z₀)) :=
    Measure.smul_finite _ ENNReal.ofReal_ne_top
  unfold robustLowerTail
  infer_instance

/-- The band count of the named reference design: the least `N` with
`bandEdge N` below the quantile threshold of `η` at the conditional rarity. -/
def robustSplitBands (η : Measure Gap) [IsProbabilityMeasure η] {z₀ ρ : ℝ} (hzρ : z₀ < ρ)
    (hρ4 : ρ ≤ 1/4) : ℕ :=
  Nat.find (exists_bandEdge_lt η (ρ := conditionalRarity ρ z₀)
    (show 0 < conditionalRarity ρ z₀ from div_pos (show (0:ℝ) < ρ - z₀ by linarith)
        (show (0:ℝ) < 1 - z₀ by linarith))
      (show conditionalRarity ρ z₀ ≤ 1 from
        (div_le_one (show (0:ℝ) < 1 - z₀ by linarith)).mpr (by linarith)))

/-- The exact zero-atom enclosure of the named reference design. -/
def robustPlannerEnclosure (η : Measure Gap) [IsProbabilityMeasure η] {z₀ ρ : ℝ} (B : ℝ)
    (hz0 : 0 ≤ z₀) (hzρ : z₀ < ρ) (hρ4 : ρ ≤ 1/4) :
    SplitEnclosure (robustCore η z₀ ρ) (robustUpperTail η z₀ ρ B) (robustLowerTail η z₀ ρ B)
      (robustSplitBands η hzρ hρ4) :=
  SplitEnclosure.exactZero (robustCore η z₀ ρ) (robustUpperTail η z₀ ρ B)
    (robustLowerTail η z₀ ρ B) (robustSplitBands η hzρ hρ4) hz0

/-- The planner's decision on the named reference design with the exact
integrals and the optimal weights. -/
def RobustRunsPlan (η : Measure Gap) [IsProbabilityMeasure η] {z₀ ρ : ℝ} (B : ℝ)
    (hz0 : 0 ≤ z₀) (hzρ : z₀ < ρ) (hρ4 : ρ ≤ 1/4) : Prop :=
  RunsPlan (robustPlannerEnclosure η B hz0 hzρ hρ4) (hz0.trans_lt hzρ)
    (SplitEnclosure.exactZero_tight (robustCore η z₀ ρ) (robustUpperTail η z₀ ρ B)
      (robustLowerTail η z₀ ρ B) (robustSplitBands η hzρ hρ4) hz0).vanishes B
    (robustExactWeights (robustCore η z₀ ρ) (robustUpperTail η z₀ ρ B)
      (robustLowerTail η z₀ ρ B) hz0 (hz0.trans_lt hzρ) B (robustSplitBands η hzρ hρ4))

/-- The plan branch of the planner on the named reference design, named. -/
def robustPlannerPlan (η : Measure Gap) [IsProbabilityMeasure η] {z₀ ρ : ℝ} (B : ℝ)
    (hz0 : 0 ≤ z₀) (hzρ : z₀ < ρ) (hρ4 : ρ ≤ 1/4) :
    AdaptiveEstimator (Fin (planTerminal (hz0.trans_lt hzρ) B
      (robustPlannerEnclosure η B hz0 hzρ hρ4).unresolved + 1) → ℕ) :=
  robustQuantilePlanEstimator η (robustCore η z₀ ρ) (robustUpperTail η z₀ ρ B)
    (robustLowerTail η z₀ ρ B) (N := robustSplitBands η hzρ hρ4) hz0 hzρ hρ4 rfl
    (Nat.find_spec (exists_bandEdge_lt η (ρ := conditionalRarity ρ z₀)
      (show 0 < conditionalRarity ρ z₀ from div_pos (show (0:ℝ) < ρ - z₀ by linarith)
        (show (0:ℝ) < 1 - z₀ by linarith))
      (show conditionalRarity ρ z₀ ≤ 1 from
        (div_le_one (show (0:ℝ) < 1 - z₀ by linarith)).mpr (by linarith))))
    (robustPlannerEnclosure η B hz0 hzρ hρ4)
    (SplitEnclosure.exactZero_tight (robustCore η z₀ ρ) (robustUpperTail η z₀ ρ B)
      (robustLowerTail η z₀ ρ B) (robustSplitBands η hzρ hρ4) hz0).vanishes B
    (robustExactWeights (robustCore η z₀ ρ) (robustUpperTail η z₀ ρ B)
      (robustLowerTail η z₀ ρ B) hz0 (hz0.trans_lt hzρ) B (robustSplitBands η hzρ hρ4))

/-- (i-a) The named robust planner, for a tight enclosure and weights within a
factor two of the optimal ones, under every true law coupled above the
reference. In the plan branch the named plan estimator, and otherwise the
constant `ρ/2`, has budget `B` and root-mean-square risk at most `C₀ K_α(B)`. -/
def RobustTightPlannerOutputStatement : Prop :=
  ∀ (η : Measure Gap) [IsProbabilityMeasure η] (σ τ ζ : Measure Gap)
    [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] {z₀ ρ B : ℝ} {N : ℕ}
    (hz0 : 0 ≤ z₀) (hzρ : z₀ < ρ) (hρ4 : ρ ≤ 1/4), 0 < B →
    ∀ (hcore : σ = ENNReal.ofReal (1 - z₀) • quantileCore η (conditionalRarity ρ z₀)),
    τ+ζ = ENNReal.ofReal (1 - z₀) • quantileTail η (conditionalRarity ρ z₀) →
    (∀ᵐ d : Gap ∂τ, budgetScale B ≤ (d:ℝ)) → (∀ᵐ d : Gap ∂ζ, (d:ℝ) ≤ budgetScale B) →
    ∀ (hN : bandEdge N < quantileThreshold η (conditionalRarity ρ z₀))
      (E : SplitEnclosure σ τ ζ N) (hE : E.Tight (z₀ + ζ.real univ))
      (w : Fin (planTerminal (hz0.trans_lt hzρ) B E.unresolved + 1) → ℝ),
    (∀ i, Real.sqrt (17*levelAccuracy ρ i.val / planCost E ρ
        (searchCaps E.resolvedError hE.vanishes (hz0.trans_lt hzρ))
        (planTerminal (hz0.trans_lt hzρ) B E.unresolved) i) ≤ w i) →
    (∀ i, w i ≤ 2 * Real.sqrt (17*levelAccuracy ρ i.val / planCost E ρ
        (searchCaps E.resolvedError hE.vanishes (hz0.trans_lt hzρ))
        (planTerminal (hz0.trans_lt hzρ) B E.unresolved) i)) →
    (RunsPlan E (hz0.trans_lt hzρ) hE.vanishes B w →
      ∀ (π : Measure (Gap × Gap)) (μ₀ μ : Measure Gap) [IsFiniteMeasure π]
        [IsFiniteMeasure μ₀] [IsProbabilityMeasure μ],
        (∀ᵐ z ∂π, (z.1:ℝ) ≤ z.2) → π.map Prod.fst = ENNReal.ofReal (1 - z₀) • η →
        μ = π.map Prod.snd + μ₀ →
        RareBudget μ (robustQuantilePlanEstimator η σ τ ζ hz0 hzρ hρ4 hcore hN E hE.vanishes B w)
            ρ B ∧
          rareRisk μ (robustQuantilePlanEstimator η σ τ ζ hz0 hzρ hρ4 hcore hN E hE.vanishes B w)
              ρ ≤
            ENNReal.ofReal (plannedCoefficient 28000) * zeroSelection (zeroAtomLaw z₀ η) ρ B) ∧
    (¬ RunsPlan E (hz0.trans_lt hzρ) hE.vanishes B w →
      ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
        RareBudget μ (constantEstimator (ρ/2)) ρ B ∧
          rareRisk μ (constantEstimator (ρ/2)) ρ ≤
            ENNReal.ofReal (plannedCoefficient 28000) * zeroSelection (zeroAtomLaw z₀ η) ρ B)

/-- (i-b) The same as (i-a) with the coupling replaced by CDF domination of
the true law by the reference law `α = z₀ δ₀ + (1 - z₀) η`. -/
def CDFRobustTightPlannerOutputStatement : Prop :=
  ∀ (η : Measure Gap) [IsProbabilityMeasure η] (σ τ ζ : Measure Gap)
    [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] {z₀ ρ B : ℝ} {N : ℕ}
    (hz0 : 0 ≤ z₀) (hzρ : z₀ < ρ) (hρ4 : ρ ≤ 1/4), 0 < B →
    ∀ (hcore : σ = ENNReal.ofReal (1 - z₀) • quantileCore η (conditionalRarity ρ z₀)),
    τ+ζ = ENNReal.ofReal (1 - z₀) • quantileTail η (conditionalRarity ρ z₀) →
    (∀ᵐ d : Gap ∂τ, budgetScale B ≤ (d:ℝ)) → (∀ᵐ d : Gap ∂ζ, (d:ℝ) ≤ budgetScale B) →
    ∀ (hN : bandEdge N < quantileThreshold η (conditionalRarity ρ z₀))
      (E : SplitEnclosure σ τ ζ N) (hE : E.Tight (z₀ + ζ.real univ))
      (w : Fin (planTerminal (hz0.trans_lt hzρ) B E.unresolved + 1) → ℝ),
    (∀ i, Real.sqrt (17*levelAccuracy ρ i.val / planCost E ρ
        (searchCaps E.resolvedError hE.vanishes (hz0.trans_lt hzρ))
        (planTerminal (hz0.trans_lt hzρ) B E.unresolved) i) ≤ w i) →
    (∀ i, w i ≤ 2 * Real.sqrt (17*levelAccuracy ρ i.val / planCost E ρ
        (searchCaps E.resolvedError hE.vanishes (hz0.trans_lt hzρ))
        (planTerminal (hz0.trans_lt hzρ) B E.unresolved) i)) →
    (RunsPlan E (hz0.trans_lt hzρ) hE.vanishes B w →
      ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
        (∀ x, cdf (μ.map Subtype.val) x ≤ cdf (zeroAtomLaw z₀ η) x) →
        RareBudget μ (robustQuantilePlanEstimator η σ τ ζ hz0 hzρ hρ4 hcore hN E hE.vanishes B w)
            ρ B ∧
          rareRisk μ (robustQuantilePlanEstimator η σ τ ζ hz0 hzρ hρ4 hcore hN E hE.vanishes B w)
              ρ ≤
            ENNReal.ofReal (plannedCoefficient 28000) * zeroSelection (zeroAtomLaw z₀ η) ρ B) ∧
    (¬ RunsPlan E (hz0.trans_lt hzρ) hE.vanishes B w →
      ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
        RareBudget μ (constantEstimator (ρ/2)) ρ B ∧
          rareRisk μ (constantEstimator (ρ/2)) ρ ≤
            ENNReal.ofReal (plannedCoefficient 28000) * zeroSelection (zeroAtomLaw z₀ η) ρ B)

/-- (i-c) The named planner on the named reference design, with the exact
zero-atom integrals and the optimal weights, under every CDF-dominated true
law: a non-existential form of `cdf_robust_planner_rate`. -/
def RobustExactPlannerOutputStatement : Prop :=
  ∀ (η : Measure Gap) [IsProbabilityMeasure η] {z₀ ρ B : ℝ}
    (hz0 : 0 ≤ z₀) (hzρ : z₀ < ρ) (hρ4 : ρ ≤ 1/4), 0 < B →
    (RobustRunsPlan η B hz0 hzρ hρ4 →
      ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
        (∀ x, cdf (μ.map Subtype.val) x ≤ cdf (zeroAtomLaw z₀ η) x) →
        RareBudget μ (robustPlannerPlan η B hz0 hzρ hρ4) ρ B ∧
          rareRisk μ (robustPlannerPlan η B hz0 hzρ hρ4) ρ ≤
            ENNReal.ofReal (plannedCoefficient 28000) * zeroSelection (zeroAtomLaw z₀ η) ρ B) ∧
    (¬ RobustRunsPlan η B hz0 hzρ hρ4 →
      ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
        RareBudget μ (constantEstimator (ρ/2)) ρ B ∧
          rareRisk μ (constantEstimator (ρ/2)) ρ ≤
            ENNReal.ofReal (plannedCoefficient 28000) * zeroSelection (zeroAtomLaw z₀ η) ρ B)

/-- (i-a, large atom) When the reference mass at zero is at least `ρ`, the
constant `ρ/2` has budget `B` and risk at most `C₀ K_α(B)` under every true
law. -/
def RobustLargeAtomOutputStatement : Prop :=
  ∀ (η : Measure Gap) [IsProbabilityMeasure η] {z₀ ρ B : ℝ}, 0 < ρ → 0 < B → ρ ≤ z₀ →
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
      RareBudget μ (constantEstimator (ρ/2)) ρ B ∧
        rareRisk μ (constantEstimator (ρ/2)) ρ ≤
          ENNReal.ofReal (plannedCoefficient 28000) * zeroSelection (zeroAtomLaw z₀ η) ρ B

/-! ### (ii) The induced reference sign allocation -/

/-- The positive part of the sign law at the true gap, carried to the
reference gap: `B ↦ ∫_{D₀ ∈ B} q(D₁) dπ`. -/
def inducedSignMeasure (π : Measure (Gap × Gap)) (q : SignLaw) : Measure Gap :=
  (π.withDensity (fun z => ENNReal.ofReal (q.val z.2))).map Prod.fst

/-- The induced reference sign allocation: the conditional law of the sign at
the reference gap, as the Radon-Nikodym derivative of `inducedSignMeasure`
with respect to the reference marginal, truncated at one. -/
def inducedSignLaw (π : Measure (Gap × Gap)) (q : SignLaw) : SignLaw :=
  ⟨fun d => min 1 ((inducedSignMeasure π q).rnDeriv (π.map Prod.fst) d).toReal,
    measurable_const.min (Measure.measurable_rnDeriv _ _).ennreal_toReal,
    fun _ => ⟨le_min zero_le_one ENNReal.toReal_nonneg, min_le_left _ _⟩⟩

/-- (ii) The induced allocation is the conditional law of the true sign at the
reference gap, it has the same positive fraction once the uncoupled part is
added, and it is admissible for the reference. -/
def InducedSignAllocationStatement : Prop :=
  ∀ (η : Measure Gap) [IsProbabilityMeasure η] {z₀ ρ : ℝ}, 0 ≤ z₀ → z₀ < 1 →
  ∀ (π : Measure (Gap × Gap)) (μ₀ μ : Measure Gap) [IsFiniteMeasure π]
    [IsFiniteMeasure μ₀] [IsProbabilityMeasure μ],
    π.map Prod.fst = ENNReal.ofReal (1 - z₀) • η → μ = π.map Prod.snd + μ₀ →
    ∀ q : SignLaw,
      (∀ F : Gap → ℝ, Measurable F →
        (∫ z, q.val z.2 * F z.1 ∂π) = (1 - z₀) * ∫ d, (inducedSignLaw π q).val d * F d ∂η) ∧
      (1 - z₀) * signMean η (inducedSignLaw π q).val + (∫ d, q.val d ∂μ₀) = signMean μ q.val ∧
      (RarePrior μ ρ q →
        (1 - z₀) * signMean η (inducedSignLaw π q).val + (∫ d, q.val d ∂μ₀) ≤ ρ ∧
          RarePrior η (ρ / (1 - z₀)) (inducedSignLaw π q))

/-! ### (iii) Correct-sign crossing times -/

/-- A correct-sign bank crossing at round `n` of the even flips: the positive
bank for a positive coin, the negative bank for a negative one. Crossings of
the wrong sign are ignored. -/
def bankCorrectHit (neg pos : PrefixTest) (s : Bool) (ω : ℕ → Bool) (n : ℕ) : Prop :=
  cond s (pos n (Tier2.tapePrefix n (parityTape 0 ω)))
    (neg n (Tier2.tapePrefix n (parityTape 0 ω)))

/-- `T_bank^s`: the first correct-sign bank crossing, uncapped, `⊤` when there
is none. -/
def bankCorrectTime (neg pos : PrefixTest) (s : Bool) (ω : ℕ → Bool) : ℕ∞ :=
  ⨅ (n : ℕ) (_ : bankCorrectHit neg pos s ω n), (n : ℕ∞)

/-- A correct crossing of the ordinary boundary at check `k`, with the
boundary `threshold1 (cap k) (cap L)` of `classifierStop`. -/
def ordinaryCorrectCross (s : Bool) (L : ℕ) (m : ℕ → ℝ) (k : ℕ) : Prop :=
  cond s (Tier2.Model.threshold1 (Uniform713.cap k) (Uniform713.cap L) < m k - 1/2)
    (Tier2.Model.threshold1 (Uniform713.cap k) (Uniform713.cap L) < 1/2 - m k)

/-- The check of the first correct ordinary crossing, capped at the terminal
check `L`. -/
def ordinaryCorrectLevel (s : Bool) (L : ℕ) (m : ℕ → ℝ) : ℕ := by
  classical
  exact Nat.find (show ∃ k, L ≤ k ∨ ordinaryCorrectCross s L m k from ⟨L, Or.inl le_rfl⟩)

/-- `T_ord^s`: the number of flips read by the ordinary classifier at its first
correct crossing, capped at the terminal length `2^L`. -/
def ordinaryCorrectTime (s : Bool) (L : ℕ) (ω : ℕ → Bool) : ℕ :=
  2 ^ ordinaryCorrectLevel s L (fun k => Uniform713.dyadicMean Tier2.observations k ω)

/-- The sign-directed order: more heads for a positive coin, fewer heads for
a negative one. -/
def SignOrdered (s : Bool) (ω₀ ω₁ : ℕ → Bool) : Prop := cond s (ω₀ ≤ ω₁) (ω₁ ≤ ω₀)

/-- (iii-a) Pathwise, the race work is at most twice the earlier of the two
correct-sign crossing times, for either sign. -/
def CorrectTimeRaceBoundStatement : Prop :=
  ∀ (neg pos : PrefixTest) (L : ℕ) (s : Bool) (ω : ℕ → Bool),
    (raceCost neg pos L ω : ℕ∞) ≤
      2 * min (bankCorrectTime neg pos s ω) (ordinaryCorrectTime s L (parityTape 1 ω) : ℕ∞)

/-- (iii-b) Both correct-sign crossing times decrease in the sign-directed
order, for a downward negative test and an upward positive test. -/
def CorrectTimeAntitoneStatement : Prop :=
  ∀ (neg pos : PrefixTest), DownwardTest neg → UpwardTest pos →
  ∀ (L : ℕ) (s : Bool) (ω₀ ω₁ : ℕ → Bool), SignOrdered s ω₀ ω₁ →
    bankCorrectTime neg pos s ω₁ ≤ bankCorrectTime neg pos s ω₀ ∧
      ordinaryCorrectTime s L (parityTape 1 ω₁) ≤ ordinaryCorrectTime s L (parityTape 1 ω₀)

/-- (iii-c) `(UA15)` under the common-uniform tape coupling, for success
parameters `p₀` of the reference coin and `p` of the true coin ordered by the
sign. -/
def CoupledCorrectTimeWorkStatement : Prop :=
  ∀ (neg pos : PrefixTest), DownwardTest neg → UpwardTest pos →
  ∀ (L : ℕ) (s : Bool) (p₀ p : unitInterval), cond s ((p₀:ℝ) ≤ p) ((p:ℝ) ≤ p₀) →
  ∀ u : ℕ → ℝ,
    (raceCost neg pos L (CriticalEntropy.uniformCoinTape p u) : ℕ∞) ≤
      2 * min (bankCorrectTime neg pos s (CriticalEntropy.uniformCoinTape p u))
        (ordinaryCorrectTime s L (parityTape 1 (CriticalEntropy.uniformCoinTape p u)) : ℕ∞) ∧
    2 * min (bankCorrectTime neg pos s (CriticalEntropy.uniformCoinTape p u))
        (ordinaryCorrectTime s L (parityTape 1 (CriticalEntropy.uniformCoinTape p u)) : ℕ∞) ≤
      2 * min (bankCorrectTime neg pos s (CriticalEntropy.uniformCoinTape p₀ u))
        (ordinaryCorrectTime s L (parityTape 1 (CriticalEntropy.uniformCoinTape p₀ u)) : ℕ∞)

/-- (iii-c, gaps) `(UA15)` for a reference gap `d₀` below the true gap `d`,
both coins of the true sign `s`. -/
def CoupledGapCorrectTimeWorkStatement : Prop :=
  ∀ (neg pos : PrefixTest), DownwardTest neg → UpwardTest pos →
  ∀ (L : ℕ) (s : Bool) (d₀ d : Gap), (d₀:ℝ) ≤ d → ∀ u : ℕ → ℝ,
    (raceCost neg pos L
        (CriticalEntropy.uniformCoinTape (ObservableSimulation.gapParameter s d) u) : ℕ∞) ≤
      2 * min (bankCorrectTime neg pos s
          (CriticalEntropy.uniformCoinTape (ObservableSimulation.gapParameter s d) u))
        (ordinaryCorrectTime s L (parityTape 1
          (CriticalEntropy.uniformCoinTape (ObservableSimulation.gapParameter s d) u)) : ℕ∞) ∧
    2 * min (bankCorrectTime neg pos s
          (CriticalEntropy.uniformCoinTape (ObservableSimulation.gapParameter s d) u))
        (ordinaryCorrectTime s L (parityTape 1
          (CriticalEntropy.uniformCoinTape (ObservableSimulation.gapParameter s d) u)) : ℕ∞) ≤
      2 * min (bankCorrectTime neg pos s
          (CriticalEntropy.uniformCoinTape (ObservableSimulation.gapParameter s d₀) u))
        (ordinaryCorrectTime s L (parityTape 1
          (CriticalEntropy.uniformCoinTape (ObservableSimulation.gapParameter s d₀) u)) : ℕ∞)

/-- (iii-c, zero atom) `(UA15)` for the reference zero atom: the reference
coin is fair, the true coin has gap `d` and sign `s`. -/
def CoupledZeroAtomCorrectTimeWorkStatement : Prop :=
  ∀ (neg pos : PrefixTest), DownwardTest neg → UpwardTest pos →
  ∀ (L : ℕ) (s : Bool) (d : Gap) (p₀ : unitInterval), (p₀:ℝ) = 1/2 → ∀ u : ℕ → ℝ,
    (raceCost neg pos L
        (CriticalEntropy.uniformCoinTape (ObservableSimulation.gapParameter s d) u) : ℕ∞) ≤
      2 * min (bankCorrectTime neg pos s
          (CriticalEntropy.uniformCoinTape (ObservableSimulation.gapParameter s d) u))
        (ordinaryCorrectTime s L (parityTape 1
          (CriticalEntropy.uniformCoinTape (ObservableSimulation.gapParameter s d) u)) : ℕ∞) ∧
    2 * min (bankCorrectTime neg pos s
          (CriticalEntropy.uniformCoinTape (ObservableSimulation.gapParameter s d) u))
        (ordinaryCorrectTime s L (parityTape 1
          (CriticalEntropy.uniformCoinTape (ObservableSimulation.gapParameter s d) u)) : ℕ∞) ≤
      2 * min (bankCorrectTime neg pos s (CriticalEntropy.uniformCoinTape p₀ u))
        (ordinaryCorrectTime s L (parityTape 1 (CriticalEntropy.uniformCoinTape p₀ u)) : ℕ∞)

/-- (iii-d) `(UA15)` for the level race of the reference design: negative bank
`negativeBankTest w ε_l`, positive bank `positiveBankTest η w (ρ ε_l / c)` and
terminal check `2 κ_l`, with the cost of `robustFamily` on the left. -/
def ReferenceRaceCorrectTimeWorkStatement : Prop :=
  ∀ (η : Measure Gap) [IsProbabilityMeasure η] (w : ℕ → ℝ≥0) (hw : HasSum w 1) {c : ℝ}
    (hc : 0 < c) {ρ : ℝ} (hρc : ρ ≤ c) (κ : ℕ → ℕ) (l : ℕ) (s : Bool) (p₀ p : unitInterval),
    cond s ((p₀:ℝ) ≤ p) ((p:ℝ) ≤ p₀) → ∀ u : ℕ → ℝ,
    ((robustFamily η w hw hc hρc κ l).cost (CriticalEntropy.uniformCoinTape p u) : ℕ∞) ≤
      2 * min (bankCorrectTime (negativeBankTest w (levelEpsilon l))
          (positiveBankTest η w (ρ*levelEpsilon l/c)) s (CriticalEntropy.uniformCoinTape p u))
        (ordinaryCorrectTime s (2 * κ l)
          (parityTape 1 (CriticalEntropy.uniformCoinTape p u)) : ℕ∞) ∧
    2 * min (bankCorrectTime (negativeBankTest w (levelEpsilon l))
          (positiveBankTest η w (ρ*levelEpsilon l/c)) s (CriticalEntropy.uniformCoinTape p u))
        (ordinaryCorrectTime s (2 * κ l)
          (parityTape 1 (CriticalEntropy.uniformCoinTape p u)) : ℕ∞) ≤
      2 * min (bankCorrectTime (negativeBankTest w (levelEpsilon l))
          (positiveBankTest η w (ρ*levelEpsilon l/c)) s (CriticalEntropy.uniformCoinTape p₀ u))
        (ordinaryCorrectTime s (2 * κ l)
          (parityTape 1 (CriticalEntropy.uniformCoinTape p₀ u)) : ℕ∞)

end ThresholdHC.RobustContinuationForms
