import ThresholdHC.RobustContinuation.RobustLevelCertificates
import ThresholdHC.KnownLawPlanner.PlanCertificate

/-! The plan of a reference law, run under a true law with larger gaps.

The reference law has positive part `c η` with design `σ + τ + ζ = c η`.
The level race of level `l` is designed from the reference alone: band
weights of `σ`, null law `η`, allowances `ε_l` and `ρ ε_l / c`, and a cap
`4^(κ l)`. The plan's estimator runs a Poisson number of corrections at each
level, with mean counts `r`. It observes flips only and does not depend on
the true law.

Let the true law `μ` be the second marginal of a coupling `π` with first
marginal `c η` and `z.1 ≤ z.2` almost everywhere, plus a part `μ₀` coupled
to no positive reference gap. Under `μ`, for every sign law with positive
fraction at most `ρ`:

* the race of level `l` has bias at most `δ_l` and its correction has second
  moment at most `17 δ_l`, at caps that pass the error test of the reference
  design and with `ζ(all gaps) + μ₀(all gaps) ≤ δ_l/8`;
* the expected work of the race of level `l` is at most the level price of
  the reference design with unresolved mass `ζ(all gaps) + μ₀(all gaps)`;
* so a plan that is admissible for an enclosure of the reference design
  whose unresolved mass covers `ζ(all gaps) + μ₀(all gaps)` spends at most
  `B` in expectation and has root-mean-square risk at most the square root
  of its certificate `δ_J² + Σ_l 17 δ_l / r_l`.

These are the statements of the known-law plan with the true law in the
experiment and the reference law in the design. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace ThresholdHC.RobustContinuation
open ThresholdHC ThresholdHC.Tier2 ThresholdHC.Tier6 ThresholdHC.ObservableSimulation
open ThresholdHC.BlindUpper ThresholdHC.EntropyTailUpper ThresholdHC.RareAboveTwo
open ThresholdHC.EntropyTailQuantile ThresholdHC.EntropyTailAssembly
open ThresholdHC.EntropyTailSampling ThresholdHC.EntropyTailExecution
open ThresholdHC.KnownLawPlanner

/-- The race designed from a reference buys at least one flip: neither bank
test fires on the empty prefix when `ρ ≤ c`. -/
theorem robust_raceCost_pos (η : Measure Gap) [IsProbabilityMeasure η] (weights : ℕ → ℝ≥0)
    (hw : HasSum weights 1) {ρ c : ℝ} (hc : 0 < c) (hρc : ρ ≤ c) (l L : ℕ) (ω : ℕ → Bool) :
    0 < raceCost (negativeBankTest weights (levelEpsilon l))
      (positiveBankTest η weights (ρ*levelEpsilon l/c)) L ω := by
  have he : levelEpsilon l < 1 := by
    unfold levelEpsilon
    have h : (1/16:ℝ)^l ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith
  have hu : ρ*levelEpsilon l/c < 1 := by
    rw [div_lt_one hc]
    have h := mul_le_mul_of_nonneg_right hρc (levelEpsilon_pos l).le
    have h2 := mul_pos hc (sub_pos.mpr he)
    linarith
  exact raceCost_pos_of_no_empty_crossing _ _
    (negativeBankTest_zero weights hw (levelEpsilon_pos l).le he)
    (positiveBankTest_zero η weights hw hu) L ω

/-- The race of level `l` designed from a reference, at the cap `4^(κ l)`:
null law `η`, negative allowance `ε_l`, positive allowance `ρ ε_l / c`. -/
def robustFamily (η : Measure Gap) [IsProbabilityMeasure η] (w : ℕ → ℝ≥0) (hw : HasSum w 1)
    {c : ℝ} (hc : 0 < c) {ρ : ℝ} (hρc : ρ ≤ c) (κ : ℕ → ℕ) (l : ℕ) : FiniteCall where
  cost := raceCost (negativeBankTest w (levelEpsilon l))
    (positiveBankTest η w (ρ*levelEpsilon l/c)) (2 * κ l)
  value := raceValue (negativeBankTest w (levelEpsilon l))
    (positiveBankTest η w (ρ*levelEpsilon l/c)) (2 * κ l)
  measurable_cost := measurable_raceCost _ _ _
  measurable_value := measurable_raceValue _ _ _
  positive := robust_raceCost_pos η w hw hc hρc l (2 * κ l)
  prefix_ext := race_prefix_ext _ _ _

/-- Every run of the level race buys at most `2 · 4^(κ l)` flips. -/
theorem robustFamily_cost_bound (η : Measure Gap) [IsProbabilityMeasure η] (w : ℕ → ℝ≥0)
    (hw : HasSum w 1) {c : ℝ} (hc : 0 < c) {ρ : ℝ} (hρc : ρ ≤ c) (κ : ℕ → ℕ) (l : ℕ)
    (ω : ℕ → Bool) :
    ((robustFamily η w hw hc hρc κ l).cost ω:ℝ) ≤ 2 * 4 ^ κ l := by
  have h4 : (4:ℝ) ^ κ l = 2 ^ (2 * κ l) := by
    rw [pow_mul]
    norm_num
  rw [h4]
  unfold robustFamily
  exact_mod_cast raceCost_le (negativeBankTest w (levelEpsilon l))
    (positiveBankTest η w (ρ*levelEpsilon l/c)) (2 * κ l) ω

/-- The level race returns zero or one. -/
theorem robustFamily_binary (η : Measure Gap) [IsProbabilityMeasure η] (w : ℕ → ℝ≥0)
    (hw : HasSum w 1) {c : ℝ} (hc : 0 < c) {ρ : ℝ} (hρc : ρ ≤ c) (κ : ℕ → ℕ) (l : ℕ)
    (ω : ℕ → Bool) :
    (robustFamily η w hw hc hρc κ l).value ω = 0 ∨ (robustFamily η w hw hc hρc κ l).value ω = 1 :=
  raceValue_zero_or_one _ _ _ _

/-- Under the true law, the bias of the level race is at most `δ_l`. -/
theorem robustFamily_bias (η : Measure Gap) [IsProbabilityMeasure η]
    (ν ζ : Measure Gap) [IsFiniteMeasure ν] [IsFiniteMeasure ζ]
    {c : ℝ} (hc : 0 < c) (hdesign : ν+ζ = ENNReal.ofReal c • η)
    (π : Measure (Gap × Gap)) [IsFiniteMeasure π] (hup : ∀ᵐ z ∂π, (z.1:ℝ) ≤ z.2)
    (href : π.map Prod.fst = ENNReal.ofReal c • η) (μ₀ : Measure Gap) [IsFiniteMeasure μ₀]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (hμ : μ = π.map Prod.snd + μ₀)
    (w : ℕ → ℝ≥0) (hw : HasSum w 1) {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ c)
    (q : SignLaw) (hq : RarePrior μ ρ q) (κ : ℕ → ℕ) (l : ℕ)
    (hκ : eta ν (4 ^ κ l) ≤ levelAccuracy ρ l/8)
    (hz : ζ.real univ + μ₀.real univ ≤ levelAccuracy ρ l/8) :
    |(∫ ω, (robustFamily η w hw hc hρc κ l).value ω ∂originalPopulationTapeLaw μ q)-
        signMean μ q.val| ≤ levelAccuracy ρ l := by
  subst hμ
  exact (raceValue_bias_le _ q _ _ _).trans
    (robust_level_error η ν ζ hc hdesign π hup href μ₀ w hw hρ q hq l (κ l) hκ hz)

/-- Under the true law, the correction of level `l` has second moment at
most `17 δ_l`. -/
theorem robustFamily_second (η : Measure Gap) [IsProbabilityMeasure η]
    (ν ζ : Measure Gap) [IsFiniteMeasure ν] [IsFiniteMeasure ζ]
    {c : ℝ} (hc : 0 < c) (hdesign : ν+ζ = ENNReal.ofReal c • η)
    (π : Measure (Gap × Gap)) [IsFiniteMeasure π] (hup : ∀ᵐ z ∂π, (z.1:ℝ) ≤ z.2)
    (href : π.map Prod.fst = ENNReal.ofReal c • η) (μ₀ : Measure Gap) [IsFiniteMeasure μ₀]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (hμ : μ = π.map Prod.snd + μ₀)
    (w : ℕ → ℝ≥0) (hw : HasSum w 1) {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ ≤ c)
    (q : SignLaw) (hq : RarePrior μ ρ q) (κ : ℕ → ℕ) (l : ℕ)
    (hκ : ∀ j, j ≤ l → eta ν (4 ^ κ j) ≤ levelAccuracy ρ j/8)
    (hz : ζ.real univ + μ₀.real univ ≤ levelAccuracy ρ l/8) :
    (∫ ω, ((incrementCall (robustFamily η w hw hc hρc κ) l).value ω)^2
      ∂originalPopulationTapeLaw μ q) ≤ 17*levelAccuracy ρ l := by
  cases l with
  | zero =>
    have he : (fun ω => ((incrementCall (robustFamily η w hw hc hρc κ) 0).value ω)^2) =
        (robustFamily η w hw hc hρc κ 0).value := by
      funext ω
      rcases robustFamily_binary η w hw hc hρc κ 0 ω with h | h <;> simp [incrementCall, h]
    rw [he]
    have hb := (abs_le.mp (robustFamily_bias η ν ζ hc hdesign π hup href μ₀ μ hμ w hw hρ hρc
      q hq κ 0 (hκ 0 le_rfl) hz)).2
    have hδ := levelAccuracy_zero ρ
    change signMean μ q.val ≤ ρ at hq
    linarith
  | succ l =>
    have hz' : ζ.real univ + μ₀.real univ ≤ levelAccuracy ρ l/8 :=
      hz.trans (div_le_div_of_nonneg_right (levelAccuracy_antitone hρ.le (by omega))
        (by norm_num))
    have h := race_difference_population_moment μ q
      (negativeBankTest w (levelEpsilon (l+1))) (positiveBankTest η w (ρ*levelEpsilon (l+1)/c))
      (negativeBankTest w (levelEpsilon l)) (positiveBankTest η w (ρ*levelEpsilon l/c))
      (2 * κ (l+1)) (2 * κ l)
    change (∫ ω, ((incrementCall (robustFamily η w hw hc hρc κ) (l+1)).value ω)^2
      ∂originalPopulationTapeLaw μ q) ≤ _ at h
    refine h.trans ?_
    subst hμ
    have he := add_le_add
      (robust_level_error η ν ζ hc hdesign π hup href μ₀ w hw hρ q hq (l+1) (κ (l+1))
        (hκ (l+1) le_rfl) hz)
      (robust_level_error η ν ζ hc hdesign π hup href μ₀ w hw hρ q hq l (κ l)
        (hκ l (by omega)) hz')
    have hδ := levelAccuracy_succ ρ l
    linarith

/-- Under the true law, the expected work of the level race is at most the
proved level work of the reference design, with `μ₀` in the unresolved
mass. -/
theorem robustFamily_work (η : Measure Gap) [IsProbabilityMeasure η]
    (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ]
    {c : ℝ} (hc : 0 < c) (hdesign : σ+τ+ζ = ENNReal.ofReal c • η)
    (π : Measure (Gap × Gap)) [IsFiniteMeasure π] (hup : ∀ᵐ z ∂π, (z.1:ℝ) ≤ z.2)
    (href : π.map Prod.fst = ENNReal.ofReal c • η) (μ₀ : Measure Gap) [IsFiniteMeasure μ₀]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (hμ : μ = π.map Prod.snd + μ₀)
    {t ρ : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ))
    (hN : bandEdge N < t) (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ)
    (hρ : 0 < ρ) (hρc : ρ ≤ c) (hz : ζ.real univ ≤ ρ) (q : SignLaw)
    (hq : RarePrior μ ρ q) (κ : ℕ → ℕ) (l : ℕ) :
    (∫ ω, ((robustFamily η (referenceWeights σ) (referenceWeights_probability σ ht hs hN)
      hc hρc κ l).cost ω:ℝ) ∂originalPopulationTapeLaw μ q) ≤
      planLevelWork τ ρ (costEntropy (fun j : Fin N => bandCost σ j.val))
        (ζ.real univ + μ₀.real univ) l (κ l) := by
  subst hμ
  rw [show (fun ω => ((robustFamily η (referenceWeights σ)
      (referenceWeights_probability σ ht hs hN) hc hρc κ l).cost ω:ℝ)) =
      fun ω => (raceCost (negativeBankTest (referenceWeights σ) (levelEpsilon l))
        (positiveBankTest η (referenceWeights σ) (ρ*levelEpsilon l/c)) (2 * κ l) ω:ℝ) from rfl,
    race_population_work]
  have h := robust_three_piece_level_work η σ τ ζ hc hdesign π hup href μ₀ ht hs hN hτ hρ hz
    q hq l (2 * κ l)
  rw [cap_twice] at h
  exact h.trans_eq (by unfold planLevelWork; ring)

/-- Under the true law, the expected work of the level race is at most the
level price of the reference design, with `μ₀` in the unresolved mass. -/
theorem robustFamily_price (η : Measure Gap) [IsProbabilityMeasure η]
    (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ]
    {c : ℝ} (hc : 0 < c) (hdesign : σ+τ+ζ = ENNReal.ofReal c • η)
    (π : Measure (Gap × Gap)) [IsFiniteMeasure π] (hup : ∀ᵐ z ∂π, (z.1:ℝ) ≤ z.2)
    (href : π.map Prod.fst = ENNReal.ofReal c • η) (μ₀ : Measure Gap) [IsFiniteMeasure μ₀]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (hμ : μ = π.map Prod.snd + μ₀)
    {t ρ : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ))
    (hN : bandEdge N < t) (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ)
    (hρ : 0 < ρ) (hρc : ρ ≤ c) (hz : ζ.real univ ≤ ρ) (q : SignLaw)
    (hq : RarePrior μ ρ q) (κ : ℕ → ℕ) (l : ℕ) :
    (∫ ω, ((robustFamily η (referenceWeights σ) (referenceWeights_probability σ ht hs hN)
      hc hρc κ l).cost ω:ℝ) ∂originalPopulationTapeLaw μ q) ≤
      planLevelPrice τ ρ (costEntropy (fun j : Fin N => bandCost σ j.val))
        (ζ.real univ + μ₀.real univ) l (κ l) := by
  refine le_min ?_ (robustFamily_work η σ τ ζ hc hdesign π hup href μ₀ μ hμ ht hs hN hτ hρ hρc
    hz q hq κ l)
  have hK := robustFamily_cost_bound η (referenceWeights σ)
    (referenceWeights_probability σ ht hs hN) hc hρc κ l
  have h := integral_mono (call_cost_integrable (originalPopulationTapeLaw μ q) _ hK)
    (integrable_const (μ := originalPopulationTapeLaw μ q) ((2:ℝ) * 4 ^ κ l)) hK
  simpa using h

/-- The estimator of a plan of the reference: the Poisson multilevel
estimator over the corrections of the level races designed from the
reference, with the plan's caps and counts. It does not depend on the true
law. -/
def robustPlanEstimator (η : Measure Gap) [IsProbabilityMeasure η] (σ : Measure Gap)
    [IsFiniteMeasure σ] {t : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ))
    (hN : bandEdge N < t) {c : ℝ} (hc : 0 < c) {ρ : ℝ} (hρc : ρ ≤ c) (κ : ℕ → ℕ) {J : ℕ}
    (r : Fin (J+1) → ℝ≥0) : AdaptiveEstimator (Fin (J+1) → ℕ) :=
  plannedEstimator r (fun i => incrementCall (robustFamily η (referenceWeights σ)
    (referenceWeights_probability σ ht hs hN) hc hρc κ) i.val)

/-- The work of a plan of the reference under the true law. When each price
is at least the level price of the reference design with `μ₀` in the
unresolved mass, and the counts spend at most `B`, the expected work is at
most `B` under every rare prior of the true law. -/
theorem robust_plan_budget (η : Measure Gap) [IsProbabilityMeasure η]
    (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ]
    {c : ℝ} (hc : 0 < c) (hdesign : σ+τ+ζ = ENNReal.ofReal c • η)
    (π : Measure (Gap × Gap)) [IsFiniteMeasure π] (hup : ∀ᵐ z ∂π, (z.1:ℝ) ≤ z.2)
    (href : π.map Prod.fst = ENNReal.ofReal c • η) (μ₀ : Measure Gap) [IsFiniteMeasure μ₀]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (hμ : μ = π.map Prod.snd + μ₀)
    {t ρ B : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ))
    (hN : bandEdge N < t) (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ)
    (hρ : 0 < ρ) (hρc : ρ ≤ c) (hz : ζ.real univ ≤ ρ) (κ : ℕ → ℕ) (C : ℕ → ℝ)
    (hC : ∀ l, planLevelPrice τ ρ (costEntropy (fun j : Fin N => bandCost σ j.val))
      (ζ.real univ + μ₀.real univ) l (κ l) ≤ C l)
    {J : ℕ} (r : Fin (J+1) → ℝ≥0)
    (hwork : ∑ i : Fin (J+1), (r i:ℝ) * adjacentCost C i.val ≤ B) :
    RareBudget μ (robustPlanEstimator η σ ht hs hN hc hρc κ r) ρ B := by
  intro q hq
  have hK := robustFamily_cost_bound η (referenceWeights σ)
    (referenceWeights_probability σ ht hs hN) hc hρc κ
  have hP : ∀ l, (∫ ω, ((robustFamily η (referenceWeights σ)
      (referenceWeights_probability σ ht hs hN) hc hρc κ l).cost ω:ℝ)
      ∂originalPopulationTapeLaw μ q) ≤ C l := fun l =>
    (robustFamily_price η σ τ ζ hc hdesign π hup href μ₀ μ hμ ht hs hN hτ hρ hρc hz q hq κ
      l).trans (hC l)
  unfold robustPlanEstimator
  exact (planned_work_bound r _
    (fun i => incrementCall_cost_bound _ (fun l => 2 * 4 ^ κ l) hK i.val) μ q
    (c := fun i => adjacentCost C i.val)
    (fun i => incrementCall_work_bound (originalPopulationTapeLaw μ q) _
      (fun l => 2 * 4 ^ κ l) C hK hP i.val)).trans (ENNReal.ofReal_le_ofReal hwork)

/-- The error of a plan of the reference under the true law. When each cap
passes the error test of the reference design and
`ζ(all gaps) + μ₀(all gaps) ≤ δ_J/8`, the squared risk is at most the
certificate, under every rare prior of the true law. -/
theorem robust_plan_squaredRisk (η : Measure Gap) [IsProbabilityMeasure η]
    (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ]
    {c : ℝ} (hc : 0 < c) (hdesign : σ+τ+ζ = ENNReal.ofReal c • η)
    (π : Measure (Gap × Gap)) [IsFiniteMeasure π] (hup : ∀ᵐ z ∂π, (z.1:ℝ) ≤ z.2)
    (href : π.map Prod.fst = ENNReal.ofReal c • η) (μ₀ : Measure Gap) [IsFiniteMeasure μ₀]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (hμ : μ = π.map Prod.snd + μ₀)
    {t ρ : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ))
    (hN : bandEdge N < t) (hρ : 0 < ρ) (hρc : ρ ≤ c) (κ : ℕ → ℕ) {J : ℕ}
    (hκ : ∀ l, l ≤ J → eta (σ+τ) (4 ^ κ l) ≤ levelAccuracy ρ l/8)
    (hzJ : ζ.real univ + μ₀.real univ ≤ levelAccuracy ρ J/8)
    (r : Fin (J+1) → ℝ≥0) (hr : ∀ i, 0 < (r i:ℝ)) (q : SignLaw) (hq : RarePrior μ ρ q) :
    squaredRisk (experimentLaw μ (robustPlanEstimator η σ ht hs hN hc hρc κ r) q)
      (populationOutput (robustPlanEstimator η σ ht hs hN hc hρc κ r)) (signMean μ q.val) ≤
      ENNReal.ofReal (planCertificate ρ r) := by
  have hbin := robustFamily_binary η (referenceWeights σ)
    (referenceWeights_probability σ ht hs hN) hc hρc κ
  have hV : ∀ i : Fin (J+1), (∫ ω, ((incrementCall (robustFamily η (referenceWeights σ)
      (referenceWeights_probability σ ht hs hN) hc hρc κ) i.val).value ω)^2
      ∂originalPopulationTapeLaw μ q) ≤ 17*levelAccuracy ρ i.val := fun i =>
    robustFamily_second η (σ+τ) ζ hc hdesign π hup href μ₀ μ hμ _ _ hρ hρc q hq κ i.val
      (fun j hj => hκ j (by omega))
      (hzJ.trans (div_le_div_of_nonneg_right
        (levelAccuracy_antitone hρ.le (by omega)) (by norm_num)))
  have hbias : |(∑ i : Fin (J+1), ∫ ω, (incrementCall (robustFamily η (referenceWeights σ)
      (referenceWeights_probability σ ht hs hN) hc hρc κ) i.val).value ω
      ∂originalPopulationTapeLaw μ q)-signMean μ q.val| ≤ levelAccuracy ρ J := by
    rw [incrementCall_mean_sum _ _ hbin J]
    exact robustFamily_bias η (σ+τ) ζ hc hdesign π hup href μ₀ μ hμ _ _ hρ hρc q hq κ J
      (hκ J le_rfl) hzJ
  unfold robustPlanEstimator planCertificate
  rw [add_comm (levelAccuracy ρ J ^ 2)]
  exact planned_mse_bound r hr _ (fun _ => zero_le_one)
    (fun i => incrementCall_bounded _ hbin i.val) μ q _ hV
    (levelAccuracy_pos hρ J).le hbias

/-- The root-mean-square risk of a plan of the reference, over all rare
priors of the true law. -/
theorem robust_plan_rareRisk (η : Measure Gap) [IsProbabilityMeasure η]
    (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ]
    {c : ℝ} (hc : 0 < c) (hdesign : σ+τ+ζ = ENNReal.ofReal c • η)
    (π : Measure (Gap × Gap)) [IsFiniteMeasure π] (hup : ∀ᵐ z ∂π, (z.1:ℝ) ≤ z.2)
    (href : π.map Prod.fst = ENNReal.ofReal c • η) (μ₀ : Measure Gap) [IsFiniteMeasure μ₀]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (hμ : μ = π.map Prod.snd + μ₀)
    {t ρ : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ))
    (hN : bandEdge N < t) (hρ : 0 < ρ) (hρc : ρ ≤ c) (κ : ℕ → ℕ) {J : ℕ}
    (hκ : ∀ l, l ≤ J → eta (σ+τ) (4 ^ κ l) ≤ levelAccuracy ρ l/8)
    (hzJ : ζ.real univ + μ₀.real univ ≤ levelAccuracy ρ J/8)
    (r : Fin (J+1) → ℝ≥0) (hr : ∀ i, 0 < (r i:ℝ)) :
    rareRisk μ (robustPlanEstimator η σ ht hs hN hc hρc κ r) ρ ≤
      ENNReal.ofReal (Real.sqrt (planCertificate ρ r)) := by
  refine iSup₂_le fun q hq => ?_
  have h := robust_plan_squaredRisk η σ τ ζ hc hdesign π hup href μ₀ μ hμ ht hs hN hρ hρc κ hκ
    hzJ r hr q hq
  unfold rootMeanRisk
  calc _ ≤ ENNReal.ofReal (planCertificate ρ r) ^ (1/2 : ℝ) :=
        ENNReal.rpow_le_rpow h (by norm_num)
    _ = ENNReal.ofReal (Real.sqrt (planCertificate ρ r)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (planCertificate_nonneg hρ r) (by norm_num),
          ← Real.sqrt_eq_rpow]

/-- The price computed from an enclosure is at least the level price at
every unresolved mass that the enclosure covers. -/
theorem planLevelPrice_le_price {σ τ ζ : Measure Gap} {N : ℕ} (E : SplitEnclosure σ τ ζ N)
    {ρ z : ℝ} (hρ : 0 < ρ) (hz : z ≤ E.unresolved) (l k : ℕ) :
    planLevelPrice τ ρ (costEntropy (fun j : Fin N => bandCost σ j.val)) z l k ≤
      E.price ρ l k := by
  have hH : 0 ≤ ∫ d : Gap, (d:ℝ)⁻¹ ∂τ := integral_nonneg fun d => inv_nonneg.mpr d.property.1.le
  have hsq : (∫ d : Gap, (d:ℝ)⁻¹ ∂τ)^2 ≤ E.tailInverse^2 :=
    pow_le_pow_left₀ hH E.tailInverse_le 2
  have hl : (0:ℝ) ≤ 128*(l+1) := by positivity
  have h4 : (0:ℝ) < 4 ^ k := by positivity
  unfold planLevelPrice planLevelWork SplitEnclosure.price
  refine min_le_min le_rfl ?_
  have h1 := mul_le_mul_of_nonneg_left E.entropy_le hl
  have h2 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by norm_num : (0:ℝ) ≤ 6))
    hρ.le
  have h3 := E.tailWork_le (4 ^ k)
  have h4' := mul_le_mul_of_nonneg_right hz h4.le
  linarith

/-- **A plan of the reference is valid under the true law.** The plan is
computed from an enclosure of the reference design whose unresolved mass
covers `ζ(all gaps) + μ₀(all gaps)`: its caps pass the enclosure's error
test, its terminal level covers the enclosure's unresolved mass, and its
counts are priced by the enclosure's level prices. Under the true law the
plan's estimator spends at most `B` in expectation and has root-mean-square
risk at most the square root of the certificate, under every rare prior. -/
theorem robust_enclosed_plan_valid (η : Measure Gap) [IsProbabilityMeasure η]
    (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ]
    {c : ℝ} (hc : 0 < c) (hdesign : σ+τ+ζ = ENNReal.ofReal c • η)
    (π : Measure (Gap × Gap)) [IsFiniteMeasure π] (hup : ∀ᵐ z ∂π, (z.1:ℝ) ≤ z.2)
    (href : π.map Prod.fst = ENNReal.ofReal c • η) (μ₀ : Measure Gap) [IsFiniteMeasure μ₀]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (hμ : μ = π.map Prod.snd + μ₀)
    {t ρ B : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ))
    (hN : bandEdge N < t) (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ)
    (hρ : 0 < ρ) (hρc : ρ ≤ c) (E : SplitEnclosure σ τ ζ N)
    (hE₀ : ζ.real univ + μ₀.real univ ≤ E.unresolved) (κ : ℕ → ℕ) {J : ℕ}
    (hκ : ∀ l, l ≤ J → E.resolvedError (4 ^ κ l) ≤ levelAccuracy ρ l/8)
    (hzJ : E.unresolved ≤ levelAccuracy ρ J/8)
    (r : Fin (J+1) → ℝ≥0) (hr : ∀ i, 0 < (r i:ℝ))
    (hwork : ∑ i : Fin (J+1), (r i:ℝ) * adjacentCost (fun l => E.price ρ l (κ l)) i.val ≤ B) :
    RareBudget μ (robustPlanEstimator η σ ht hs hN hc hρc κ r) ρ B ∧
      rareRisk μ (robustPlanEstimator η σ ht hs hN hc hρc κ r) ρ ≤
        ENNReal.ofReal (Real.sqrt (planCertificate ρ r)) := by
  have hzJ' : ζ.real univ + μ₀.real univ ≤ levelAccuracy ρ J/8 := hE₀.trans hzJ
  have hz : ζ.real univ ≤ ρ := by
    have h := levelAccuracy_le_first hρ.le J
    have h0 : 0 ≤ μ₀.real univ := measureReal_nonneg
    linarith
  exact ⟨robust_plan_budget η σ τ ζ hc hdesign π hup href μ₀ μ hμ ht hs hN hτ hρ hρc hz κ _
      (fun l => planLevelPrice_le_price E hρ hE₀ l (κ l)) r hwork,
    robust_plan_rareRisk η σ τ ζ hc hdesign π hup href μ₀ μ hμ ht hs hN hρ hρc κ
      (fun l hl => (E.resolvedError_le _).trans (hκ l hl)) hzJ' r hr⟩

/-- Every correction of a plan of the reference has positive cost: under
the true law each level race buys a flip, so each level price is at least
one. -/
theorem robust_planCost_pos (η : Measure Gap) [IsProbabilityMeasure η]
    (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ]
    {c : ℝ} (hc : 0 < c) (hdesign : σ+τ+ζ = ENNReal.ofReal c • η)
    (π : Measure (Gap × Gap)) [IsFiniteMeasure π] (hup : ∀ᵐ z ∂π, (z.1:ℝ) ≤ z.2)
    (href : π.map Prod.fst = ENNReal.ofReal c • η) (μ₀ : Measure Gap) [IsFiniteMeasure μ₀]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (hμ : μ = π.map Prod.snd + μ₀)
    {t ρ : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ))
    (hN : bandEdge N < t) (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ)
    (hρ : 0 < ρ) (hρc : ρ ≤ c) (hz : ζ.real univ ≤ ρ) (E : SplitEnclosure σ τ ζ N)
    (hE₀ : ζ.real univ + μ₀.real univ ≤ E.unresolved) (κ : ℕ → ℕ) (J : ℕ) (i : Fin (J+1)) :
    0 < planCost E ρ κ J i := by
  have hq : RarePrior μ ρ allNegativeSignLaw := by
    change (∫ d, (0:ℝ) ∂μ) ≤ ρ
    simpa using hρ.le
  have hp : ∀ l, 0 < E.price ρ l (κ l) := fun l => by
    have hK := robustFamily_cost_bound η (referenceWeights σ)
      (referenceWeights_probability σ ht hs hN) hc hρc κ l
    have h1 := call_cost_mean_ge_one (originalPopulationTapeLaw μ allNegativeSignLaw) _ hK
    have h2 := robustFamily_price η σ τ ζ hc hdesign π hup href μ₀ μ hμ ht hs hN hτ hρ hρc hz
      allNegativeSignLaw hq κ l
    have h3 := planLevelPrice_le_price E hρ hE₀ l (κ l)
    linarith
  unfold planCost adjacentCost
  split_ifs
  · exact hp _
  · exact add_pos (hp _) (hp _)

/-- **The plan returned by the planner for the reference is valid under the
true law.** The planner searches the caps against the enclosure's error
envelope, prices the levels with the enclosure, and turns positive weights
into mean counts. With a terminal level `J` whose `δ_J/8` covers the
enclosure's unresolved mass, the plan's estimator spends at most `B` in
expectation under the true law and has root-mean-square risk at most the
square root of the certificate, under every rare prior. -/
theorem robust_searched_plan_valid (η : Measure Gap) [IsProbabilityMeasure η]
    (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ]
    {c : ℝ} (hc : 0 < c) (hdesign : σ+τ+ζ = ENNReal.ofReal c • η)
    (π : Measure (Gap × Gap)) [IsFiniteMeasure π] (hup : ∀ᵐ z ∂π, (z.1:ℝ) ≤ z.2)
    (href : π.map Prod.fst = ENNReal.ofReal c • η) (μ₀ : Measure Gap) [IsFiniteMeasure μ₀]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (hμ : μ = π.map Prod.snd + μ₀)
    {t ρ B : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ))
    (hN : bandEdge N < t) (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ)
    (hρ : 0 < ρ) (hρc : ρ ≤ c) (hB : 0 < B) (E : SplitEnclosure σ τ ζ N)
    (hE₀ : ζ.real univ + μ₀.real univ ≤ E.unresolved)
    (hvan : EnvelopeVanishes E.resolvedError) {J : ℕ}
    (hzJ : E.unresolved ≤ levelAccuracy ρ J/8) (w : Fin (J+1) → ℝ) (hw : ∀ i, 0 < w i) :
    RareBudget μ (robustPlanEstimator η σ ht hs hN hc hρc
        (searchCaps E.resolvedError hvan hρ)
        (planRates B (planCost E ρ (searchCaps E.resolvedError hvan hρ) J) w)) ρ B ∧
      rareRisk μ (robustPlanEstimator η σ ht hs hN hc hρc
        (searchCaps E.resolvedError hvan hρ)
        (planRates B (planCost E ρ (searchCaps E.resolvedError hvan hρ) J) w)) ρ ≤
        ENNReal.ofReal (Real.sqrt (planCertificate ρ
          (planRates B (planCost E ρ (searchCaps E.resolvedError hvan hρ) J) w))) := by
  have hz : ζ.real univ ≤ ρ := by
    have h := levelAccuracy_le_first hρ.le J
    have h0 : 0 ≤ μ₀.real univ := measureReal_nonneg
    linarith [hE₀.trans hzJ]
  have hk := robust_planCost_pos η σ τ ζ hc hdesign π hup href μ₀ μ hμ ht hs hN hτ hρ hρc hz E
    hE₀ (searchCaps E.resolvedError hvan hρ) J
  refine robust_enclosed_plan_valid η σ τ ζ hc hdesign π hup href μ₀ μ hμ ht hs hN hτ hρ hρc E
    hE₀ _ (fun l _ => searchCaps_spec E.resolvedError hvan hρ l) hzJ _
    (fun i => by rw [planRates_coe hB hk hw]; exact planCount_pos hB hk hw i) ?_
  have he : ∀ i : Fin (J+1),
      (planRates B (planCost E ρ (searchCaps E.resolvedError hvan hρ) J) w i:ℝ) *
        adjacentCost (fun l => E.price ρ l (searchCaps E.resolvedError hvan hρ l)) i.val =
      planCost E ρ (searchCaps E.resolvedError hvan hρ) J i *
        planCount B (planCost E ρ (searchCaps E.resolvedError hvan hρ) J) w i := fun i => by
    rw [planRates_coe hB hk hw, mul_comm]
    rfl
  rw [Finset.sum_congr rfl fun i _ => he i, planCount_work hk hw]

end ThresholdHC.RobustContinuation
