import ThresholdHC.KnownLawPlanner.PlanFamily
import ThresholdHC.KnownLawPlanner.PlannedEstimator
import ThresholdHC.KnownLawPlanner.PlanAllocation
import ThresholdHC.KnownLawPlanner.PlanCaps
import ThresholdHC.EntropyTailExecution.ThreePiece

/-! The certificate of a plan is valid.

The gap law is split as `σ + τ + ζ`: the selected core, the resolved tail and
the unresolved part. A plan has a terminal level `J`, a cap `4^(κ l)` and a
price `C l` for each level, and positive mean counts `r`. It is admissible
when

* each cap passes the error test: the resolved error at `4^(κ l)` is at most
  `δ_l/8`, with `δ_l = ρ 16^{-(l+1)}`;
* the unresolved mass is at most `δ_J/8`;
* each price is at least the level price, the proved bound on the expected
  work of the level race; and
* the counts spend at most the budget: `Σ_l r_l k_l ≤ B`, with `k_0 = C 0` and
  `k_l = C l + C (l-1)`.

The plan's estimator runs a Poisson number of corrections at each level.
Under every rare prior its expected work is at most `B` and its squared risk
is at most the plan's certificate

  `δ_J² + Σ_l 17 δ_l / r_l`.

The estimator observes flips only; no gap, sign or component label. A
planner works from upper bounds of the design integrals. Those are collected
in an enclosure, and a plan computed from an enclosure is admissible. The
level price uses the constants of the checked level-work theorem, `128` and
`6`. -/

noncomputable section
open MeasureTheory Set Real
open scoped NNReal ENNReal BigOperators

namespace ThresholdHC.KnownLawPlanner
open ThresholdHC.Tier6 ThresholdHC.EntropyTailQuantile ThresholdHC.EntropyTailUpper
open ThresholdHC.EntropyTailAssembly ThresholdHC.ObservableSimulation ThresholdHC.RareAboveTwo
open ThresholdHC.EntropyTailExecution

/-- The squared-error certificate of a plan with terminal level `J` and mean
counts `r`: `δ_J² + Σ_l 17 δ_l / r_l`. -/
def planCertificate (ρ : ℝ) {J : ℕ} (r : Fin (J+1) → ℝ≥0) : ℝ :=
  levelAccuracy ρ J ^ 2 + ∑ i : Fin (J+1), 17*levelAccuracy ρ i.val/(r i:ℝ)

theorem planCertificate_nonneg {ρ : ℝ} (hρ : 0 < ρ) {J : ℕ} (r : Fin (J+1) → ℝ≥0) :
    0 ≤ planCertificate ρ r :=
  add_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ =>
    div_nonneg (mul_nonneg (by norm_num) (levelAccuracy_pos hρ i.val).le) (r i).coe_nonneg)

/-- The estimator of a plan: the Poisson multilevel estimator over the
corrections of the level races at the plan's caps, with the plan's counts. -/
def planEstimator (σ τ ζ : Measure Gap)
    [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)]
    {t ρ : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) (hN : bandEdge N < t)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4) (κ : ℕ → ℕ) {J : ℕ} (r : Fin (J+1) → ℝ≥0) :
    AdaptiveEstimator (Fin (J+1) → ℕ) :=
  plannedEstimator r (fun i => incrementCall (planFamily (σ+τ+ζ) (referenceWeights σ)
    (referenceWeights_probability σ ht hs hN) hρ hρ1 κ) i.val)

/-- The level price is at least one: every race buys a flip. -/
theorem one_le_planLevelPrice (σ τ ζ : Measure Gap)
    [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)]
    {t ρ : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) (hN : bandEdge N < t)
    (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4)
    (hz : ζ.real univ ≤ ρ) (l k : ℕ) :
    1 ≤ planLevelPrice τ ρ (costEntropy (fun j : Fin N => bandCost σ j.val)) (ζ.real univ) l k := by
  have hq : RarePrior (σ+τ+ζ) ρ allNegativeSignLaw := by
    change (∫ d, (0:ℝ) ∂(σ+τ+ζ)) ≤ ρ
    simpa using hρ.le
  have hK := planFamily_cost_bound (σ+τ+ζ) (referenceWeights σ)
    (referenceWeights_probability σ ht hs hN) hρ hρ1 (fun _ => k) l
  exact (call_cost_mean_ge_one (originalPopulationTapeLaw (σ+τ+ζ) allNegativeSignLaw) _ hK).trans
    (planFamily_price σ τ ζ ht hs hN hτ hρ hρ1 hz allNegativeSignLaw hq (fun _ => k) l)

/-- The work of a plan. When each price is at least the level price and the
counts spend at most `B`, the expected work of the plan's estimator is at
most `B` under every rare prior. -/
theorem plan_budget (σ τ ζ : Measure Gap)
    [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)]
    {t ρ B : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) (hN : bandEdge N < t)
    (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4)
    (hz : ζ.real univ ≤ ρ) (κ : ℕ → ℕ) (C : ℕ → ℝ)
    (hC : ∀ l, planLevelPrice τ ρ (costEntropy (fun j : Fin N => bandCost σ j.val))
      (ζ.real univ) l (κ l) ≤ C l)
    {J : ℕ} (r : Fin (J+1) → ℝ≥0)
    (hwork : ∑ i : Fin (J+1), (r i:ℝ) * adjacentCost C i.val ≤ B) :
    RareBudget (σ+τ+ζ) (planEstimator σ τ ζ ht hs hN hρ hρ1 κ r) ρ B := by
  intro q hq
  have hK := planFamily_cost_bound (σ+τ+ζ) (referenceWeights σ)
    (referenceWeights_probability σ ht hs hN) hρ hρ1 κ
  have hP : ∀ l, (∫ ω, ((planFamily (σ+τ+ζ) (referenceWeights σ)
      (referenceWeights_probability σ ht hs hN) hρ hρ1 κ l).cost ω:ℝ)
      ∂originalPopulationTapeLaw (σ+τ+ζ) q) ≤ C l := fun l =>
    (planFamily_price σ τ ζ ht hs hN hτ hρ hρ1 hz q hq κ l).trans (hC l)
  unfold planEstimator
  exact (planned_work_bound r _
    (fun i => incrementCall_cost_bound _ (fun l => 2 * 4 ^ κ l) hK i.val) (σ+τ+ζ) q
    (c := fun i => adjacentCost C i.val)
    (fun i => incrementCall_work_bound (originalPopulationTapeLaw (σ+τ+ζ) q) _
      (fun l => 2 * 4 ^ κ l) C hK hP i.val)).trans (ENNReal.ofReal_le_ofReal hwork)

/-- The error of a plan. When each cap passes the error test and the
unresolved mass is at most `δ_J/8`, the squared risk of the plan's estimator
is at most the certificate, under every rare prior. -/
theorem plan_squaredRisk (σ τ ζ : Measure Gap)
    [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)]
    {t ρ : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) (hN : bandEdge N < t)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4) (κ : ℕ → ℕ) {J : ℕ}
    (hκ : ∀ l, l ≤ J → eta (σ+τ) (4 ^ κ l) ≤ levelAccuracy ρ l/8)
    (hzJ : ζ.real univ ≤ levelAccuracy ρ J/8)
    (r : Fin (J+1) → ℝ≥0) (hr : ∀ i, 0 < (r i:ℝ)) (q : SignLaw)
    (hq : RarePrior (σ+τ+ζ) ρ q) :
    squaredRisk (experimentLaw (σ+τ+ζ) (planEstimator σ τ ζ ht hs hN hρ hρ1 κ r) q)
      (populationOutput (planEstimator σ τ ζ ht hs hN hρ hρ1 κ r)) (signMean (σ+τ+ζ) q.val) ≤
      ENNReal.ofReal (planCertificate ρ r) := by
  have hbin := planFamily_binary (σ+τ+ζ) (referenceWeights σ)
    (referenceWeights_probability σ ht hs hN) hρ hρ1 κ
  have hV : ∀ i : Fin (J+1), (∫ ω, ((incrementCall (planFamily (σ+τ+ζ) (referenceWeights σ)
      (referenceWeights_probability σ ht hs hN) hρ hρ1 κ) i.val).value ω)^2
      ∂originalPopulationTapeLaw (σ+τ+ζ) q) ≤ 17*levelAccuracy ρ i.val := fun i =>
    planFamily_second (σ+τ+ζ) (σ+τ) ζ rfl _ _ hρ hρ1 q hq κ i.val
      (fun j hj => hκ j (by omega))
      (hzJ.trans (div_le_div_of_nonneg_right
        (levelAccuracy_antitone hρ.le (by omega)) (by norm_num)))
  have hbias : |(∑ i : Fin (J+1), ∫ ω, (incrementCall (planFamily (σ+τ+ζ) (referenceWeights σ)
      (referenceWeights_probability σ ht hs hN) hρ hρ1 κ) i.val).value ω
      ∂originalPopulationTapeLaw (σ+τ+ζ) q)-signMean (σ+τ+ζ) q.val| ≤ levelAccuracy ρ J := by
    rw [incrementCall_mean_sum _ _ hbin J]
    exact planFamily_bias (σ+τ+ζ) (σ+τ) ζ rfl _ _ hρ hρ1 q hq κ J (hκ J le_rfl) hzJ
  unfold planEstimator planCertificate
  rw [add_comm (levelAccuracy ρ J ^ 2)]
  exact planned_mse_bound r hr _ (fun _ => zero_le_one)
    (fun i => incrementCall_bounded _ hbin i.val) (σ+τ+ζ) q _ hV
    (levelAccuracy_pos hρ J).le hbias

/-- The root-mean-square risk of an admissible plan, over all rare priors. -/
theorem plan_rareRisk (σ τ ζ : Measure Gap)
    [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)]
    {t ρ : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) (hN : bandEdge N < t)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4) (κ : ℕ → ℕ) {J : ℕ}
    (hκ : ∀ l, l ≤ J → eta (σ+τ) (4 ^ κ l) ≤ levelAccuracy ρ l/8)
    (hzJ : ζ.real univ ≤ levelAccuracy ρ J/8)
    (r : Fin (J+1) → ℝ≥0) (hr : ∀ i, 0 < (r i:ℝ)) :
    rareRisk (σ+τ+ζ) (planEstimator σ τ ζ ht hs hN hρ hρ1 κ r) ρ ≤
      ENNReal.ofReal (Real.sqrt (planCertificate ρ r)) := by
  refine iSup₂_le fun q hq => ?_
  have h := plan_squaredRisk σ τ ζ ht hs hN hρ hρ1 κ hκ hzJ r hr q hq
  unfold rootMeanRisk
  calc _ ≤ ENNReal.ofReal (planCertificate ρ r) ^ (1/2 : ℝ) :=
        ENNReal.rpow_le_rpow h (by norm_num)
    _ = ENNReal.ofReal (Real.sqrt (planCertificate ρ r)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (planCertificate_nonneg hρ r) (by norm_num),
          ← Real.sqrt_eq_rpow]

/-- Certified upper bounds of the design integrals of a split `σ + τ + ζ`
whose core meets the first `N` bands: the cost entropy of the band costs of
`σ`, `∫ d⁻¹ dτ`, the mass of `ζ`, the resolved error of `σ + τ` and the
ordinary work of `τ` at every cap. -/
structure SplitEnclosure (σ τ ζ : Measure Gap) (N : ℕ) where
  entropy : ℝ
  tailInverse : ℝ
  unresolved : ℝ
  resolvedError : ℝ → ℝ
  tailWork : ℝ → ℝ
  entropy_le : costEntropy (fun j : Fin N => bandCost σ j.val) ≤ entropy
  tailInverse_le : (∫ d : Gap, (d:ℝ)⁻¹ ∂τ) ≤ tailInverse
  unresolved_le : ζ.real univ ≤ unresolved
  resolvedError_le : ∀ M : ℝ, eta (σ+τ) M ≤ resolvedError M
  tailWork_le : ∀ M : ℝ, ordinaryCost τ M ≤ tailWork M

/-- The exact design integrals. -/
def SplitEnclosure.exact (σ τ ζ : Measure Gap) (N : ℕ) : SplitEnclosure σ τ ζ N where
  entropy := costEntropy (fun j : Fin N => bandCost σ j.val)
  tailInverse := ∫ d : Gap, (d:ℝ)⁻¹ ∂τ
  unresolved := ζ.real univ
  resolvedError := eta (σ+τ)
  tailWork := ordinaryCost τ
  entropy_le := le_rfl
  tailInverse_le := le_rfl
  unresolved_le := le_rfl
  resolvedError_le := fun _ => le_rfl
  tailWork_le := fun _ => le_rfl

/-- The level price computed from an enclosure, at level `l` and cap `4^k`. -/
def SplitEnclosure.price {σ τ ζ : Measure Gap} {N : ℕ} (E : SplitEnclosure σ τ ζ N) (ρ : ℝ)
    (l k : ℕ) : ℝ :=
  min (2 * 4 ^ k)
    (128*(l+1)*E.entropy + 6*E.tailInverse^2/ρ + 2*E.tailWork (4 ^ k) + 2*E.unresolved*4 ^ k)

/-- The price computed from an enclosure is at least the level price. -/
theorem SplitEnclosure.planLevelPrice_le {σ τ ζ : Measure Gap} {N : ℕ}
    (E : SplitEnclosure σ τ ζ N) {ρ : ℝ} (hρ : 0 < ρ) (l k : ℕ) :
    planLevelPrice τ ρ (costEntropy (fun j : Fin N => bandCost σ j.val)) (ζ.real univ) l k ≤
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
  have h4' := mul_le_mul_of_nonneg_right E.unresolved_le h4.le
  linarith

/-- A plan computed from an enclosure is admissible. The caps are tested
against the enclosure's error envelope, the terminal level against its
unresolved mass, and the counts are priced by its level prices. The plan's
estimator then spends at most `B` in expectation and has root-mean-square
risk at most the square root of the certificate, under every rare prior. -/
theorem enclosed_plan_valid (σ τ ζ : Measure Gap)
    [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)]
    {t ρ B : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) (hN : bandEdge N < t)
    (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4)
    (E : SplitEnclosure σ τ ζ N) (κ : ℕ → ℕ) {J : ℕ}
    (hκ : ∀ l, l ≤ J → E.resolvedError (4 ^ κ l) ≤ levelAccuracy ρ l/8)
    (hzJ : E.unresolved ≤ levelAccuracy ρ J/8)
    (r : Fin (J+1) → ℝ≥0) (hr : ∀ i, 0 < (r i:ℝ))
    (hwork : ∑ i : Fin (J+1), (r i:ℝ) * adjacentCost (fun l => E.price ρ l (κ l)) i.val ≤ B) :
    RareBudget (σ+τ+ζ) (planEstimator σ τ ζ ht hs hN hρ hρ1 κ r) ρ B ∧
      rareRisk (σ+τ+ζ) (planEstimator σ τ ζ ht hs hN hρ hρ1 κ r) ρ ≤
        ENNReal.ofReal (Real.sqrt (planCertificate ρ r)) := by
  have hzJ' : ζ.real univ ≤ levelAccuracy ρ J/8 := E.unresolved_le.trans hzJ
  have hz : ζ.real univ ≤ ρ := by
    have h := levelAccuracy_le_first hρ.le J
    linarith
  exact ⟨plan_budget σ τ ζ ht hs hN hτ hρ hρ1 hz κ _
      (fun l => E.planLevelPrice_le hρ l (κ l)) r hwork,
    plan_rareRisk σ τ ζ ht hs hN hρ hρ1 κ
      (fun l hl => (E.resolvedError_le _).trans (hκ l hl)) hzJ' r hr⟩

/-- The minimax risk at budget `B` is at most the certified risk of every
admissible plan, and at most the risk `ρ/2` of the constant fallback. -/
theorem enclosed_plan_minimax (σ τ ζ : Measure Gap)
    [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)]
    {t ρ B : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) (hN : bandEdge N < t)
    (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4)
    (E : SplitEnclosure σ τ ζ N) (κ : ℕ → ℕ) {J : ℕ}
    (hκ : ∀ l, l ≤ J → E.resolvedError (4 ^ κ l) ≤ levelAccuracy ρ l/8)
    (hzJ : E.unresolved ≤ levelAccuracy ρ J/8)
    (r : Fin (J+1) → ℝ≥0) (hr : ∀ i, 0 < (r i:ℝ))
    (hwork : ∑ i : Fin (J+1), (r i:ℝ) * adjacentCost (fun l => E.price ρ l (κ l)) i.val ≤ B) :
    rareMinimaxRisk (σ+τ+ζ) ρ B ≤
      ENNReal.ofReal (min (ρ/2) (Real.sqrt (planCertificate ρ r))) := by
  obtain ⟨hb, hrisk⟩ := enclosed_plan_valid σ τ ζ ht hs hN hτ hρ hρ1 E κ hκ hzJ r hr hwork
  have h1 : rareMinimaxRisk (σ+τ+ζ) ρ B ≤ ENNReal.ofReal (Real.sqrt (planCertificate ρ r)) :=
    (show rareMinimaxRisk (σ+τ+ζ) ρ B ≤
        rareRisk (σ+τ+ζ) (planEstimator σ τ ζ ht hs hN hρ hρ1 κ r) ρ from
      sInf_le ⟨Fin (J+1) → ℕ, inferInstance, planEstimator σ τ ζ ht hs hN hρ hρ1 κ r, hb,
        rfl⟩).trans hrisk
  have h2 := minimax_half_rarity (σ+τ+ζ) (B := B) hρ.le
  rcases le_total (ρ/2) (Real.sqrt (planCertificate ρ r)) with h | h
  · rwa [min_eq_left h]
  · rwa [min_eq_right h]

/-- The cost of one correction at level `i`: the price of level `i`, plus the
price of level `i - 1` when `i > 0`. -/
def planCost {σ τ ζ : Measure Gap} {N : ℕ} (E : SplitEnclosure σ τ ζ N) (ρ : ℝ) (κ : ℕ → ℕ)
    (J : ℕ) (i : Fin (J+1)) : ℝ :=
  adjacentCost (fun l => E.price ρ l (κ l)) i.val

/-- The mean counts of the plan, from weights `w`: `n_i = B w_i / Σ_j k_j w_j`. -/
def planRates {J : ℕ} (B : ℝ) (k w : Fin (J+1) → ℝ) (i : Fin (J+1)) : ℝ≥0 :=
  Real.toNNReal (planCount B k w i)

/-- Every correction has positive cost: each level price is at least one. -/
theorem planCost_pos (σ τ ζ : Measure Gap)
    [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)]
    {t ρ : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) (hN : bandEdge N < t)
    (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4)
    (hz : ζ.real univ ≤ ρ) (E : SplitEnclosure σ τ ζ N) (κ : ℕ → ℕ) (J : ℕ) (i : Fin (J+1)) :
    0 < planCost E ρ κ J i := by
  have hp : ∀ l, 0 < E.price ρ l (κ l) := fun l =>
    lt_of_lt_of_le zero_lt_one
      ((one_le_planLevelPrice σ τ ζ ht hs hN hτ hρ hρ1 hz l (κ l)).trans
        (E.planLevelPrice_le hρ l (κ l)))
  unfold planCost adjacentCost
  split_ifs
  · exact hp _
  · exact add_pos (hp _) (hp _)

theorem planRates_coe {J : ℕ} {B : ℝ} {k w : Fin (J+1) → ℝ} (hB : 0 < B)
    (hk : ∀ i, 0 < k i) (hw : ∀ i, 0 < w i) (i : Fin (J+1)) :
    (planRates B k w i:ℝ) = planCount B k w i :=
  Real.coe_toNNReal _ (planCount_pos hB hk hw i).le

/-- The plan returned by the planner is admissible. From an enclosure whose
error envelope meets the termination requirement, the planner searches the
caps, prices the levels, and turns positive weights into mean counts. With a
terminal level `J` whose `δ_J/8` covers the enclosure's unresolved mass, the
plan's estimator spends at most `B` in expectation and has root-mean-square
risk at most the square root of the certificate, under every rare prior. -/
theorem searched_plan_valid (σ τ ζ : Measure Gap)
    [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)]
    {t ρ B : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) (hN : bandEdge N < t)
    (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4) (hB : 0 < B)
    (E : SplitEnclosure σ τ ζ N) (hvan : EnvelopeVanishes E.resolvedError) {J : ℕ}
    (hzJ : E.unresolved ≤ levelAccuracy ρ J/8) (w : Fin (J+1) → ℝ) (hw : ∀ i, 0 < w i) :
    RareBudget (σ+τ+ζ) (planEstimator σ τ ζ ht hs hN hρ hρ1
        (searchCaps E.resolvedError hvan hρ)
        (planRates B (planCost E ρ (searchCaps E.resolvedError hvan hρ) J) w)) ρ B ∧
      rareRisk (σ+τ+ζ) (planEstimator σ τ ζ ht hs hN hρ hρ1
        (searchCaps E.resolvedError hvan hρ)
        (planRates B (planCost E ρ (searchCaps E.resolvedError hvan hρ) J) w)) ρ ≤
        ENNReal.ofReal (Real.sqrt (planCertificate ρ
          (planRates B (planCost E ρ (searchCaps E.resolvedError hvan hρ) J) w))) := by
  have hz : ζ.real univ ≤ ρ := by
    have h := levelAccuracy_le_first hρ.le J
    linarith [E.unresolved_le.trans hzJ]
  have hk := planCost_pos σ τ ζ ht hs hN hτ hρ hρ1 hz E (searchCaps E.resolvedError hvan hρ) J
  refine enclosed_plan_valid σ τ ζ ht hs hN hτ hρ hρ1 E _
    (fun l _ => searchCaps_spec E.resolvedError hvan hρ l) hzJ _
    (fun i => by rw [planRates_coe hB hk hw]; exact planCount_pos hB hk hw i) ?_
  have he : ∀ i : Fin (J+1),
      (planRates B (planCost E ρ (searchCaps E.resolvedError hvan hρ) J) w i:ℝ) *
        adjacentCost (fun l => E.price ρ l (searchCaps E.resolvedError hvan hρ l)) i.val =
      planCost E ρ (searchCaps E.resolvedError hvan hρ) J i *
        planCount B (planCost E ρ (searchCaps E.resolvedError hvan hρ) J) w i := fun i => by
    rw [planRates_coe hB hk hw, mul_comm]
    rfl
  rw [Finset.sum_congr rfl fun i _ => he i, planCount_work hk hw]

/-- The certificate of the planner's counts. With weights between
`√(v_i/k_i)` and `θ √(v_i/k_i)`, where `v_i = 17 δ_i` and `k_i` is the cost of
one correction, the certificate is at most `δ_J² + θ (Σ_i √(v_i k_i))² / B`. -/
theorem planCertificate_le_of_weights {ρ B θ : ℝ} (hρ : 0 < ρ) (hB : 0 < B) {J : ℕ}
    {k w : Fin (J+1) → ℝ} (hk : ∀ i, 0 < k i)
    (hlow : ∀ i, Real.sqrt (17*levelAccuracy ρ i.val / k i) ≤ w i)
    (hup : ∀ i, w i ≤ θ * Real.sqrt (17*levelAccuracy ρ i.val / k i)) :
    planCertificate ρ (planRates B k w) ≤
      levelAccuracy ρ J ^ 2 +
        θ * (allocationCertificate (fun i : Fin (J+1) => 17*levelAccuracy ρ i.val) k) ^ 2 / B := by
  have hv : ∀ i : Fin (J+1), 0 < 17*levelAccuracy ρ i.val := fun i =>
    mul_pos (by norm_num) (levelAccuracy_pos hρ i.val)
  have hw : ∀ i, 0 < w i := fun i =>
    lt_of_lt_of_le (Real.sqrt_pos.mpr (div_pos (hv i) (hk i))) (hlow i)
  unfold planCertificate
  refine add_le_add le_rfl ?_
  have h := planCount_variance_le hB hv hk hlow hup
  simpa only [planRates_coe hB hk hw] using h

end ThresholdHC.KnownLawPlanner
