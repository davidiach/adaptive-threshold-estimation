import ThresholdHC.EntropyTailExecution.ScheduledFamily

/-! The level races of a plan, at the plan's own caps.

The scheduled family of the upper theorem runs level `l` at the least cap
`4^k` whose resolved error is at most `δ_l/8`. A plan may use any cap with
that property, for example one found from an upper bound of the resolved
error. For such caps the race of level `l` has error at most `δ_l`, the
correction of level `l` has second moment at most `17 δ_l`, and the expected
work of level `l` is at most

  `min{2 · 4^k, 128 (l+1) Γ + 6 H²/ρ + 2 O_τ(4^k) + 2 z 4^k}`.

`δ_l = ρ 16^{-(l+1)}`. The gap law is `σ + τ + ζ`: the selected core, the
resolved tail and the unresolved part. `Γ` is the cost entropy of the band
costs of `σ`, `H = ∫ d⁻¹ dτ`, `O_τ` is the ordinary work of `τ` and `z` the
mass of `ζ`. -/

noncomputable section
open MeasureTheory Real
open scoped NNReal BigOperators

namespace ThresholdHC.KnownLawPlanner
open ThresholdHC.Tier6 ThresholdHC.EntropyTailUpper ThresholdHC.EntropyTailAssembly
open ThresholdHC.EntropyTailSampling ThresholdHC.ObservableSimulation ThresholdHC.RareAboveTwo
open ThresholdHC.EntropyTailExecution

/-- The race of level `l`, run at the cap `4^(κ l)`. -/
def planFamily (μ : Measure Gap) [IsProbabilityMeasure μ] (w : ℕ → ℝ≥0) (hw : HasSum w 1)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4) (κ : ℕ → ℕ) (l : ℕ) : FiniteCall :=
  scheduledCall μ w hw hρ hρ1 l (2 * κ l)

/-- Every run of the level race buys at most `2 · 4^(κ l)` flips. -/
theorem planFamily_cost_bound (μ : Measure Gap) [IsProbabilityMeasure μ] (w : ℕ → ℝ≥0)
    (hw : HasSum w 1) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4) (κ : ℕ → ℕ) (l : ℕ) (ω : ℕ → Bool) :
    ((planFamily μ w hw hρ hρ1 κ l).cost ω:ℝ) ≤ 2 * 4 ^ κ l := by
  have h4 : (4:ℝ) ^ κ l = 2 ^ (2 * κ l) := by
    rw [pow_mul]
    norm_num
  rw [h4]
  unfold planFamily scheduledCall
  exact_mod_cast raceCost_le (negativeBankTest w (levelEpsilon l))
    (positiveBankTest μ w (ρ*levelEpsilon l)) (2 * κ l) ω

/-- The level race returns zero or one. -/
theorem planFamily_binary (μ : Measure Gap) [IsProbabilityMeasure μ] (w : ℕ → ℝ≥0)
    (hw : HasSum w 1) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4) (κ : ℕ → ℕ) (l : ℕ) (ω : ℕ → Bool) :
    (planFamily μ w hw hρ hρ1 κ l).value ω = 0 ∨ (planFamily μ w hw hρ hρ1 κ l).value ω = 1 :=
  raceValue_zero_or_one _ _ _ _

/-- The error of the level race at any cap `4^k` whose resolved error is at
most `δ_l/8`, when the unresolved mass is at most `δ_l/8`. -/
theorem plan_level_error (μ ν ζ : Measure Gap) [IsProbabilityMeasure μ]
    [IsFiniteMeasure ν] [IsFiniteMeasure ζ] (hμ : μ = ν+ζ)
    (weights : ℕ → ℝ≥0) (hw : HasSum weights 1) {ρ : ℝ} (hρ : 0 < ρ)
    (q : SignLaw) (hq : RarePrior μ ρ q) (l k : ℕ)
    (hk : eta ν (4 ^ k) ≤ levelAccuracy ρ l/8)
    (hz : ζ.real Set.univ ≤ levelAccuracy ρ l/8) :
    racePopulationError μ q (negativeBankTest weights (levelEpsilon l))
      (positiveBankTest μ weights (ρ*levelEpsilon l)) (2*k) ≤ levelAccuracy ρ l := by
  have h := bank_population_error_le μ weights hw (levelEpsilon_pos l).le
    (mul_pos hρ (levelEpsilon_pos l)).le q hq (2*k)
  change _ ≤ ρ*levelEpsilon l+ρ*levelEpsilon l+eta μ (Uniform713.cap (2*k)) at h
  rw [cap_twice, hμ, eta_add, levelEpsilon_accuracy] at h
  have hz' := eta_le_mass ζ ((4:ℝ)^k)
  have hδ := levelAccuracy_pos hρ l
  rw [hμ, levelEpsilon_accuracy]
  linarith

/-- The bias of the level race is at most `δ_l`. -/
theorem planFamily_bias (μ ν ζ : Measure Gap) [IsProbabilityMeasure μ]
    [IsFiniteMeasure ν] [IsFiniteMeasure ζ] (hμ : μ = ν+ζ)
    (w : ℕ → ℝ≥0) (hw : HasSum w 1) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4)
    (q : SignLaw) (hq : RarePrior μ ρ q) (κ : ℕ → ℕ) (l : ℕ)
    (hκ : eta ν (4 ^ κ l) ≤ levelAccuracy ρ l/8)
    (hz : ζ.real Set.univ ≤ levelAccuracy ρ l/8) :
    |(∫ ω, (planFamily μ w hw hρ hρ1 κ l).value ω ∂originalPopulationTapeLaw μ q)-
        signMean μ q.val| ≤ levelAccuracy ρ l :=
  (raceValue_bias_le μ q _ _ _).trans (plan_level_error μ ν ζ hμ w hw hρ q hq l (κ l) hκ hz)

/-- The correction of level `l` has second moment at most `17 δ_l`. -/
theorem planFamily_second (μ ν ζ : Measure Gap) [IsProbabilityMeasure μ]
    [IsFiniteMeasure ν] [IsFiniteMeasure ζ] (hμ : μ = ν+ζ)
    (w : ℕ → ℝ≥0) (hw : HasSum w 1) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4)
    (q : SignLaw) (hq : RarePrior μ ρ q) (κ : ℕ → ℕ) (l : ℕ)
    (hκ : ∀ j, j ≤ l → eta ν (4 ^ κ j) ≤ levelAccuracy ρ j/8)
    (hz : ζ.real Set.univ ≤ levelAccuracy ρ l/8) :
    (∫ ω, ((incrementCall (planFamily μ w hw hρ hρ1 κ) l).value ω)^2
      ∂originalPopulationTapeLaw μ q) ≤ 17*levelAccuracy ρ l := by
  cases l with
  | zero =>
    have he : (fun ω => ((incrementCall (planFamily μ w hw hρ hρ1 κ) 0).value ω)^2) =
        (planFamily μ w hw hρ hρ1 κ 0).value := by
      funext ω
      rcases planFamily_binary μ w hw hρ hρ1 κ 0 ω with h | h <;> simp [incrementCall,h]
    rw [he]
    have hb := (abs_le.mp (planFamily_bias μ ν ζ hμ w hw hρ hρ1 q hq κ 0 (hκ 0 le_rfl) hz)).2
    have hδ := levelAccuracy_zero ρ
    change signMean μ q.val ≤ ρ at hq
    linarith
  | succ l =>
    have hz' : ζ.real Set.univ ≤ levelAccuracy ρ l/8 :=
      hz.trans (div_le_div_of_nonneg_right (levelAccuracy_antitone hρ.le (by omega)) (by norm_num))
    have h := race_difference_population_moment μ q
      (negativeBankTest w (levelEpsilon (l+1))) (positiveBankTest μ w (ρ*levelEpsilon (l+1)))
      (negativeBankTest w (levelEpsilon l)) (positiveBankTest μ w (ρ*levelEpsilon l))
      (2 * κ (l+1)) (2 * κ l)
    change (∫ ω, ((incrementCall (planFamily μ w hw hρ hρ1 κ) (l+1)).value ω)^2
      ∂originalPopulationTapeLaw μ q) ≤ _ at h
    exact h.trans (by
      have he := add_le_add
        (plan_level_error μ ν ζ hμ w hw hρ q hq (l+1) (κ (l+1)) (hκ (l+1) le_rfl) hz)
        (plan_level_error μ ν ζ hμ w hw hρ q hq l (κ l) (hκ l (by omega)) hz')
      have hδ := levelAccuracy_succ ρ l
      linarith)

/-- The proved bound on the expected work of level `l` at the cap `4^k`. -/
def planLevelWork (τ : Measure Gap) (ρ Γ z : ℝ) (l k : ℕ) : ℝ :=
  128*(l+1)*Γ + 6*(∫ d : Gap, (d:ℝ)⁻¹ ∂τ)^2/ρ + 2*ordinaryCost τ (4 ^ k) + 2*z*4 ^ k

/-- The level price: the proved work bound, capped by the pathwise cost
`2 · 4^k` of the race. -/
def planLevelPrice (τ : Measure Gap) (ρ Γ z : ℝ) (l k : ℕ) : ℝ :=
  min (2 * 4 ^ k) (planLevelWork τ ρ Γ z l k)

/-- Expected work of the level race at the plan's cap. -/
theorem planFamily_work (σ τ ζ : Measure Gap)
    [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)]
    {t ρ : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ))
    (hN : ThresholdHC.EntropyTailQuantile.bandEdge N < t)
    (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4) (hz : ζ.real Set.univ ≤ ρ) (q : SignLaw)
    (hq : RarePrior (σ+τ+ζ) ρ q) (κ : ℕ → ℕ) (l : ℕ) :
    (∫ ω, ((planFamily (σ+τ+ζ) (referenceWeights σ)
      (referenceWeights_probability σ ht hs hN) hρ hρ1 κ l).cost ω:ℝ)
      ∂originalPopulationTapeLaw (σ+τ+ζ) q) ≤
      planLevelWork τ ρ (ThresholdHC.EntropyTailQuantile.costEntropy
        (fun j : Fin N => ThresholdHC.EntropyTailQuantile.bandCost σ j.val))
        (ζ.real Set.univ) l (κ l) := by
  rw [show (fun ω => ((planFamily (σ+τ+ζ) (referenceWeights σ)
      (referenceWeights_probability σ ht hs hN) hρ hρ1 κ l).cost ω:ℝ)) =
      fun ω => (raceCost (negativeBankTest (referenceWeights σ) (levelEpsilon l))
        (positiveBankTest (σ+τ+ζ) (referenceWeights σ) (ρ*levelEpsilon l))
        (2 * κ l) ω:ℝ) from rfl,
    race_population_work]
  have h := three_piece_level_work σ τ ζ ht hs hN hτ hρ hz q hq l (2 * κ l)
  simpa only [cap_twice, planLevelWork, mul_comm (ζ.real Set.univ), mul_assoc] using h

/-- Expected work of the level race is at most the level price. -/
theorem planFamily_price (σ τ ζ : Measure Gap)
    [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)]
    {t ρ : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ))
    (hN : ThresholdHC.EntropyTailQuantile.bandEdge N < t)
    (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4) (hz : ζ.real Set.univ ≤ ρ) (q : SignLaw)
    (hq : RarePrior (σ+τ+ζ) ρ q) (κ : ℕ → ℕ) (l : ℕ) :
    (∫ ω, ((planFamily (σ+τ+ζ) (referenceWeights σ)
      (referenceWeights_probability σ ht hs hN) hρ hρ1 κ l).cost ω:ℝ)
      ∂originalPopulationTapeLaw (σ+τ+ζ) q) ≤
      planLevelPrice τ ρ (ThresholdHC.EntropyTailQuantile.costEntropy
        (fun j : Fin N => ThresholdHC.EntropyTailQuantile.bandCost σ j.val))
        (ζ.real Set.univ) l (κ l) := by
  refine le_min ?_ (planFamily_work σ τ ζ ht hs hN hτ hρ hρ1 hz q hq κ l)
  have hK := planFamily_cost_bound (σ+τ+ζ) (referenceWeights σ)
    (referenceWeights_probability σ ht hs hN) hρ hρ1 κ l
  have h := integral_mono (call_cost_integrable (originalPopulationTapeLaw (σ+τ+ζ) q) _ hK)
    (integrable_const (μ := originalPopulationTapeLaw (σ+τ+ζ) q) ((2:ℝ) * 4 ^ κ l)) hK
  simpa using h

end ThresholdHC.KnownLawPlanner
