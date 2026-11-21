import ThresholdHC.TwoFlipFeedback.TwoGapLaw
import ThresholdHC.HardBudget.Controller

/-! Members of the noninteractive cap-two class: two genuine two-flip
schedules (the same coin twice, two fresh coins), and the zero-flip estimator
with constant output `1/8`, whose worst rare mean squared error is at most
`1/64`. So the class is nonempty and its minimax value is finite. -/

noncomputable section
namespace ThresholdHC.TwoFlipFeedback
open MeasureTheory
open scoped ENNReal
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.HardBudget

/-- Two flips of coin `0`. -/
def sameCoinEstimator : AdaptiveEstimator Unit where
  randomLaw := Measure.dirac ()
  probability := inferInstance
  policy := fun _ => stopAt 2 (fun _ => 0)
  policy_measurable := fun _ _ => measurableSet_eq_fun measurable_const measurable_const
  output := fun _ => 0
  output_measurable := measurable_const

/-- One flip each of the coins `0` and `1`. -/
def freshCoinEstimator : AdaptiveEstimator Unit where
  randomLaw := Measure.dirac ()
  probability := inferInstance
  policy := fun _ => stopAt 2 (fun xs => xs.length)
  policy_measurable := fun _ _ => measurableSet_eq_fun measurable_const measurable_const
  output := fun _ => 0
  output_measurable := measurable_const

/-- No flip and the constant output `1/8`. -/
def constantEstimator : AdaptiveEstimator Unit where
  randomLaw := Measure.dirac ()
  probability := inferInstance
  policy := fun _ _ => none
  policy_measurable := fun _ _ => measurableSet_eq_fun measurable_const measurable_const
  output := fun _ => 1/8
  output_measurable := measurable_const

theorem sameCoin_cap : PathwiseCap sameCoinEstimator 2 :=
  stopAt_pathwise_cap sameCoinEstimator 2 (fun _ => fun _ => 0) (fun _ => rfl)

theorem freshCoin_cap : PathwiseCap freshCoinEstimator 2 :=
  stopAt_pathwise_cap freshCoinEstimator 2 (fun _ => fun xs => xs.length) (fun _ => rfl)

theorem constant_cap : PathwiseCap constantEstimator 2 := by
  have h0 : PathwiseCap constantEstimator 0 :=
    stopAt_pathwise_cap constantEstimator 0 (fun _ => fun _ => 0)
      (fun _ => funext fun xs => by simp [constantEstimator, stopAt])
  intro r x hv
  exact (h0 r x hv).trans (by norm_num)

theorem sameCoin_noninteractive : NoninteractiveCapTwo sameCoinEstimator := by
  intro r c h
  have h0 : sameCoinEstimator.policy r [] = some 0 := rfl
  have hc : c = 0 := Option.some_injective _ (h.symm.trans h0)
  subst hc
  exact Or.inl fun b => Or.inr rfl

theorem freshCoin_noninteractive : NoninteractiveCapTwo freshCoinEstimator := by
  intro r c h
  have h0 : freshCoinEstimator.policy r [] = some 0 := rfl
  have hc : c = 0 := Option.some_injective _ (h.symm.trans h0)
  subst hc
  refine Or.inr ⟨fun b => ?_, rfl⟩
  change stopAt 2 (fun xs => xs.length) [b] ≠ some 0
  simp [stopAt]

theorem constant_noninteractive : NoninteractiveCapTwo constantEstimator := by
  intro r c h
  exact absurd h (by simp [constantEstimator])

theorem signMean_nonneg (q : SignLaw) : 0 ≤ signMean twoGapLaw q.val := by
  rw [signMean_twoGapLaw]
  linarith [(q.property.2 quarterGap).1, (q.property.2 eighthGap).1]

theorem constant_upper : rareSquaredRisk constantEstimator ≤ ENNReal.ofReal (1/64) := by
  unfold rareSquaredRisk
  refine iSup₂_le fun q hq => ?_
  have h0 := signMean_nonneg q
  have h1 : signMean twoGapLaw q.val ≤ 1/4 := hq
  unfold squaredRisk
  simp only [populationOutput, constantEstimator]
  rw [lintegral_const, measure_univ, mul_one]
  apply ENNReal.ofReal_le_ofReal
  nlinarith

theorem minimax_le : noninteractiveMinimax ≤ ENNReal.ofReal (1/64) := by
  unfold noninteractiveMinimax
  refine (sInf_le ?_).trans constant_upper
  exact ⟨Unit, inferInstance, constantEstimator, constant_cap, constant_noninteractive, rfl⟩

end ThresholdHC.TwoFlipFeedback
