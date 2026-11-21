import ThresholdHC.KnownGapRarity.Cap
import ThresholdHC.KnownGapRarity.Miss
import ThresholdHC.FixedPlan.Output

/-! Work and mean squared error of the known-gap estimator.

At the gap law `delta_d` a coin's majority vote has mean `p = f + (1-2f) theta`,
so the debiased share `(Zbar - f)/(1-2f)` is unbiased and its mean squared error
is `Var(Z)/(n (1-2f)^2) <= 4 (theta + f)/n`, using `Var(Z) <= E Z^2 = p <= theta + f`
and `1 - 2f >= 1/2`. With `n >= B/(2m)` and `f <= 1/(2B)` this is at most
`8 m theta/B + 4 m/B^2`. For `B < 2m` the output is `0`, with error `theta^2`,
which is below the same bound. Clipping to `[0,1]` does not increase the error. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ThresholdHC.KnownGapRarity
open ThresholdHC.Tier6 ThresholdHC.FixedPlan ThresholdHC.HardBudget
open ThresholdHC.ObservableSimulation

theorem signMean_dirac (d : Gap) (q : SignLaw) : signMean (Measure.dirac d) q.val = q.val d := by
  simp [signMean]

/-- Mean majority vote at a one-point gap law: `p = f + (1-2f) theta`. -/
theorem vote_mean_dirac (k : ℕ) (d : Gap) (q : SignLaw) :
    ∫ ω, majorityVote k ω ∂originalPopulationTapeLaw (Measure.dirac d) q =
      majorityMiss k d + (1 - 2 * majorityMiss k d) * q.val d := by
  rw [majorityVote_population_mean]
  simp only [integral_dirac]
  ring

/-- A binary variable has variance at most its mean. -/
theorem vote_variance_le (k : ℕ) (P : Measure (ℕ → Bool)) [IsProbabilityMeasure P] :
    variance (majorityVote k) P ≤ ∫ ω, majorityVote k ω ∂P := by
  refine (variance_le_expectation_sq (measurable_majorityVote k).aestronglyMeasurable).trans
    (le_of_eq ?_)
  apply integral_congr_ae
  filter_upwards with ω
  rcases majorityVote_binary k ω with h | h <;> simp [h]

/-- The squared error of the debiased share is a rescaled squared error of the
plain share, about the vote mean `f + (1-2f) theta`. -/
theorem debiased_squaredRisk (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (k n : ℕ) (f θ : ℝ) (hf : 2*f < 1) :
    squaredRisk (experimentLaw μ (debiased k n f) q) (populationOutput (debiased k n f)) θ =
      ENNReal.ofReal (((1 - 2*f)^2)⁻¹) *
        squaredRisk (experimentLaw μ (majorityEstimator k n) q)
          (populationOutput (majorityEstimator k n)) (f + (1 - 2*f) * θ) := by
  unfold squaredRisk
  rw [debiased_experimentLaw, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro z
  rw [debiased_populationOutput, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hc : 1 - 2*f ≠ 0 := by linarith
  have h : (populationOutput (majorityEstimator k n) z - f) / (1 - 2*f) - θ =
      (populationOutput (majorityEstimator k n) z - (f + (1 - 2*f) * θ)) / (1 - 2*f) := by
    rw [eq_div_iff hc, sub_mul, div_mul_cancel₀ _ hc]
    ring
  rw [h, div_pow, div_eq_inv_mul]

/-- Mean squared error of the debiased plan at `delta_d`: at most `4 (theta + f)/n`. -/
theorem debiased_risk_le (q : SignLaw) (d : Gap) (k n : ℕ) (hn : 0 < n)
    (hf : 1/2 ≤ 1 - 2 * majorityMiss k d) :
    squaredRisk (experimentLaw (Measure.dirac d) (debiased k n (majorityMiss k d)) q)
      (populationOutput (debiased k n (majorityMiss k d))) (q.val d) ≤
      ENNReal.ofReal (4 * (q.val d + majorityMiss k d) / n) := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hf0 := majorityMiss_nonneg k d
  have hθ0 := (q.property.2 d).1
  have hθ1 := (q.property.2 d).2
  have hv := vote_variance_le k (originalPopulationTapeLaw (Measure.dirac d) q)
  have hv0 : 0 ≤ variance (majorityVote k) (originalPopulationTapeLaw (Measure.dirac d) q) :=
    variance_nonneg _ _
  rw [vote_mean_dirac] at hv
  rw [debiased_squaredRisk _ _ _ _ _ _ (by linarith), majority_output_squaredRisk,
    vote_mean_dirac, sub_self, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  set f := majorityMiss k d
  set V := variance (majorityVote k) (originalPopulationTapeLaw (Measure.dirac d) q)
  have hp : (0 : ℝ) < (n' : ℝ) + 1 := by positivity
  have h4 : ((1 - 2*f)^2)⁻¹ ≤ 4 := by
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    nlinarith
  have hVθ : V ≤ q.val d + f := by nlinarith
  have hdiv : V / ((n' : ℝ) + 1) ≤ (q.val d + f) / ((n' : ℝ) + 1) :=
    div_le_div_of_nonneg_right hVθ hp.le
  push_cast
  calc ((1 - 2*f)^2)⁻¹ * (V / ((n' : ℝ) + 1) + 0^2)
      = ((1 - 2*f)^2)⁻¹ * (V / ((n' : ℝ) + 1)) := by ring
    _ ≤ 4 * ((q.val d + f) / ((n' : ℝ) + 1)) :=
      mul_le_mul h4 hdiv (by positivity) (by norm_num)
    _ = 4 * (q.val d + f) / ((n' : ℝ) + 1) := by ring

/-- The arithmetic step `4 (theta + f)/n <= 8 m theta/B + 4 m/B^2`. -/
theorem risk_arith {θ f m n B : ℝ} (hθ : 0 ≤ θ) (hf : f ≤ 1/(2*B)) (hm : 0 < m)
    (hB : 0 < B) (hn : B / (2*m) ≤ n) :
    4 * (θ + f) / n ≤ 8 * m * θ / B + 4 * m / B^2 := by
  have hn0 : 0 < n := lt_of_lt_of_le (by positivity) hn
  rw [div_le_iff₀ hn0]
  have h4f : 4 * f ≤ 2 / B := by
    have : 4 * (1/(2*B)) = 2 / B := by field_simp; ring
    linarith
  calc 4 * (θ + f) ≤ 4 * θ + 2 / B := by linarith
    _ = (8 * m * θ / B + 4 * m / B^2) * (B / (2*m)) := by field_simp; ring
    _ ≤ (8 * m * θ / B + 4 * m / B^2) * n := mul_le_mul_of_nonneg_left hn (by positivity)

/-- An estimator with output identically `0` has squared error `theta^2`. -/
theorem zero_output_risk {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (hA : ∀ z, A.output z = 0) (q : SignLaw) (θ : ℝ) :
    squaredRisk (experimentLaw μ A q) (populationOutput A) θ = ENNReal.ofReal (θ^2) := by
  unfold squaredRisk
  have h : ∀ z, populationOutput A z = 0 := fun z => hA _
  simp_rw [h]
  rw [lintegral_const, measure_univ, mul_one]
  congr 1
  ring

/-- The raw estimate obeys the bound `8 m theta/B + 4 m/B^2` in both regimes. -/
theorem rawEstimator_risk_le (d : Gap) {B : ℝ} (hB : 1 ≤ B) (q : SignLaw) :
    squaredRisk (experimentLaw (Measure.dirac d) (rawEstimator d B) q)
          (populationOutput (rawEstimator d B)) (signMean (Measure.dirac d) q.val) ≤
        ENNReal.ofReal (8 * (flipCount d B : ℝ) * signMean (Measure.dirac d) q.val / B
          + 4 * (flipCount d B : ℝ) / B^2) := by
  rw [signMean_dirac]
  have hθ0 := (q.property.2 d).1
  have hθ1 := (q.property.2 d).2
  have hm := flipCount_cast_pos d B
  by_cases h : 2 * (flipCount d B : ℝ) ≤ B
  · rw [rawEstimator_of_le h]
    refine (debiased_risk_le q d _ _ (coinCount_pos h) (one_sub_two_missRate h)).trans ?_
    apply ENNReal.ofReal_le_ofReal
    have hn := coinCount_ge h
    exact risk_arith hθ0 (missRate_le d (by linarith)) hm (by linarith) hn
  · have hlt := lt_of_not_ge h
    rw [zero_output_risk _ _ (rawEstimator_output_of_lt hlt)]
    apply ENNReal.ofReal_le_ofReal
    have hB0 : 0 < B := by linarith
    have h1 : q.val d ≤ 8 * (flipCount d B : ℝ) * q.val d / B := by
      rw [le_div_iff₀ hB0]
      nlinarith
    have h2 : 0 ≤ 4 * (flipCount d B : ℝ) / B^2 := by positivity
    nlinarith

/-- The known-gap estimator obeys the bound `8 m theta/B + 4 m/B^2`. -/
theorem knownGap_risk_le (d : Gap) {B : ℝ} (hB : 1 ≤ B) (q : SignLaw) :
    squaredRisk (experimentLaw (Measure.dirac d) (knownGapEstimator d B) q)
          (populationOutput (knownGapEstimator d B)) (signMean (Measure.dirac d) q.val) ≤
        ENNReal.ofReal (8 * (flipCount d B : ℝ) * signMean (Measure.dirac d) q.val / B
          + 4 * (flipCount d B : ℝ) / B^2) :=
  (ClippedOutput.unitClip_squaredRisk_le (Measure.dirac d) (rawEstimator d B) q).trans
    (rawEstimator_risk_le d hB q)

/-- The expected work is at most `B` for every sign law. -/
theorem knownGap_uniformBudget (d : Gap) {B : ℝ} (hB : 0 ≤ B) :
    UniformBudget (Measure.dirac d) (knownGapEstimator d B) B := by
  intro q
  change expectedWork (Measure.dirac d) (rawEstimator d B) q ≤ _
  by_cases h : 2 * (flipCount d B : ℝ) ≤ B
  · rw [rawEstimator_of_le h, debiased_expectedWork, majority_expectedWork, ← ENNReal.ofReal_natCast]
    apply ENNReal.ofReal_le_ofReal
    have hc := coinCount_mul_le d hB
    unfold flipCount at hc
    push_cast at hc ⊢
    exact hc
  · rw [rawEstimator_of_lt (lt_of_not_ge h), majority_expectedWork]
    simp

end ThresholdHC.KnownGapRarity
