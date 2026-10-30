import ThresholdHC.EntropyTailAssembly.LevelCertificates
import ThresholdHC.RareAboveTwo.Increment

/-! Bias and coupled second moments for the raced classifiers under the
original population tape law. Adjacent decisions share the same coin prefix. -/

noncomputable section
open MeasureTheory Set Real

namespace ThresholdHC.EntropyTailSampling
open ThresholdHC ThresholdHC.Tier6 ThresholdHC.EntropyTailUpper ThresholdHC.EntropyTailAssembly
open ThresholdHC.ObservableSimulation ThresholdHC.RareAboveTwo
open ThresholdHC.CriticalEntropy ThresholdHC.Uniform713

theorem race_error_integral (neg pos : PrefixTest) (L : ℕ) (s : Bool) (d : Gap) :
    raceConditionalError neg pos L s d =
      ∫ ω, |raceValue neg pos L ω-Tier2.bit s| ∂Tier2.tapeMeasure (gapParameter s d) :=
  (integral_binary_error (measurable_raceValue neg pos L) measurable_const
    (raceValue_zero_or_one neg pos L) (fun _ => by cases s <;> simp [Tier2.bit])).symm

def raceMean (neg pos : PrefixTest) (L : ℕ) (s : Bool) (d : Gap) : ℝ :=
  ∫ ω, raceValue neg pos L ω ∂Tier2.tapeMeasure (gapParameter s d)

theorem raceValue_bounds (neg pos : PrefixTest) (L : ℕ) (ω : ℕ → Bool) :
    raceValue neg pos L ω ∈ Icc (0:ℝ) 1 := by
  rcases raceValue_zero_or_one neg pos L ω with h | h <;> simp [h]

theorem raceMean_bounds (neg pos : PrefixTest) (L : ℕ) (s : Bool) (d : Gap) :
    raceMean neg pos L s d ∈ Icc (0:ℝ) 1 := by
  refine ⟨integral_nonneg (fun ω => (raceValue_bounds neg pos L ω).1), ?_⟩
  have h := integral_mono (integrable_binary (measurable_raceValue neg pos L) (raceValue_zero_or_one neg pos L))
    (integrable_const (μ := Tier2.tapeMeasure (gapParameter s d)) (1:ℝ))
    (fun ω => (raceValue_bounds neg pos L ω).2)
  simpa only [raceMean, integral_const, probReal_univ, smul_eq_mul, one_mul] using h

theorem measurable_raceMean (neg pos : PrefixTest) (L : ℕ) (s : Bool) :
    Measurable (raceMean neg pos L s) :=
  (CriticalUpper.measurable_tape_integral _ (measurable_raceValue neg pos L)).comp (measurable_gapParameter s)

theorem raceMean_bias (neg pos : PrefixTest) (L : ℕ) (s : Bool) (d : Gap) :
    |raceMean neg pos L s d-Tier2.bit s| ≤ raceConditionalError neg pos L s d := by
  rw [race_error_integral]
  calc
    _ = |∫ ω, raceValue neg pos L ω-Tier2.bit s ∂Tier2.tapeMeasure (gapParameter s d)| := by
      rw [integral_sub (integrable_binary (measurable_raceValue neg pos L) (raceValue_zero_or_one neg pos L))
        (integrable_const _)]
      simp [raceMean]
    _ ≤ _ := abs_integral_le_integral_abs

theorem raceValue_bias_le (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (neg pos : PrefixTest) (L : ℕ) :
    |(∫ ω, raceValue neg pos L ω ∂originalPopulationTapeLaw μ q)-signMean μ q.val| ≤
      racePopulationError μ q neg pos L := by
  let m := raceMean neg pos L
  have hm : Integrable (fun d => q.val d*m true d+(1-q.val d)*m false d) μ := by
    apply Integrable.of_bound ((q.property.1.mul (measurable_raceMean neg pos L true)).add
      ((measurable_const.sub q.property.1).mul (measurable_raceMean neg pos L false))).aestronglyMeasurable 1
    apply ae_of_all
    intro d
    have hp := raceMean_bounds neg pos L true d
    have hn := raceMean_bounds neg pos L false d
    have hq := q.property.2 d
    change ‖q.val d*m true d+(1-q.val d)*m false d‖ ≤ 1
    rw [Real.norm_of_nonneg (add_nonneg (mul_nonneg hq.1 hp.1) (mul_nonneg (by linarith) hn.1))]
    nlinarith [mul_le_mul_of_nonneg_left hp.2 hq.1,
      mul_le_mul_of_nonneg_left hn.2 (sub_nonneg.mpr hq.2)]
  have hqi := integrable_signLaw μ q
  have he := integral_sub hm hqi
  rw [originalTape_integral_mixture μ q _ (measurable_raceValue neg pos L) 1
    (fun ω => by rw [abs_of_nonneg (raceValue_bounds neg pos L ω).1]; exact (raceValue_bounds neg pos L ω).2)]
  change |(∫ d, q.val d*m true d+(1-q.val d)*m false d ∂μ)-(∫ d, q.val d ∂μ)| ≤ _
  rw [← he]
  apply abs_integral_le_integral_abs.trans
  apply integral_mono (hm.sub hqi).abs (integrable_racePopulationError μ q neg pos L)
  intro d
  have hp := abs_le.mp (raceMean_bias neg pos L true d)
  have hn := abs_le.mp (raceMean_bias neg pos L false d)
  simp only [Tier2.bit, ite_true, Bool.false_eq_true, ite_false, sub_zero] at hp hn
  have hp0 := mul_le_mul_of_nonneg_left hp.1 (q.property.2 d).1
  have hp1 := mul_le_mul_of_nonneg_left hp.2 (q.property.2 d).1
  have hn0 := mul_le_mul_of_nonneg_left hn.1 (sub_nonneg.mpr (q.property.2 d).2)
  have hn1 := mul_le_mul_of_nonneg_left hn.2 (sub_nonneg.mpr (q.property.2 d).2)
  dsimp only [m, Pi.add_apply, Pi.sub_apply]
  apply abs_le.mpr
  constructor <;> nlinarith only [hp0, hp1, hn0, hn1]

theorem race_difference_sq_integrable (ν : Measure (ℕ → Bool)) [IsProbabilityMeasure ν]
    (neg pos neg' pos' : PrefixTest) (L L' : ℕ) :
    Integrable (fun ω => (raceValue neg pos L ω-raceValue neg' pos' L' ω)^2) ν := by
  apply Integrable.of_bound
    (((measurable_raceValue neg pos L).sub (measurable_raceValue neg' pos' L')).pow_const 2).aestronglyMeasurable 1
  exact ae_of_all _ (fun ω => by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact binary_difference_sq_le_one _ _ (raceValue_zero_or_one neg pos L ω) (raceValue_zero_or_one neg' pos' L' ω))

theorem race_difference_coin_moment (neg pos neg' pos' : PrefixTest) (L L' : ℕ) (s : Bool) (d : Gap) :
    (∫ ω, (raceValue neg pos L ω-raceValue neg' pos' L' ω)^2 ∂Tier2.tapeMeasure (gapParameter s d)) ≤
      raceConditionalError neg pos L s d+raceConditionalError neg' pos' L' s d := by
  have hi := ((integrable_binary (μ := Tier2.tapeMeasure (gapParameter s d))
    (measurable_raceValue neg pos L) (raceValue_zero_or_one neg pos L)).sub (integrable_const (Tier2.bit s))).abs
  have hi' := ((integrable_binary (μ := Tier2.tapeMeasure (gapParameter s d))
    (measurable_raceValue neg' pos' L') (raceValue_zero_or_one neg' pos' L')).sub (integrable_const (Tier2.bit s))).abs
  dsimp only [Pi.sub_apply] at hi hi'
  rw [race_error_integral, race_error_integral, ← integral_add hi hi']
  apply integral_mono (race_difference_sq_integrable _ neg pos neg' pos' L L') (hi.add hi')
  exact fun ω => binary_difference_sq_le _ _ (raceValue_zero_or_one neg pos L ω) (raceValue_zero_or_one neg' pos' L' ω) s

theorem race_difference_population_moment (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (neg pos neg' pos' : PrefixTest) (L L' : ℕ) :
    (∫ ω, (raceValue neg pos L ω-raceValue neg' pos' L' ω)^2 ∂originalPopulationTapeLaw μ q) ≤
      racePopulationError μ q neg pos L+racePopulationError μ q neg' pos' L' := by
  have hF : Measurable (fun ω => (raceValue neg pos L ω-raceValue neg' pos' L' ω)^2) :=
    ((measurable_raceValue neg pos L).sub (measurable_raceValue neg' pos' L')).pow_const 2
  have hb (ω) : |(raceValue neg pos L ω-raceValue neg' pos' L' ω)^2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact binary_difference_sq_le_one _ _ (raceValue_zero_or_one neg pos L ω) (raceValue_zero_or_one neg' pos' L' ω)
  rw [originalTape_integral_mixture μ q _ hF 1 hb]
  have hi := integrable_racePopulationError μ q neg pos L
  have hi' := integrable_racePopulationError μ q neg' pos' L'
  unfold racePopulationError
  rw [← integral_add hi hi']
  apply integral_mono_of_nonneg ?_ (hi.add hi') ?_
  · exact ae_of_all _ (fun d => add_nonneg
      (mul_nonneg (q.property.2 d).1 (integral_nonneg (fun _ => sq_nonneg _)))
      (mul_nonneg (sub_nonneg.mpr (q.property.2 d).2) (integral_nonneg (fun _ => sq_nonneg _))))
  · apply ae_of_all
    intro d
    have hp := mul_le_mul_of_nonneg_left (race_difference_coin_moment neg pos neg' pos' L L' true d) (q.property.2 d).1
    have hn := mul_le_mul_of_nonneg_left (race_difference_coin_moment neg pos neg' pos' L L' false d)
      (sub_nonneg.mpr (q.property.2 d).2)
    dsimp only [Pi.add_apply]
    nlinarith only [hp, hn]

theorem race_population_work (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (neg pos : PrefixTest) (L : ℕ) :
    (∫ ω, (raceCost neg pos L ω:ℝ) ∂originalPopulationTapeLaw μ q) =
      ∫ d, mixtureRaceWork q neg pos L d ∂μ := by
  exact originalTape_integral_mixture μ q _
    ((measurable_of_countable (fun n : ℕ => (n:ℝ))).comp (measurable_raceCost neg pos L))
    (2*(2^L)) (fun ω => by
      rw [abs_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast raceCost_le neg pos L ω)

end ThresholdHC.EntropyTailSampling
