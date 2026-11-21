import ThresholdHC.UnknownLawConfidence.Item
import ThresholdHC.ArbitraryLawAdaptation.TailTestLaw

/-! The three outcome probabilities of one fresh item of the original population.

Conditioning on the latent pair, `p+ <= theta + tau`, `p- <= 1 - theta + tau` and
`p0 <= P(D <= 2r) + tau`, where `theta = signMean mu q`. The sign may depend
measurably on the gap. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Real
namespace ThresholdHC.UnknownLawConfidence
open ThresholdHC.Tier2 ThresholdHC.Tier6 ThresholdHC.CriticalEntropy
open ThresholdHC.ObservableSimulation ThresholdHC.ArbitraryLawAdaptation

/-- The mean of a bounded tape statistic under the original population tape law,
conditioned on the latent pair. -/
theorem original_tape_integral (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (G : (ℕ → Bool) → ℝ) (hG : Measurable G) {M : ℝ} (hb : ∀ t, |G t| ≤ M) :
    ∫ t, G t ∂originalPopulationTapeLaw μ q =
      ∫ d, q.val d * (∫ t, G t ∂tapeMeasure (gapParameter true d)) +
        (1 - q.val d) * (∫ t, G t ∂tapeMeasure (gapParameter false d)) ∂μ := by
  let κ := populationParameterLaw μ (gapParameter false) (gapParameter true) (signUnit q)
  let _ : IsProbabilityMeasure κ := populationParameterLaw_probability μ
    (gapParameter false) (gapParameter true) (signUnit q)
    (measurable_gapParameter false) (measurable_gapParameter true) (measurable_signUnit q)
  change (∫ t, G t ∂parameterTapeLaw κ) = _
  rw [parameterTape_integral κ G hG hb]
  rw [show κ = populationParameterLaw μ (gapParameter false) (gapParameter true)
      (signUnit q) from rfl,
    populationParameterLaw_integral μ _ _ _ (measurable_gapParameter false)
      (measurable_gapParameter true) (measurable_signUnit q)
      (fun p => ∫ t, G t ∂tapeMeasure p) (measurable_tape_integral G hG) M
      (fun p => tape_integral_abs_le p G hb)]
  rfl

/-- The probability of an outcome set under the original population tape law. -/
theorem original_tape_real (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    {A : Set (ℕ → Bool)} (hA : MeasurableSet A) :
    (originalPopulationTapeLaw μ q).real A =
      ∫ d, q.val d * (tapeMeasure (gapParameter true d)).real A +
        (1 - q.val d) * (tapeMeasure (gapParameter false d)).real A ∂μ := by
  have hb : ∀ t, |A.indicator (1 : (ℕ → Bool) → ℝ) t| ≤ 1 := by
    intro t
    by_cases h : t ∈ A <;> simp [h]
  rw [← integral_indicator_one hA,
    original_tape_integral μ q _ (measurable_one.indicator hA) hb]
  simp only [integral_indicator_one hA]

theorem signLaw_integrable (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    Integrable q.val μ := by
  apply (integrable_const (1 : ℝ)).mono' q.property.1.aestronglyMeasurable
  filter_upwards [] with d
  rw [Real.norm_of_nonneg (q.property.2 d).1]
  exact (q.property.2 d).2

theorem mixture_nonneg (q : SignLaw) (A : Set (ℕ → Bool)) (d : Gap) :
    0 ≤ q.val d * (tapeMeasure (gapParameter true d)).real A +
      (1 - q.val d) * (tapeMeasure (gapParameter false d)).real A := by
  have h0 := (q.property.2 d).1
  have h1 := (q.property.2 d).2
  have := measureReal_nonneg (μ := tapeMeasure (gapParameter true d)) (s := A)
  have := measureReal_nonneg (μ := tapeMeasure (gapParameter false d)) (s := A)
  have : 0 ≤ 1 - q.val d := by linarith
  positivity

/-- `p+ <= theta + tau`. -/
theorem positive_prob_le (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (j : ℕ) :
    (originalPopulationTapeLaw μ q).real (posSet j) ≤ signMean μ q.val + tolerance j := by
  rw [original_tape_real μ q (measurableSet_posSet j)]
  have hi : Integrable (fun d => q.val d + tolerance j) μ :=
    (signLaw_integrable μ q).add (integrable_const _)
  have hv : ∫ d, (q.val d + tolerance j) ∂μ = signMean μ q.val + tolerance j := by
    rw [integral_add (signLaw_integrable μ q) (integrable_const _), integral_const]
    simp [signMean]
  rw [← hv]
  apply integral_mono_of_nonneg (ae_of_all _ (mixture_nonneg q _)) hi (ae_of_all _ _)
  intro d
  have h0 := (q.property.2 d).1
  have h1 := (q.property.2 d).2
  have ht := pos_false_le j d
  have hu : (tapeMeasure (gapParameter true d)).real (posSet j) ≤ 1 := measureReal_le_one
  have hτ := (tolerance_pos j).le
  have : 0 ≤ 1 - q.val d := by linarith
  calc q.val d * (tapeMeasure (gapParameter true d)).real (posSet j) +
        (1 - q.val d) * (tapeMeasure (gapParameter false d)).real (posSet j)
      ≤ q.val d * 1 + (1 - q.val d) * tolerance j := by gcongr
    _ ≤ q.val d + tolerance j := by nlinarith

/-- `p- <= 1 - theta + tau`. -/
theorem negative_prob_le (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (j : ℕ) :
    (originalPopulationTapeLaw μ q).real (negSet j) ≤
      1 - signMean μ q.val + tolerance j := by
  rw [original_tape_real μ q (measurableSet_negSet j)]
  have hi : Integrable (fun d => 1 - q.val d + tolerance j) μ :=
    ((integrable_const _).sub (signLaw_integrable μ q)).add (integrable_const _)
  have hv : ∫ d, (1 - q.val d + tolerance j) ∂μ = 1 - signMean μ q.val + tolerance j := by
    rw [integral_add (f := fun d => 1 - q.val d) (g := fun _ => tolerance j)
      ((integrable_const _).sub (signLaw_integrable μ q)) (integrable_const _),
      integral_sub (f := fun _ => (1 : ℝ)) (g := q.val) (integrable_const _)
        (signLaw_integrable μ q), integral_const, integral_const]
    simp [signMean]
  rw [← hv]
  apply integral_mono_of_nonneg (ae_of_all _ (mixture_nonneg q _)) hi (ae_of_all _ _)
  intro d
  have h0 := (q.property.2 d).1
  have h1 := (q.property.2 d).2
  have ht := neg_true_le j d
  have hu : (tapeMeasure (gapParameter false d)).real (negSet j) ≤ 1 := measureReal_le_one
  have hτ := (tolerance_pos j).le
  have : 0 ≤ 1 - q.val d := by linarith
  calc q.val d * (tapeMeasure (gapParameter true d)).real (negSet j) +
        (1 - q.val d) * (tapeMeasure (gapParameter false d)).real (negSet j)
      ≤ q.val d * tolerance j + (1 - q.val d) * 1 := by gcongr
    _ ≤ 1 - q.val d + tolerance j := by nlinarith

/-- `p0 <= P(D <= 2r) + tau`. -/
theorem zero_prob_le (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (j : ℕ) :
    (originalPopulationTapeLaw μ q).real (zeroSet j) ≤
      μ.real {d : Gap | (d : ℝ) ≤ 2 * radius j} + tolerance j := by
  rw [original_tape_real μ q (measurableSet_zeroSet j)]
  let S := {d : Gap | (d : ℝ) ≤ 2 * radius j}
  have hS : MeasurableSet S := measurableSet_le measurable_subtype_coe measurable_const
  have hi1 : Integrable (S.indicator (1 : Gap → ℝ)) μ := (integrable_const (1 : ℝ)).indicator hS
  have hi : Integrable (fun d => S.indicator (1 : Gap → ℝ) d + tolerance j) μ :=
    hi1.add (integrable_const _)
  have hv : ∫ d, (S.indicator (1 : Gap → ℝ) d + tolerance j) ∂μ =
      μ.real S + tolerance j := by
    rw [integral_add (f := fun d => S.indicator (1 : Gap → ℝ) d) (g := fun _ => tolerance j)
      hi1 (integrable_const _), integral_indicator_one hS, integral_const]
    simp
  rw [← hv]
  apply integral_mono_of_nonneg (ae_of_all _ (mixture_nonneg q _)) hi (ae_of_all _ _)
  intro d
  dsimp only
  have h0 := (q.property.2 d).1
  have h1 := (q.property.2 d).2
  have hτ := (tolerance_pos j).le
  have : 0 ≤ 1 - q.val d := by linarith
  by_cases hd : d ∈ S
  · have hu : (tapeMeasure (gapParameter true d)).real (zeroSet j) ≤ 1 := measureReal_le_one
    have hu' : (tapeMeasure (gapParameter false d)).real (zeroSet j) ≤ 1 := measureReal_le_one
    rw [Set.indicator_of_mem hd]
    calc q.val d * (tapeMeasure (gapParameter true d)).real (zeroSet j) +
          (1 - q.val d) * (tapeMeasure (gapParameter false d)).real (zeroSet j)
        ≤ q.val d * 1 + (1 - q.val d) * 1 := by gcongr
      _ ≤ (1 : Gap → ℝ) d + tolerance j := by simp; linarith
  · have hlt : 2 * radius j < (d : ℝ) := lt_of_not_ge hd
    have ht := zero_true_le j hlt
    have hf := zero_false_le j hlt
    rw [Set.indicator_of_notMem hd]
    calc q.val d * (tapeMeasure (gapParameter true d)).real (zeroSet j) +
          (1 - q.val d) * (tapeMeasure (gapParameter false d)).real (zeroSet j)
        ≤ q.val d * tolerance j + (1 - q.val d) * tolerance j := by gcongr
      _ = 0 + tolerance j := by ring

end ThresholdHC.UnknownLawConfidence
