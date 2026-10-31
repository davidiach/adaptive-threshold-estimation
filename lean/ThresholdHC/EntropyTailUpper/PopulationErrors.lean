import ThresholdHC.EntropyTailUpper.BankRace
import ThresholdHC.RareAboveTwo.PopulationError

/-! Errors of the actual raced classifier under every globally rare prior.
The positive-bank allowance is integrated against the full null mixture. -/

noncomputable section
open MeasureTheory Set Real
open scoped ENNReal NNReal

namespace ThresholdHC.EntropyTailUpper
open ThresholdHC ThresholdHC.Tier2 ThresholdHC.Tier6 ThresholdHC.ObservableSimulation
open ThresholdHC.RareAboveTwo

theorem measurableSet_everPrefixHit (hit : PrefixTest) : MeasurableSet (everPrefixHit hit) := by
  rw [everPrefixHit_eq_iUnion]
  exact MeasurableSet.iUnion (measurableSet_firstPrefixHit hit)

def tapeEventProbability (s : Bool) (E : Set (ℕ → Bool)) (d : Gap) : ℝ :=
  (tapeMeasure (gapParameter s d)).real E

theorem measurable_tapeEventProbability (s : Bool) {E : Set (ℕ → Bool)} (hE : MeasurableSet E) :
    Measurable (tapeEventProbability s E) := by
  have h := (CriticalUpper.measurable_tape_integral (E.indicator (fun _ => (1:ℝ)))
    (measurable_const.indicator hE)).comp (measurable_gapParameter s)
  change Measurable (fun d : Gap => (tapeMeasure (gapParameter s d)).real E)
  simpa only [Function.comp_def, integral_indicator_const _ hE, smul_eq_mul, mul_one,
    tapeEventProbability] using h

theorem integrable_tapeEventProbability (μ : Measure Gap) [IsFiniteMeasure μ]
    (s : Bool) {E : Set (ℕ → Bool)} (hE : MeasurableSet E) :
    Integrable (tapeEventProbability s E) μ := by
  apply Integrable.of_bound (measurable_tapeEventProbability s hE).aestronglyMeasurable 1
  exact ae_of_all _ (fun d => by
    change ‖(tapeMeasure (gapParameter s d)).real E‖ ≤ 1
    rw [Real.norm_of_nonneg (measureReal_nonneg : 0 ≤ tapeEventProbability s E d)]
    exact measureReal_le_one)

theorem null_event_mixture (μ : Measure Gap) [IsProbabilityMeasure μ]
    {E : Set (ℕ → Bool)} (hE : MeasurableSet E) :
    (allNegativeLaw μ).real E = ∫ d, tapeEventProbability false E d ∂μ := by
  have h := originalTape_integral_mixture μ allNegativeSignLaw (E.indicator (fun _ => (1:ℝ)))
    (measurable_const.indicator hE) 1 (fun ω => by
      by_cases hω : ω ∈ E <;> simp [Set.indicator, hω])
  simpa only [integral_indicator_const _ hE, smul_eq_mul, mul_one, allNegativeSignLaw, zero_mul, sub_zero,
    one_mul, zero_add, allNegativeLaw, tapeEventProbability] using h

theorem parityTape_event (b : Fin 2) (p : unitInterval) {E : Set (ℕ → Bool)} (hE : MeasurableSet E) :
    (tapeMeasure p).real (parityTape b ⁻¹' E) = (tapeMeasure p).real E := by
  unfold Measure.real
  rw [← Measure.map_apply (measurable_parityTape b) hE, (parityTape_measurePreserving b p).map_eq]

def raceConditionalError (neg pos : PrefixTest) (L : ℕ) (s : Bool) (d : Gap) : ℝ :=
  tapeEventProbability s {ω | raceValue neg pos L ω ≠ bit s} d

theorem measurable_raceConditionalError (neg pos : PrefixTest) (L : ℕ) (s : Bool) :
    Measurable (raceConditionalError neg pos L s) :=
  measurable_tapeEventProbability s (measurableSet_eq_fun (measurable_raceValue neg pos L) measurable_const).compl

theorem race_error_positive_bound (neg pos : PrefixTest) (L : ℕ) (d : Gap) :
    raceConditionalError neg pos L true d ≤ tapeEventProbability true (everPrefixHit neg) d +
      ordinaryErrorKernel (Uniform713.cap L) (d:ℝ) := by
  have h := (measureReal_mono (μ := tapeMeasure (gapParameter true d))
    (race_error_positive_subset neg pos L)).trans (measureReal_union_le _ _)
  rw [parityTape_event 0 _ (measurableSet_everPrefixHit neg),
    parityTape_event 1 _ (E := {ω | BlindUpper.classifierValue L ω ≠ 1})
      (measurableSet_eq_fun (BlindUpper.measurable_classifierValue L) measurable_const).compl] at h
  exact h.trans (add_le_add le_rfl (ordinary_conditional_error L d true))

theorem race_error_negative_bound (neg pos : PrefixTest) (L : ℕ) (d : Gap) :
    raceConditionalError neg pos L false d ≤ tapeEventProbability false (everPrefixHit pos) d +
      ordinaryErrorKernel (Uniform713.cap L) (d:ℝ) := by
  have h := (measureReal_mono (μ := tapeMeasure (gapParameter false d))
    (race_error_negative_subset neg pos L)).trans (measureReal_union_le _ _)
  rw [parityTape_event 0 _ (measurableSet_everPrefixHit pos),
    parityTape_event 1 _ (E := {ω | BlindUpper.classifierValue L ω ≠ 0})
      (measurableSet_eq_fun (BlindUpper.measurable_classifierValue L) measurable_const).compl] at h
  exact h.trans (add_le_add le_rfl (ordinary_conditional_error L d false))

theorem negative_bank_probability (weights : ℕ → ℝ≥0) (hw : HasSum weights 1)
    {ε : ℝ} (hε : 0 ≤ ε) (d : Gap) :
    tapeEventProbability true (everPrefixHit (negativeBankTest weights ε)) d ≤ ε := by
  have h := negative_bank_error weights hw hε (gapParameter true d)
    (by change (1/2:ℝ) ≤ 1/2+(d:ℝ); linarith [d.property.1])
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rw [ENNReal.toReal_ofReal hε] at ht
  simpa only [tapeEventProbability, Measure.real, ever_negativeBankTest] using ht

theorem positive_bank_integrated_probability (μ : Measure Gap) [IsProbabilityMeasure μ]
    (weights : ℕ → ℝ≥0) (hw : HasSum weights 1) {u : ℝ} (hu : 0 ≤ u) :
    (∫ d, tapeEventProbability false (everPrefixHit (positiveBankTest μ weights u)) d ∂μ) ≤ u := by
  rw [← null_event_mixture μ (measurableSet_everPrefixHit _), ever_positiveBankTest]
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (positive_bank_error μ weights hw u)
  simpa only [Measure.real, ENNReal.toReal_ofReal hu] using h

def racePopulationError (μ : Measure Gap) (q : SignLaw) (neg pos : PrefixTest) (L : ℕ) : ℝ :=
  ∫ d, q.val d*raceConditionalError neg pos L true d +
    (1-q.val d)*raceConditionalError neg pos L false d ∂μ

theorem integrable_racePopulationError (μ : Measure Gap) [IsFiniteMeasure μ]
    (q : SignLaw) (neg pos : PrefixTest) (L : ℕ) :
    Integrable (fun d => q.val d*raceConditionalError neg pos L true d +
      (1-q.val d)*raceConditionalError neg pos L false d) μ := by
  apply Integrable.of_bound
    ((q.property.1.mul (measurable_raceConditionalError neg pos L true)).add
      ((measurable_const.sub q.property.1).mul (measurable_raceConditionalError neg pos L false))).aestronglyMeasurable 1
  refine ae_of_all _ (fun d => ?_)
  have ht : raceConditionalError neg pos L true d ∈ Icc (0:ℝ) 1 := ⟨measureReal_nonneg, measureReal_le_one⟩
  have hf : raceConditionalError neg pos L false d ∈ Icc (0:ℝ) 1 := ⟨measureReal_nonneg, measureReal_le_one⟩
  have hq := q.property.2 d
  change ‖q.val d*raceConditionalError neg pos L true d +
    (1-q.val d)*raceConditionalError neg pos L false d‖ ≤ 1
  rw [Real.norm_of_nonneg (add_nonneg (mul_nonneg hq.1 ht.1) (mul_nonneg (by linarith) hf.1))]
  nlinarith [mul_le_mul_of_nonneg_left ht.2 hq.1, mul_le_mul_of_nonneg_left hf.2 (by linarith : 0 ≤ 1-q.val d)]

theorem integrable_ordinaryErrorKernel (μ : Measure Gap) [IsFiniteMeasure μ] (M : ℝ) :
    Integrable (fun d : Gap => ordinaryErrorKernel M (d:ℝ)) μ := by
  apply Integrable.of_bound (show Measurable (fun d : Gap => ordinaryErrorKernel M (d:ℝ)) by
    unfold ordinaryErrorKernel; fun_prop).aestronglyMeasurable 1
  exact ae_of_all _ (fun d => by
    rw [Real.norm_of_nonneg (by unfold ordinaryErrorKernel; positivity)]
    exact min_le_left _ _)

theorem bank_population_error_le (μ : Measure Gap) [IsProbabilityMeasure μ]
    (weights : ℕ → ℝ≥0) (hw : HasSum weights 1) {ε u ρ : ℝ}
    (hε : 0 ≤ ε) (hu : 0 ≤ u) (q : SignLaw) (hq : RarePrior μ ρ q) (L : ℕ) :
    racePopulationError μ q (negativeBankTest weights ε) (positiveBankTest μ weights u) L ≤
      ρ*ε + u + ∫ d : Gap, ordinaryErrorKernel (Uniform713.cap L) (d:ℝ) ∂μ := by
  let neg := negativeBankTest weights ε
  let pos := positiveBankTest μ weights u
  let e := fun d : Gap => ordinaryErrorKernel (Uniform713.cap L) (d:ℝ)
  let k := tapeEventProbability false (everPrefixHit pos)
  have hqi : Integrable q.val μ := by
    apply Integrable.of_bound q.property.1.aestronglyMeasurable 1
    exact ae_of_all _ (fun d => by rw [Real.norm_of_nonneg (q.property.2 d).1]; exact (q.property.2 d).2)
  have hki := integrable_tapeEventProbability μ false (measurableSet_everPrefixHit pos)
  have hei := integrable_ordinaryErrorKernel μ (Uniform713.cap L)
  have hpt (d : Gap) : q.val d*raceConditionalError neg pos L true d +
      (1-q.val d)*raceConditionalError neg pos L false d ≤ q.val d*ε+k d+e d := by
    have hp := (race_error_positive_bound neg pos L d).trans
      (add_le_add (negative_bank_probability weights hw hε d) le_rfl)
    have hn := race_error_negative_bound neg pos L d
    have h1 := mul_le_mul_of_nonneg_left hp (q.property.2 d).1
    have h2 := mul_le_mul_of_nonneg_left hn (sub_nonneg.mpr (q.property.2 d).2)
    have h3 := mul_nonneg (q.property.2 d).1 (show 0 ≤ k d from measureReal_nonneg)
    dsimp [e, k]
    nlinarith only [h1, h2, h3]
  have h := integral_mono (integrable_racePopulationError μ q neg pos L)
    (((hqi.mul_const ε).add hki).add hei) hpt
  dsimp only [Pi.add_apply, Pi.mul_apply] at h
  have hs1 := integral_add ((hqi.mul_const ε).add hki) hei
  have hs2 := integral_add (hqi.mul_const ε) hki
  dsimp only [Pi.add_apply, Pi.mul_apply] at hs1 hs2
  rw [hs1, hs2, integral_mul_const] at h
  have hb := positive_bank_integrated_probability μ weights hw hu
  have hr := mul_le_mul_of_nonneg_right hq hε
  change (∫ d, q.val d ∂μ)*ε ≤ ρ*ε at hr
  exact h.trans (add_le_add (add_le_add hr hb) le_rfl)

end ThresholdHC.EntropyTailUpper
