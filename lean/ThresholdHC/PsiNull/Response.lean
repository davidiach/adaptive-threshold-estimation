import ThresholdHC.PsiNull.StoppedKL
import ThresholdHC.PsiNull.OneSided
import ThresholdHC.CriticalEntropy.Activation
import ThresholdHC.CriticalEntropy.FiniteAffinity
import ThresholdHC.CriticalEntropy.UniformCoin
import ThresholdHC.ObservableSimulation.OriginalExperiment

/-! Per-gap response bounds for seeded capped procedures with bounded output.

`activation_response` compares the conditional means of a bounded output under
two arbitrary coin parameters. Seeds that never observe a flip contribute the
same amount under both parameters, so only the active seeds matter.
Cauchy–Schwarz bounds the square of each active part by the activation
probability times a second moment, so the squared difference of the means is
at most twice the activation probability times the two second moments.

`gap_response_bound` is the per-gap response cost (paper,
eq:conditional-response-cost): the squared mean response between the two signs
of a gap `d` is at most `64 d²` times the expected work under the negative sign
times the sum of the two conditional second moments. For `d ≤ 1/4` it uses the
stopped KL chain rule and the one-sided information/mean inequality; for
`d > 1/4` (including `d = 1/2`) it uses `activation_response`. -/
noncomputable section
namespace ThresholdHC.PsiNull
open MeasureTheory InformationTheory Set
open scoped ENNReal
open ThresholdHC.CriticalEntropy
open ThresholdHC.ObservableSimulation (gapParameter)
open ThresholdHC.Tier6 (Gap)

/-- A bounded output is integrable under every coin parameter. -/
theorem output_integrable_of_bound {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R ℝ)
    {C : ℝ} (hC : ∀ z, |A.output z| ≤ C) (p : unitInterval) :
    Integrable A.output (ν.prod (Tier2.tapeMeasure p)) :=
  Integrable.of_bound A.measurable_output.aestronglyMeasurable C
    (ae_of_all _ (fun z => by rw [Real.norm_eq_abs]; exact hC z))

/-- A bounded output is square integrable under every coin parameter. -/
theorem output_memLp_two_of_bound {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R ℝ)
    {C : ℝ} (hC : ∀ z, |A.output z| ≤ C) (p : unitInterval) :
    MemLp A.output 2 (ν.prod (Tier2.tapeMeasure p)) :=
  MemLp.of_bound A.measurable_output.aestronglyMeasurable C
    (ae_of_all _ (fun z => by rw [Real.norm_eq_abs]; exact hC z))

/-- A bounded output has a finite conditional second moment. -/
theorem conditionalSecondMoment_ne_top_of_bound {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R ℝ)
    {C : ℝ} (hC : ∀ z, |A.output z| ≤ C) (p : unitInterval) :
    conditionalSecondMoment ν p A ≠ ∞ := by
  refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := C^2)) ?_
  unfold conditionalSecondMoment
  calc
    _ ≤ ∫⁻ _z, ENNReal.ofReal (C^2) ∂ν.prod (Tier2.tapeMeasure p) := by
      apply lintegral_mono
      intro z
      apply ENNReal.ofReal_le_ofReal
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hC z) 2
    _ = _ := by simp

/-- The real conditional second moment is the Bochner integral of the square. -/
theorem conditionalSecondMoment_toReal_eq {R : Type} [MeasurableSpace R]
    (ν : Measure R) (A : StoppedProcedure R ℝ) (p : unitInterval) :
    (conditionalSecondMoment ν p A).toReal =
      ∫ z, (A.output z)^2 ∂ν.prod (Tier2.tapeMeasure p) := by
  unfold conditionalSecondMoment
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun z => sq_nonneg (A.output z)))
    (A.measurable_output.pow_const 2).aestronglyMeasurable]

/-- The conditional expected work of a capped procedure is at most the cap. -/
theorem expectedStoppedProcedureWork_le_cap {R E : Type} [MeasurableSpace R]
    [MeasurableSpace E] (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R E)
    (m : ℕ) (hcap : ∀ z, A.stop z ≤ m) (p : unitInterval) :
    expectedStoppedProcedureWork ν p A ≤ m := by
  unfold expectedStoppedProcedureWork
  calc
    _ ≤ ∫⁻ _z, (m : ℝ≥0∞) ∂ν.prod (Tier2.tapeMeasure p) := by
      apply lintegral_mono
      intro z
      change (A.stop z).toENNReal ≤ (m : ℝ≥0∞)
      simpa using ENat.toENNReal_mono (hcap z)
    _ = _ := by simp

/-- Split of a conditional mean into the active seeds and a parameter-free part
from the inactive seeds, which never look at the tape. -/
theorem conditionalMean_active_split {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R ℝ) (p : unitInterval)
    (hint : Integrable A.output (ν.prod (Tier2.tapeMeasure p))) :
    conditionalMean ν p A =
      (∫ z in activeSeeds A ×ˢ (univ : Set (ℕ → Bool)), A.output z
        ∂ν.prod (Tier2.tapeMeasure p)) +
        ∫ r in (activeSeeds A)ᶜ, A.output (r, fun _ => false) ∂ν := by
  have hT : MeasurableSet (activeSeeds A ×ˢ (univ : Set (ℕ → Bool))) :=
    (measurableSet_activeSeeds A).prod MeasurableSet.univ
  unfold conditionalMean
  rw [← integral_add_compl hT hint]
  congr 1
  have he : (activeSeeds A ×ˢ (univ : Set (ℕ → Bool)))ᶜ = (activeSeeds A)ᶜ ×ˢ univ := by
    ext z
    simp
  calc
    _ = ∫ z in (activeSeeds A ×ˢ (univ : Set (ℕ → Bool)))ᶜ, A.output (z.1, fun _ => false)
        ∂ν.prod (Tier2.tapeMeasure p) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hT.compl] with z hz
      have hz' : z.1 ∉ activeSeeds A := fun h => hz ⟨h, mem_univ _⟩
      exact inactive_output A z.1 z.2 hz'
    _ = _ := by
      rw [he, ← Measure.prod_restrict, Measure.restrict_univ,
        integral_fun_fst (fun r : R => A.output (r, fun _ => false))]
      simp

/-- Cauchy–Schwarz on the active seeds: the squared active part of the mean is
at most the activation probability times the raw second moment. -/
theorem active_part_sq_le {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R ℝ) (p : unitInterval)
    (hm : MemLp A.output 2 (ν.prod (Tier2.tapeMeasure p))) :
    (∫ z in activeSeeds A ×ˢ (univ : Set (ℕ → Bool)), A.output z
        ∂ν.prod (Tier2.tapeMeasure p))^2 ≤
      ν.real (activeSeeds A) * ∫ z, (A.output z)^2 ∂ν.prod (Tier2.tapeMeasure p) := by
  set T := activeSeeds A ×ˢ (univ : Set (ℕ → Bool)) with hTdef
  have hT : MeasurableSet T := (measurableSet_activeSeeds A).prod MeasurableSet.univ
  have hf : MemLp (T.indicator (fun _ => (1 : ℝ))) 2 (ν.prod (Tier2.tapeMeasure p)) :=
    (memLp_const (1 : ℝ)).indicator hT.nullMeasurableSet
  have h := ThresholdHC.UnbiasedConverse.integral_mul_sq_le (ν.prod (Tier2.tapeMeasure p)) hf hm
  have h1 : (fun z => T.indicator (fun _ => (1 : ℝ)) z * A.output z) = T.indicator A.output := by
    funext z
    by_cases hz : z ∈ T <;> simp [hz]
  have h2 : (fun z => T.indicator (fun _ => (1 : ℝ)) z ^ 2) =
      T.indicator (fun _ => (1 : ℝ)) := by
    funext z
    by_cases hz : z ∈ T <;> simp [hz]
  have h3 : (ν.prod (Tier2.tapeMeasure p)).real T = ν.real (activeSeeds A) := by
    rw [hTdef, measureReal_def, measureReal_def, Measure.prod_prod, measure_univ, mul_one]
  rw [h1, h2, integral_indicator_const _ hT, h3, integral_indicator hT, smul_eq_mul,
    mul_one] at h
  exact h

/-- Activation response: for a bounded output and any two coin parameters,
the squared difference of conditional means is at most twice the activation
probability times the sum of the two conditional second moments. -/
theorem activation_response {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R ℝ)
    (C : ℝ) (hC : ∀ z, |A.output z| ≤ C) (p q : unitInterval) :
    (conditionalMean ν q A - conditionalMean ν p A)^2 ≤
      2 * ν.real (activeSeeds A) *
        ((conditionalSecondMoment ν p A).toReal + (conditionalSecondMoment ν q A).toReal) := by
  rw [conditionalMean_active_split ν A q (output_integrable_of_bound ν A hC q),
    conditionalMean_active_split ν A p (output_integrable_of_bound ν A hC p),
    conditionalSecondMoment_toReal_eq, conditionalSecondMoment_toReal_eq]
  have ha := active_part_sq_le ν A q (output_memLp_two_of_bound ν A hC q)
  have hb := active_part_sq_le ν A p (output_memLp_two_of_bound ν A hC p)
  set a := ∫ z in activeSeeds A ×ˢ (univ : Set (ℕ → Bool)), A.output z
    ∂ν.prod (Tier2.tapeMeasure q)
  set b := ∫ z in activeSeeds A ×ˢ (univ : Set (ℕ → Bool)), A.output z
    ∂ν.prod (Tier2.tapeMeasure p)
  nlinarith [sq_nonneg (a + b)]

/-- The negative-sign coin parameter of a gap `d` is `1/2 - d`. -/
theorem negGapParameter_coe (d : Gap) :
    ((gapParameter false d : unitInterval) : ℝ) = 1/2 - d := by
  simp only [gapParameter, Bool.false_eq_true, ite_false]
  ring

/-- The positive-sign coin parameter of a gap `d` is `1/2 + d`. -/
theorem posGapParameter_coe (d : Gap) :
    ((gapParameter true d : unitInterval) : ℝ) = 1/2 + d := by
  simp only [gapParameter, ite_true]

/-- Per-gap response cost (paper, eq:conditional-response-cost): for a
capped procedure with bounded output and any gap `d`, the squared response of
the conditional mean between the two signs is at most `64 d²` times the
expected work under the negative sign times the sum of the two conditional
second moments. -/
theorem gap_response_bound {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R ℝ) (m : ℕ)
    (hcap : ∀ z, A.stop z ≤ m) (C : ℝ) (hC : ∀ z, |A.output z| ≤ C) (d : Gap) :
    (conditionalMean ν (gapParameter true d) A -
        conditionalMean ν (gapParameter false d) A)^2 ≤
      64 * (d : ℝ)^2 * (expectedStoppedProcedureWork ν (gapParameter false d) A).toReal *
        ((conditionalSecondMoment ν (gapParameter false d) A).toReal +
          (conditionalSecondMoment ν (gapParameter true d) A).toReal) := by
  set pm := gapParameter false d with hpm
  set pp := gapParameter true d with hpp
  have hd0 : 0 < (d : ℝ) := d.property.1
  have hd1 : (d : ℝ) ≤ 1/2 := d.property.2
  have hwfin : expectedStoppedProcedureWork ν pm A ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.natCast_ne_top m)
      (expectedStoppedProcedureWork_le_cap ν A m hcap pm)
  set w := (expectedStoppedProcedureWork ν pm A).toReal with hw
  have hw0 : 0 ≤ w := ENNReal.toReal_nonneg
  set M := (conditionalSecondMoment ν pm A).toReal + (conditionalSecondMoment ν pp A).toReal
    with hM
  have hM0 : 0 ≤ M := add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  by_cases hd : (d : ℝ) ≤ 1/4
  · -- KL route.
    have hpmv : (pm : ℝ) = 1/2 - d := negGapParameter_coe d
    have hppv : (pp : ℝ) = 1/2 + d := posGapParameter_coe d
    have hp0 : 0 < (pm : ℝ) := by rw [hpmv]; linarith
    have hp1 : (pm : ℝ) < 1 := by rw [hpmv]; linarith
    have hq0 : 0 < (pp : ℝ) := by rw [hppv]; linarith
    have hq1 : (pp : ℝ) < 1 := by rw [hppv]; linarith
    have hklB : klB pm pp ≤ 64 * (d : ℝ)^2 / 3 := by
      refine (binary_kl_le_chisq pm pp hp0 hp1 hq0 hq1).trans ?_
      rw [hpmv, hppv]
      have hden : 0 < (1/2 + (d : ℝ)) * (1 - (1/2 + d)) := by nlinarith
      rw [div_le_div_iff₀ hden (by norm_num)]
      nlinarith [mul_nonneg (mul_nonneg hd0.le hd0.le)
        (mul_nonneg (sub_nonneg.2 hd) (by linarith : (0 : ℝ) ≤ 1/4 + d))]
    let Tm := ν.prod (Tier2.tapeMeasure pm)
    let Tp := ν.prod (Tier2.tapeMeasure pp)
    have hdata : klDiv (Tm.map A.output) (Tp.map A.output) ≤
        klDiv (Tm.map (cappedTranscript A m)) (Tp.map (cappedTranscript A m)) := by
      rw [← cappedOutput_map A m hcap Tm, ← cappedOutput_map A m hcap Tp]
      exact klDiv_map_le _ _ (measurable_cappedOutput A m)
    have hchain := capped_transcript_kl ν A m hcap pm pp hp0 hp1 hq0 hq1
    have hKLle : klDiv (Tm.map A.output) (Tp.map A.output) ≤
        ENNReal.ofReal (w * (64 * (d : ℝ)^2 / 3)) := by
      refine (hdata.trans_eq hchain).trans (ENNReal.ofReal_le_ofReal ?_)
      exact mul_le_mul_of_nonneg_left hklB hw0
    have hne : klDiv (Tm.map A.output) (Tp.map A.output) ≠ ∞ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hKLle
    have hK : (klDiv (Tm.map A.output) (Tp.map A.output)).toReal ≤
        w * (64 * (d : ℝ)^2 / 3) :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) hKLle
    have hfinm := conditionalSecondMoment_ne_top_of_bound ν A hC pm
    have hfinp := conditionalSecondMoment_ne_top_of_bound ν A hC pp
    have hmemm : MemLp (fun x : ℝ => x) 2 (Tm.map A.output) :=
      (conditionalSecondMoment_finite_iff ν pm A).mp hfinm
    have hmemp : MemLp (fun x : ℝ => x) 2 (Tp.map A.output) :=
      (conditionalSecondMoment_finite_iff ν pp A).mp hfinp
    have h := kl_mean_one_sided (Tm.map A.output) (Tp.map A.output) hmemm hmemp hne
    rw [conditionalMean_output_law, conditionalMean_output_law,
      conditionalSecondMoment_output_law ν pm A hfinm,
      conditionalSecondMoment_output_law ν pp A hfinp] at h
    have hK0 : 0 ≤ (klDiv (Tm.map A.output) (Tp.map A.output)).toReal := ENNReal.toReal_nonneg
    have hsq : (conditionalMean ν pp A - conditionalMean ν pm A)^2 =
        (conditionalMean ν pm A - conditionalMean ν pp A)^2 := by ring
    rw [hsq]
    calc
      _ ≤ 2 * (klDiv (Tm.map A.output) (Tp.map A.output)).toReal * M := h
      _ ≤ 2 * (w * (64 * (d : ℝ)^2 / 3)) * M := by gcongr
      _ ≤ 64 * (d : ℝ)^2 * w * M := by
        have hdw : 0 ≤ (d : ℝ)^2 * w * M := by positivity
        nlinarith
  · -- Activation route: `d > 1/4`, which includes `d = 1/2`.
    have hd' : 1/4 < (d : ℝ) := lt_of_not_ge hd
    have h5 := activation_response ν A C hC pm pp
    have hS : ν.real (activeSeeds A) ≤ w := by
      rw [measureReal_def]
      exact ENNReal.toReal_mono hwfin (activation_probability_le_work ν pm A)
    have h64 : 2 ≤ 64 * (d : ℝ)^2 := by nlinarith
    calc
      _ ≤ 2 * ν.real (activeSeeds A) * M := h5
      _ ≤ 2 * w * M := by gcongr
      _ ≤ 64 * (d : ℝ)^2 * w * M := by
        have := mul_le_mul_of_nonneg_right h64 (mul_nonneg hw0 hM0)
        nlinarith

end ThresholdHC.PsiNull
