import ThresholdHC.CriticalEntropy.FiniteSufficiency
import ThresholdHC.CriticalEntropy.LikelihoodBounds
import ThresholdHC.CriticalEntropy.Hellinger

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace ThresholdHC.CriticalEntropy

theorem cappedStatisticLaw_probability {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (hq : Measurable q) (A : StoppedProcedure R E) (m : ℕ) :
    IsProbabilityMeasure (cappedStatisticLaw μ ν p₀ p₁ q A m) := by
  let : IsProbabilityMeasure (cappedTranscriptLaw μ ν p₀ p₁ q A m) :=
    cappedTranscriptLaw_probability μ ν p₀ p₁ q h₀ h₁ hq A m
  have hT : Measurable (fun z : R × CappedWord m => stoppedStatistic m z.2) :=
    (measurable_of_countable (stoppedStatistic m)).comp measurable_snd
  constructor
  rw [cappedStatisticLaw,Measure.map_apply hT MeasurableSet.univ]
  simp

theorem cappedStatisticLaw_zero_iff_reference {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (hq : Measurable q) (A : StoppedProcedure R E) (m : ℕ)
    (hcap : ∀ z, A.stop z ≤ m)
    (hp : ∀ᵐ d ∂μ, 0 < (p₀ d : ℝ) ∧ (p₀ d : ℝ) < 1 ∧
      0 < (p₁ d : ℝ) ∧ (p₁ d : ℝ) < 1) (i : Fin (m+1) × Fin (m+1)) :
    cappedStatisticLaw μ ν p₀ p₁ q A m {i} = 0 ↔
      ((stoppedReference ν A m).map (fun z => stoppedStatistic m z.2)) {i} = 0 := by
  rw [cappedStatisticLaw_density μ ν p₀ p₁ q h₀ h₁ hq A m hcap,
    withDensity_apply _ (measurableSet_singleton i),lintegral_singleton,mul_eq_zero]
  simp [ne_of_gt (populationWordLikelihood_pos μ p₀ p₁ q h₀ h₁ hq hp i.1.val i.2.val)]

theorem hellingerAffinity_factored_statistic {Ω I : Type}
    [MeasurableSpace Ω] [MeasurableSpace I]
    (ξ : Measure Ω) [IsFiniteMeasure ξ] (T : Ω → I) (hT : Measurable T)
    (f g : I → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g)
    (hf_top : ∀ i, f i ≠ ∞) (hg_top : ∀ i, g i ≠ ∞)
    (hs₀ : ∀ i, f i+g i ≠ 0) :
    hellingerAffinity (ξ.withDensity (f ∘ T)) (ξ.withDensity (g ∘ T)) =
      hellingerAffinity ((ξ.withDensity (f ∘ T)).map T) ((ξ.withDensity (g ∘ T)).map T) := by
  rw [map_factored_density ξ T hT f hf,map_factored_density ξ T hT g hg,
    hellingerAffinity_withDensity ξ (f ∘ T) (g ∘ T) (hf.comp hT) (hg.comp hT)
      (fun x => hf_top (T x)) (fun x => hg_top (T x)) (fun x => hs₀ (T x)),
    hellingerAffinity_withDensity (ξ.map T) f g hf hg hf_top hg_top hs₀,
    lintegral_map (by fun_prop) hT]
  rfl

theorem capped_observation_reconstruction {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (hq : Measurable q) (A : StoppedProcedure R E) (m : ℕ)
    (hcap : ∀ z, A.stop z ≤ m)
    (hp : ∀ᵐ d ∂μ, 0 < (p₀ d : ℝ) ∧ (p₀ d : ℝ) < 1 ∧
      0 < (p₁ d : ℝ) ∧ (p₁ d : ℝ) < 1) :
    cappedTranscriptLaw μ ν p₀ p₁ q A m =
      ∑ i, cappedStatisticLaw μ ν p₀ p₁ q A m {i} • transcriptReconstruction ν A m i := by
  let P := cappedTranscriptLaw μ ν p₀ p₁ q A m
  let ξ := stoppedReference ν A m
  let T : R × CappedWord m → Fin (m+1) × Fin (m+1) := fun z => stoppedStatistic m z.2
  let g : Fin (m+1) × Fin (m+1) → ℝ≥0∞ :=
    fun i => populationWordLikelihood μ p₀ p₁ q i.1.val i.2.val
  have hT : Measurable T := (measurable_of_countable (stoppedStatistic m)).comp measurable_snd
  have hP : P = ξ.withDensity (g ∘ T) :=
    cappedTranscriptLaw_density μ ν p₀ p₁ q h₀ h₁ hq A m hcap
  let : IsProbabilityMeasure P := cappedTranscriptLaw_probability μ ν p₀ p₁ q h₀ h₁ hq A m
  have hc (i : Fin (m+1) × Fin (m+1)) : cond P (T ⁻¹' {i}) = transcriptReconstruction ν A m i := by
    rw [hP]
    exact factored_density_cond ξ T hT g i
      (ne_of_gt (populationWordLikelihood_pos μ p₀ p₁ q h₀ h₁ hq hp _ _))
      (ne_top_of_le_ne_top (by norm_num) (populationWordLikelihood_le_one μ p₀ p₁ q _ _))
  have ht := sum_meas_smul_cond_fiber hT P
  calc
    P = ∑ i, P (T ⁻¹' {i}) • cond P (T ⁻¹' {i}) := ht.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hc]
      congr 1
      exact (Measure.map_apply hT (measurableSet_singleton i)).symm

theorem capped_observation_affinity {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q r : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (hq : Measurable q) (hr : Measurable r) (A : StoppedProcedure R E) (m : ℕ)
    (hcap : ∀ z, A.stop z ≤ m)
    (hp : ∀ᵐ d ∂μ, 0 < (p₀ d : ℝ) ∧ (p₀ d : ℝ) < 1 ∧
      0 < (p₁ d : ℝ) ∧ (p₁ d : ℝ) < 1) :
    hellingerAffinity (cappedTranscriptLaw μ ν p₀ p₁ q A m) (cappedTranscriptLaw μ ν p₀ p₁ r A m) =
      hellingerAffinity (cappedStatisticLaw μ ν p₀ p₁ q A m) (cappedStatisticLaw μ ν p₀ p₁ r A m) := by
  let ξ := stoppedReference ν A m
  let T : R × CappedWord m → Fin (m+1) × Fin (m+1) := fun z => stoppedStatistic m z.2
  let f : Fin (m+1) × Fin (m+1) → ℝ≥0∞ :=
    fun i => populationWordLikelihood μ p₀ p₁ q i.1.val i.2.val
  let g : Fin (m+1) × Fin (m+1) → ℝ≥0∞ :=
    fun i => populationWordLikelihood μ p₀ p₁ r i.1.val i.2.val
  have hf : cappedTranscriptLaw μ ν p₀ p₁ q A m = ξ.withDensity (f ∘ T) :=
    cappedTranscriptLaw_density μ ν p₀ p₁ q h₀ h₁ hq A m hcap
  have hg : cappedTranscriptLaw μ ν p₀ p₁ r A m = ξ.withDensity (g ∘ T) :=
    cappedTranscriptLaw_density μ ν p₀ p₁ r h₀ h₁ hr A m hcap
  rw [cappedStatisticLaw,cappedStatisticLaw,hf,hg]
  apply hellingerAffinity_factored_statistic ξ T
    ((measurable_of_countable (stoppedStatistic m)).comp measurable_snd) f g
    (measurable_of_countable f) (measurable_of_countable g)
  · intro i
    exact ne_top_of_le_ne_top (by norm_num) (populationWordLikelihood_le_one μ p₀ p₁ q _ _)
  · intro i
    exact ne_top_of_le_ne_top (by norm_num) (populationWordLikelihood_le_one μ p₀ p₁ r _ _)
  · intro i
    exact ne_of_gt (lt_of_lt_of_le (populationWordLikelihood_pos μ p₀ p₁ q h₀ h₁ hq hp _ _)
      (le_add_right le_rfl))

theorem capped_observation_finite_affinity {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q r : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (hq : Measurable q) (hr : Measurable r) (A : StoppedProcedure R E) (m : ℕ)
    (hcap : ∀ z, A.stop z ≤ m)
    (hp : ∀ᵐ d ∂μ, 0 < (p₀ d : ℝ) ∧ (p₀ d : ℝ) < 1 ∧
      0 < (p₁ d : ℝ) ∧ (p₁ d : ℝ) < 1) :
    hellingerAffinity (cappedTranscriptLaw μ ν p₀ p₁ q A m) (cappedTranscriptLaw μ ν p₀ p₁ r A m) =
      finiteAffinity (fun i => cappedStatisticLaw μ ν p₀ p₁ q A m {i})
        (fun i => cappedStatisticLaw μ ν p₀ p₁ r A m {i}) := by
  rw [capped_observation_affinity μ ν p₀ p₁ q r h₀ h₁ hq hr A m hcap hp,
    cappedStatisticLaw_density μ ν p₀ p₁ q h₀ h₁ hq A m hcap,
    cappedStatisticLaw_density μ ν p₀ p₁ r h₀ h₁ hr A m hcap]
  apply hellingerAffinity_finite_density
  · intro i
    exact ne_top_of_le_ne_top (by norm_num) (populationWordLikelihood_le_one μ p₀ p₁ q _ _)
  · intro i
    exact ne_top_of_le_ne_top (by norm_num) (populationWordLikelihood_le_one μ p₀ p₁ r _ _)
  · intro i
    exact ne_of_gt (lt_of_lt_of_le (populationWordLikelihood_pos μ p₀ p₁ q h₀ h₁ hq hp _ _)
      (le_add_right le_rfl))

theorem capped_transcript_work {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (A : StoppedProcedure R E) (m : ℕ) (z : R × (ℕ → Bool)) (hcap : A.stop z ≤ m) :
    stoppedProcedureWork A z = ((stoppedStatistic m (cappedTranscript A m z).2).1.val : ℝ≥0∞) := by
  have hfin : A.stop z ≠ ⊤ := ne_top_of_le_ne_top (by simp) hcap
  have hlen : (A.stop z).toNat ≤ m := by simpa using ENat.toNat_le_toNat hcap (by simp)
  have hn : A.stop z = (A.stop z).toNat := (ENat.natCast_toNat hfin).symm
  rw [cappedTranscript_of_stop A m (A.stop z).toNat hlen z hn]
  change (A.stop z : ℝ≥0∞) = ((A.stop z).toNat : ℝ≥0∞)
  conv_lhs => rw [hn]
  simp

theorem capped_observation_work {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (hq : Measurable q) (A : StoppedProcedure R E) (m : ℕ)
    (hcap : ∀ z, A.stop z ≤ m) :
    populationExpectedWork μ ν p₀ p₁ q A =
      ∑ i : Fin (m+1) × Fin (m+1), (i.1.val : ℝ≥0∞)*cappedStatisticLaw μ ν p₀ p₁ q A m {i} := by
  let T : R × CappedWord m → Fin (m+1) × Fin (m+1) := fun z => stoppedStatistic m z.2
  have hT : Measurable T := (measurable_of_countable (stoppedStatistic m)).comp measurable_snd
  have htime : Measurable (fun i : Fin (m+1) × Fin (m+1) => (i.1.val : ℝ≥0∞)) :=
    measurable_of_countable _
  calc
    _ = ∫⁻ i, (i.1.val : ℝ≥0∞) ∂cappedStatisticLaw μ ν p₀ p₁ q A m := by
      rw [cappedStatisticLaw,lintegral_map htime hT,cappedTranscriptLaw]
      have htimeT : Measurable (fun z : R × CappedWord m => (T z).1.val :
          R × CappedWord m → ℝ≥0∞) := htime.comp hT
      rw [lintegral_map htimeT ((measurable_cappedTranscript A m).comp
        (measurable_populationInput p₀ p₁ q h₀ h₁ hq))]
      exact lintegral_congr (fun z => capped_transcript_work A m _ (hcap _))
    _ = _ := lintegral_fintype _

/-- Population-independent reconstruction for the fixed quadratic experiment. -/
theorem critical_observation_reconstruction {R E : Type}
    [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsProbabilityMeasure ν] (q : ℝ → unitInterval) (hq : Measurable q)
    (A : StoppedProcedure R E) (m : ℕ) (hcap : ∀ z, A.stop z ≤ m) :
    cappedTranscriptLaw criticalGapLaw ν
      (fun d => criticalParameter d false) (fun d => criticalParameter d true) q A m =
      ∑ i, cappedStatisticLaw criticalGapLaw ν
        (fun d => criticalParameter d false) (fun d => criticalParameter d true) q A m {i} •
          transcriptReconstruction ν A m i :=
  capped_observation_reconstruction criticalGapLaw ν _ _ q
    (measurable_criticalParameter false) (measurable_criticalParameter true) hq A m hcap
    critical_parameters_interior

/-- Canonical full-transcript affinity is exactly the finite categorical affinity. -/
theorem critical_observation_finite_affinity {R E : Type}
    [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsProbabilityMeasure ν] (q r : ℝ → unitInterval)
    (hq : Measurable q) (hr : Measurable r)
    (A : StoppedProcedure R E) (m : ℕ) (hcap : ∀ z, A.stop z ≤ m) :
    hellingerAffinity
      (cappedTranscriptLaw criticalGapLaw ν
        (fun d => criticalParameter d false) (fun d => criticalParameter d true) q A m)
      (cappedTranscriptLaw criticalGapLaw ν
        (fun d => criticalParameter d false) (fun d => criticalParameter d true) r A m) =
      finiteAffinity
        (fun i => cappedStatisticLaw criticalGapLaw ν
          (fun d => criticalParameter d false) (fun d => criticalParameter d true) q A m {i})
        (fun i => cappedStatisticLaw criticalGapLaw ν
          (fun d => criticalParameter d false) (fun d => criticalParameter d true) r A m {i}) :=
  capped_observation_finite_affinity criticalGapLaw ν _ _ q r
    (measurable_criticalParameter false) (measurable_criticalParameter true) hq hr A m hcap
    critical_parameters_interior

/-- The finite reduction retains the actual expected number of flips. -/
theorem critical_observation_work {R E : Type}
    [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsProbabilityMeasure ν] (q : ℝ → unitInterval) (hq : Measurable q)
    (A : StoppedProcedure R E) (m : ℕ) (hcap : ∀ z, A.stop z ≤ m) :
    populationExpectedWork criticalGapLaw ν
      (fun d => criticalParameter d false) (fun d => criticalParameter d true) q A =
      ∑ i : Fin (m+1) × Fin (m+1), (i.1.val : ℝ≥0∞)*cappedStatisticLaw criticalGapLaw ν
        (fun d => criticalParameter d false) (fun d => criticalParameter d true) q A m {i} :=
  capped_observation_work criticalGapLaw ν _ _ q
    (measurable_criticalParameter false) (measurable_criticalParameter true) hq A m hcap

end ThresholdHC.CriticalEntropy
