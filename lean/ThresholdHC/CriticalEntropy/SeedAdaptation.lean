import ThresholdHC.CriticalEntropy.CapInvariance

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace ThresholdHC.CriticalEntropy

theorem reseed_statistic_law {D R S E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace S] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure S) [IsProbabilityMeasure ν]
    (p₀ p₁ q : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q)
    (A : StoppedProcedure R E) (m : ℕ) (f : S → R) (hf : Measurable f) :
    cappedStatisticLaw μ ν p₀ p₁ q (reseedProcedure A f hf) m =
      cappedStatisticLaw μ (ν.map f) p₀ p₁ q A m := by
  classical
  apply Measure.ext_of_singleton
  intro j
  have h := reseed_statistic_lintegral μ ν p₀ p₁ q h₀ h₁ hq A m f hf
    (({j} : Set (Fin (m+1) × Fin (m+1))).indicator (fun _ => 1))
  simpa only [lintegral_indicator_fun_one (measurableSet_singleton j)] using h

/-- Adding independent seed coordinates does not alter the canonical affinity,
even though the full observation contains those coordinates. -/
theorem reseed_affinity_real {D R S E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace S] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure S) [IsProbabilityMeasure ν]
    (p₀ p₁ q r : D → unitInterval)
    (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q) (hr : Measurable r)
    (A : StoppedProcedure R E) (m : ℕ) (hcap : ∀ z, A.stop z ≤ m)
    (f : S → R) (hf : Measurable f)
    (hp : ∀ᵐ d ∂μ, 0 < (p₀ d : ℝ) ∧ (p₀ d : ℝ) < 1 ∧
      0 < (p₁ d : ℝ) ∧ (p₁ d : ℝ) < 1) :
    (hellingerAffinity (cappedTranscriptLaw μ ν p₀ p₁ q (reseedProcedure A f hf) m)
      (cappedTranscriptLaw μ ν p₀ p₁ r (reseedProcedure A f hf) m)).toReal =
    (hellingerAffinity (cappedTranscriptLaw μ (ν.map f) p₀ p₁ q A m)
      (cappedTranscriptLaw μ (ν.map f) p₀ p₁ r A m)).toReal := by
  let : IsProbabilityMeasure (ν.map f) := (Measure.isProbabilityMeasure_map_iff hf.aemeasurable).2 inferInstance
  rw [capped_observation_affinity_real μ ν p₀ p₁ q r h₀ h₁ hq hr
    (reseedProcedure A f hf) m (fun z => hcap (f z.1,z.2)) hp,
    capped_observation_affinity_real μ (ν.map f) p₀ p₁ q r h₀ h₁ hq hr A m hcap hp,
    reseed_statistic_law μ ν p₀ p₁ q h₀ h₁ hq A m f hf,
    reseed_statistic_law μ ν p₀ p₁ r h₀ h₁ hr A m f hf]

/-- The probability law realizing a finite vector of nonnegative mixture weights. -/
def finiteWeightMeasure {I : Type} [Fintype I] [MeasurableSpace I] (w : I → ℝ) : Measure I :=
  ∑ i, ENNReal.ofReal (w i) • Measure.dirac i

theorem finiteWeightMeasure_singleton {I : Type} [Fintype I]
    [MeasurableSpace I] [MeasurableSingletonClass I] (w : I → ℝ) (i : I) :
    finiteWeightMeasure w {i} = ENNReal.ofReal (w i) := by
  classical
  simp [finiteWeightMeasure,Measure.dirac_apply',Pi.single_apply]

theorem finiteWeightMeasure_probability {I : Type} [Fintype I]
    [MeasurableSpace I] [MeasurableSingletonClass I]
    (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : (∑ i, w i) = 1) :
    IsProbabilityMeasure (finiteWeightMeasure w) := by
  constructor
  have h := sum_measure_singleton (μ := finiteWeightMeasure w) (s := Finset.univ)
  simp only [Finset.coe_univ] at h
  rw [← h]
  simp only [finiteWeightMeasure_singleton]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i hi => hw i),hs]
  norm_num

theorem finiteWeightMeasure_real_singleton {I : Type} [Fintype I]
    [MeasurableSpace I] [MeasurableSingletonClass I]
    (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (i : I) :
    (finiteWeightMeasure w).real {i} = w i := by
  rw [measureReal_def,finiteWeightMeasure_singleton,ENNReal.toReal_ofReal (hw i)]

theorem selected_population_work_real {D I R E : Type} [Fintype I]
    [MeasurableSpace D] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (κ : Measure I) [IsProbabilityMeasure κ]
    (ν : Measure R) [IsProbabilityMeasure ν] (p₀ p₁ q : D → unitInterval)
    (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q)
    (A : I → StoppedProcedure R E) (m : ℕ) (hcap : ∀ i z, (A i).stop z ≤ m) :
    (populationExpectedWork μ (κ.prod ν) p₀ p₁ q (selectedProcedure A)).toReal =
      ∑ i, κ.real {i}*(populationExpectedWork μ ν p₀ p₁ q (A i)).toReal := by
  have hfin (i : I) : populationExpectedWork μ ν p₀ p₁ q (A i) ≠ ∞ :=
    ne_top_of_le_ne_top (by simp) (population_capped_work_le μ ν p₀ p₁ q (A i) m (hcap i))
  rw [selected_population_work μ κ ν p₀ p₁ q h₀ h₁ hq A,
    ENNReal.toReal_sum (fun i hi => ENNReal.mul_ne_top (measure_ne_top _ _) (hfin i))]
  simp only [ENNReal.toReal_mul,measureReal_def]

end ThresholdHC.CriticalEntropy
