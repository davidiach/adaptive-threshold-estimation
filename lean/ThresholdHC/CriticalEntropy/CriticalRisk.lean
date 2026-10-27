import ThresholdHC.CriticalEntropy.ObservationRisk
import ThresholdHC.CriticalEntropy.BaseCost

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace ThresholdHC.CriticalEntropy

/-- A single observable estimator realizing the critical capped affinity
comparison, with genuine square integrability and unchanged actual work. -/
theorem critical_capped_estimator {R E : Type} [MeasurableSpace R] [MeasurableSpace E]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R E)
    (m : ℕ) (hcap : ∀ z, A.stop z ≤ m) (ρ ε : ℝ) (hρ : 0 ≤ ρ) (hε : 0 ≤ ε) (n : ℕ)
    (hsep : ∀ q r : ℝ → unitInterval, CappedPrior criticalGapLaw ρ q → CappedPrior criticalGapLaw ρ r →
      1/2 ≤ ((hellingerAffinity
        (cappedTranscriptLaw criticalGapLaw ν
          (fun d => criticalParameter d false) (fun d => criticalParameter d true) q A m)
        (cappedTranscriptLaw criticalGapLaw ν
          (fun d => criticalParameter d false) (fun d => criticalParameter d true) r A m)).toReal)^n →
      (∫ d, (q d : ℝ) ∂criticalGapLaw)-(∫ d, (r d : ℝ) ∂criticalGapLaw) < 2*ε) :
    ∃ Z : StoppedProcedure R ℝ, Z.stop = A.stop ∧
      ∀ q : ℝ → unitInterval, CappedPrior criticalGapLaw ρ q →
      MemLp (Z.output ∘ populationInput
        (fun d => criticalParameter d false) (fun d => criticalParameter d true) q) 2
        (populationMeasure criticalGapLaw ν) ∧
      |populationMean criticalGapLaw ν
        (fun d => criticalParameter d false) (fun d => criticalParameter d true) q Z-
        (∫ d, (q d : ℝ) ∂criticalGapLaw)| ≤ 3*ε ∧
      evariance (Z.output ∘ populationInput
        (fun d => criticalParameter d false) (fun d => criticalParameter d true) q)
        (populationMeasure criticalGapLaw ν) ≤ ENNReal.ofReal ((n : ℝ)*(9*ε^2)) ∧
      populationExpectedWork criticalGapLaw ν
        (fun d => criticalParameter d false) (fun d => criticalParameter d true) q Z =
      populationExpectedWork criticalGapLaw ν
        (fun d => criticalParameter d false) (fun d => criticalParameter d true) q A := by
  obtain ⟨f,hf⟩ := capped_observation_one_run criticalGapLaw ν
    (fun d => criticalParameter d false) (fun d => criticalParameter d true)
    (measurable_criticalParameter false) (measurable_criticalParameter true)
    A m hcap ρ ε hρ hε n critical_parameters_interior hsep
  refine ⟨cappedStatisticProcedure A m hcap f,rfl,?_⟩
  intro q hq
  exact ⟨cappedStatisticProcedure_memLp criticalGapLaw ν
    (fun d => criticalParameter d false) (fun d => criticalParameter d true) q
    (measurable_criticalParameter false) (measurable_criticalParameter true) hq.1 A m hcap f,
    (hf q hq).1,(hf q hq).2,rfl⟩

/-- An affinity modulus for one capped policy must pay the proved critical
base cost. The estimator and every one-run guarantee are derived. -/
theorem critical_capped_affinity_obstruction : ∃ c : ℝ, 0 < c ∧
    ∀ (R E : Type) [MeasurableSpace R] [MeasurableSpace E]
      (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R E)
      (m : ℕ), (∀ z, A.stop z ≤ m) → ∀ (ρ : unitInterval),
      0 < (ρ : ℝ) → (ρ : ℝ) ≤ 1/4 → ∀ (n : ℕ) (ε : ℝ),
      0 ≤ ε → 3*ε ≤ (ρ : ℝ)/64 →
      (∀ q r : ℝ → unitInterval, CappedPrior criticalGapLaw (ρ : ℝ) q →
        CappedPrior criticalGapLaw (ρ : ℝ) r →
        1/2 ≤ ((hellingerAffinity
          (cappedTranscriptLaw criticalGapLaw ν
            (fun d => criticalParameter d false) (fun d => criticalParameter d true) q A m)
          (cappedTranscriptLaw criticalGapLaw ν
            (fun d => criticalParameter d false) (fun d => criticalParameter d true) r A m)).toReal)^n →
        (∫ d, (q d : ℝ) ∂criticalGapLaw)-(∫ d, (r d : ℝ) ∂criticalGapLaw) < 2*ε) →
      c*(ρ : ℝ)*criticalLogFactor (ρ : ℝ) ≤
        ((n : ℝ)*(9*ε^2))*(populationExpectedWork criticalGapLaw ν
          (fun d => criticalParameter d false) (fun d => criticalParameter d true) (fun _ => 0) A).toReal := by
  obtain ⟨c,hc,hbase⟩ := critical_base_cost
  refine ⟨c,hc,?_⟩
  intro R E _ _ ν _ A m hcap ρ hρ hρ' n ε hε hsmall hsep
  obtain ⟨f,hf⟩ := capped_observation_one_run criticalGapLaw ν
    (fun d => criticalParameter d false) (fun d => criticalParameter d true)
    (measurable_criticalParameter false) (measurable_criticalParameter true)
    A m hcap (ρ : ℝ) ε hρ.le hε n critical_parameters_interior hsep
  have h := hbase R ν (cappedStatisticProcedure A m hcap f) ρ hρ hρ'
    ((n : ℝ)*(9*ε^2)) (by positivity) (fun q hq => (hf q hq).2) (fun q hq => ?_)
    (fun q hq => (hf q hq).1.trans hsmall)
  · simpa only [cappedStatisticProcedure_work] using h
  · rw [cappedStatisticProcedure_work]
    exact ne_top_of_le_ne_top (by simp) (population_capped_work_le criticalGapLaw ν
      (fun d => criticalParameter d false) (fun d => criticalParameter d true) q A m hcap)

/-- For each capped policy, there is an actual admissible separated population
pair with high n-fold affinity whenever its null work violates the base cost.
This quantifier order does not yet assert one common pair for every policy. -/
theorem critical_capped_policy_pair : ∃ c : ℝ, 0 < c ∧
    ∀ (R E : Type) [MeasurableSpace R] [MeasurableSpace E]
      (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R E)
      (m : ℕ), (∀ z, A.stop z ≤ m) → ∀ (ρ : unitInterval),
      0 < (ρ : ℝ) → (ρ : ℝ) ≤ 1/4 → ∀ (n : ℕ) (ε : ℝ),
      0 ≤ ε → 3*ε ≤ (ρ : ℝ)/64 →
      ((n : ℝ)*(9*ε^2))*(populationExpectedWork criticalGapLaw ν
        (fun d => criticalParameter d false) (fun d => criticalParameter d true) (fun _ => 0) A).toReal <
        c*(ρ : ℝ)*criticalLogFactor (ρ : ℝ) →
      ∃ q r : ℝ → unitInterval, CappedPrior criticalGapLaw (ρ : ℝ) q ∧
        CappedPrior criticalGapLaw (ρ : ℝ) r ∧
        2*ε ≤ (∫ d, (q d : ℝ) ∂criticalGapLaw)-(∫ d, (r d : ℝ) ∂criticalGapLaw) ∧
        1/2 ≤ ((hellingerAffinity
          (cappedTranscriptLaw criticalGapLaw ν
            (fun d => criticalParameter d false) (fun d => criticalParameter d true) q A m)
          (cappedTranscriptLaw criticalGapLaw ν
            (fun d => criticalParameter d false) (fun d => criticalParameter d true) r A m)).toReal)^n := by
  obtain ⟨c,hc,hcost⟩ := critical_capped_affinity_obstruction
  refine ⟨c,hc,?_⟩
  intro R E _ _ ν _ A m hcap ρ hρ hρ' n ε hε hsmall hlt
  by_contra hn
  have hsep : ∀ q r : ℝ → unitInterval, CappedPrior criticalGapLaw (ρ : ℝ) q →
      CappedPrior criticalGapLaw (ρ : ℝ) r →
      1/2 ≤ ((hellingerAffinity
        (cappedTranscriptLaw criticalGapLaw ν
          (fun d => criticalParameter d false) (fun d => criticalParameter d true) q A m)
        (cappedTranscriptLaw criticalGapLaw ν
          (fun d => criticalParameter d false) (fun d => criticalParameter d true) r A m)).toReal)^n →
      (∫ d, (q d : ℝ) ∂criticalGapLaw)-(∫ d, (r d : ℝ) ∂criticalGapLaw) < 2*ε := by
    intro q r hq hr ha
    apply lt_of_not_ge
    intro hgap
    exact hn ⟨q,r,hq,hr,hgap,ha⟩
  exact (not_lt_of_ge (hcost R E ν A m hcap ρ hρ hρ' n ε hε hsmall hsep)) hlt

end ThresholdHC.CriticalEntropy
