import ThresholdHC.ConfidenceLocalization.RegularizedObservation

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace ThresholdHC.ConfidenceLocalization
open ThresholdHC.CriticalEntropy

/-- A variance times all-negative-work lower bound for every capped bounded
one-coin estimator whose bias is uniformly at most b on the half-prior class. -/
def NullVarianceObstruction {D : Type} [MeasurableSpace D]
    (μ : Measure D) (p₀ p₁ : D → unitInterval) (ρ b J : ℝ) : Prop :=
  ∀ {R : Type} [MeasurableSpace R] (ν : Measure R) [IsProbabilityMeasure ν]
    (A : StoppedProcedure R ℝ) (m : ℕ), (∀ z, A.stop z ≤ m) →
    (∃ C : ℝ, ∀ z, |A.output z| ≤ C) →
    ∀ V : ℝ, 0 ≤ V →
    (∀ q : D → unitInterval, CappedPrior μ ρ q →
      evariance (A.output ∘ populationInput p₀ p₁ q) (populationMeasure μ ν) ≤ ENNReal.ofReal V) →
    (∀ q : D → unitInterval, CappedPrior μ ρ q →
      |populationMean μ ν p₀ p₁ q A-(∫ d, (q d : ℝ) ∂μ)| ≤ b) →
    J ≤ V*(populationExpectedWork μ ν p₀ p₁ (fun _ => 0) A).toReal

theorem obstruction_bias_lt_half {D : Type} [MeasurableSpace D]
    (μ : Measure D) [IsProbabilityMeasure μ] (p₀ p₁ : D → unitInterval)
    {ρ b J : ℝ} (hJ : 0 < J)
    (hobs : NullVarianceObstruction μ p₀ p₁ ρ b J) : b < ρ/2 := by
  by_contra! hb
  let R := Fin 0 → Unit
  let ν : Measure R := Measure.dirac (fun i => Fin.elim0 i)
  let A := postprocessProcedure (emptyProcedure Unit Unit) (fun _ => ρ/2) measurable_const
  let : IsProbabilityMeasure (populationMeasure μ ν) := by unfold populationMeasure; infer_instance
  have h := hobs ν A 0 (fun _ => le_rfl) ⟨|ρ/2|,fun _ => le_rfl⟩ 0 le_rfl
    (fun q _ => by simp [A,postprocessProcedure,evariance])
    (fun q hq => by
      have hmean : 0 ≤ ∫ d, (q d : ℝ) ∂μ := integral_nonneg (fun d => (q d).property.1)
      have hmean' := hq.2.2
      change |(∫ _, ρ/2 ∂populationMeasure μ ν)-(∫ d, (q d : ℝ) ∂μ)| ≤ b
      simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
      apply abs_le.mpr
      constructor <;> linarith)
  simp only [zero_mul] at h
  linarith

end ThresholdHC.ConfidenceLocalization
