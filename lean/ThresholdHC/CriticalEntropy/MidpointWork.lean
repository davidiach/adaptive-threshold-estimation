import ThresholdHC.CriticalEntropy.CriticalCommonPair

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace ThresholdHC.CriticalEntropy

def midpointPrior {D : Type} (q r : D → unitInterval) (d : D) : unitInterval :=
  ⟨((q d : ℝ)+(r d : ℝ))/2, by
    constructor <;> linarith [(q d).property.1,(q d).property.2,(r d).property.1,(r d).property.2]⟩

theorem measurable_midpointPrior {D : Type} [MeasurableSpace D]
    (q r : D → unitInterval) (hq : Measurable q) (hr : Measurable r) :
    Measurable (midpointPrior q r) := by
  apply Measurable.subtype_mk
  exact ((measurable_subtype_coe.comp hq).add (measurable_subtype_coe.comp hr)).div_const 2

theorem unitInterval_integrable {D : Type} [MeasurableSpace D]
    (μ : Measure D) [IsFiniteMeasure μ] (q : D → unitInterval) (hq : Measurable q) :
    Integrable (fun d => (q d : ℝ)) μ := by
  apply Integrable.of_bound (measurable_subtype_coe.comp hq).aestronglyMeasurable 1
  apply ae_of_all
  intro d
  change ‖(q d : ℝ)‖ ≤ 1
  rw [Real.norm_eq_abs,abs_of_nonneg (q d).property.1]
  exact (q d).property.2

theorem midpointPrior_integral {D : Type} [MeasurableSpace D]
    (μ : Measure D) [IsFiniteMeasure μ] (q r : D → unitInterval)
    (hq : Measurable q) (hr : Measurable r) :
    (∫ d, (midpointPrior q r d : ℝ) ∂μ) =
      ((∫ d, (q d : ℝ) ∂μ)+(∫ d, (r d : ℝ) ∂μ))/2 := by
  change (∫ d, ((q d : ℝ)+(r d : ℝ))/2 ∂μ) = _
  rw [integral_div,integral_add (unitInterval_integrable μ q hq) (unitInterval_integrable μ r hr)]

theorem cappedPrior_midpoint {D : Type} [MeasurableSpace D]
    (μ : Measure D) [IsProbabilityMeasure μ] (ρ : ℝ) (q r : D → unitInterval)
    (hq : CappedPrior μ ρ q) (hr : CappedPrior μ ρ r) :
    CappedPrior μ ρ (midpointPrior q r) := by
  refine ⟨measurable_midpointPrior q r hq.1 hr.1,?_,?_⟩
  · intro d
    change ((q d : ℝ)+(r d : ℝ))/2 ≤ 1/2
    have := hq.2.1 d
    have := hr.2.1 d
    linarith
  · rw [midpointPrior_integral μ q r hq.1 hr.1]
    linarith [hq.2.2,hr.2.2]

theorem unitInterval_memLp {D : Type} [MeasurableSpace D]
    (μ : Measure D) [IsFiniteMeasure μ] (q : D → unitInterval) (hq : Measurable q) :
    MemLp (fun d => (q d : ℝ)) 2 μ := by
  apply MemLp.of_bound (measurable_subtype_coe.comp hq).aestronglyMeasurable 1
  apply ae_of_all
  intro d
  change ‖(q d : ℝ)‖ ≤ 1
  rw [Real.norm_eq_abs,abs_of_nonneg (q d).property.1]
  exact (q d).property.2

theorem populationWordLikelihood_real_midpoint {D : Type} [MeasurableSpace D]
    (μ : Measure D) [IsProbabilityMeasure μ] (p₀ p₁ q r : D → unitInterval)
    (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q) (hr : Measurable r)
    (n k : ℕ) :
    (populationWordLikelihood μ p₀ p₁ (midpointPrior q r) n k).toReal =
      ((populationWordLikelihood μ p₀ p₁ q n k).toReal+
        (populationWordLikelihood μ p₀ p₁ r n k).toReal)/2 := by
  obtain ⟨g,b,hg⟩ := populationWordLikelihood_affine_moment μ p₀ p₁ h₀ h₁ n k
  rw [hg _ (measurable_midpointPrior q r hq hr),hg q hq,hg r hr]
  have hiq : Integrable (fun d => (q d : ℝ)*g d) μ :=
    (unitInterval_memLp μ q hq).integrable_mul (Lp.memLp g)
  have hir : Integrable (fun d => (r d : ℝ)*g d) μ :=
    (unitInterval_memLp μ r hr).integrable_mul (Lp.memLp g)
  have he : (fun d => (midpointPrior q r d : ℝ)*g d) =
      fun d => ((q d : ℝ)*g d+(r d : ℝ)*g d)/2 := by
    funext d
    change (((q d : ℝ)+(r d : ℝ))/2)*g d = _
    ring
  rw [he,integral_div,integral_add hiq hir]
  ring

/-- The null work is at most twice work at any prior bounded by one half.
This is an extended-real statement and does not discard infinite costs. -/
theorem null_work_le_twice_population_work {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (hq : Measurable q) (hhalf : ∀ d, (q d : ℝ) ≤ 1/2) (A : StoppedProcedure R E) :
    populationExpectedWork μ ν p₀ p₁ (fun _ => 0) A ≤
      2*populationExpectedWork μ ν p₀ p₁ q A := by
  rw [population_work_formula μ ν p₀ p₁ (fun _ => 0) h₀ h₁ measurable_const A,
    population_work_formula μ ν p₀ p₁ q h₀ h₁ hq A]
  rw [← lintegral_const_mul' 2 _ (by norm_num)]
  apply lintegral_mono
  intro d
  have hc : (1 : ℝ≥0∞) ≤ 2*ENNReal.ofReal (1-(q d : ℝ)) := by
    have h := ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ 2*(1-(q d : ℝ)) by linarith [hhalf d])
    rw [ENNReal.ofReal_mul (by norm_num)] at h
    norm_num only [ENNReal.ofReal_one,ENNReal.ofReal_ofNat] at h
    exact h
  calc
    _ = 1*expectedStoppedProcedureWork ν (p₀ d) A := by simp
    _ ≤ (2*ENNReal.ofReal (1-(q d : ℝ)))*expectedStoppedProcedureWork ν (p₀ d) A :=
      mul_le_mul' hc le_rfl
    _ = 2*(ENNReal.ofReal (1-(q d : ℝ))*expectedStoppedProcedureWork ν (p₀ d) A) := by rw [mul_assoc]
    _ ≤ _ := mul_le_mul' le_rfl (le_add_left le_rfl)

end ThresholdHC.CriticalEntropy
