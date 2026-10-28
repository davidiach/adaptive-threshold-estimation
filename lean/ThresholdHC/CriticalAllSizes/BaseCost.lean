import ThresholdHC.CriticalAllSizes.Asymptotics
import ThresholdHC.CriticalEntropy.BaseCost

noncomputable section
open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal
namespace ThresholdHC.CriticalAllSizes
open CriticalEntropy

/-- Raw-second-moment version of the critical single-coin null-cost lower bound. -/
theorem critical_raw_base_cost_explicit :
    ∀ (R : Type) [MeasurableSpace R] (ν : Measure R) [IsProbabilityMeasure ν]
      (A : StoppedProcedure R ℝ) (ρ : unitInterval),
      0 < (ρ : ℝ) → (ρ : ℝ) ≤ 1/4 → ∀ (M : ℝ), 0 ≤ M →
      CappedPopulationGuarantee criticalGapLaw ν
        (fun d => criticalParameter d false) (fun d => criticalParameter d true) A (ρ : ℝ) M →
      (1/10000000000 : ℝ)*(ρ : ℝ)*criticalLogFactor (ρ : ℝ) ≤
        M*(populationExpectedWork criticalGapLaw ν
          (fun d => criticalParameter d false) (fun d => criticalParameter d true) (fun _ => 0) A).toReal := by
  intro R _ ν _ A ρ hρ hρ' M hM hguar
  obtain ⟨hfloor,hscales⟩ := critical_product_scale_all ν A ρ hρ hρ' M hM hguar
  exact critical_scalar_base_cost_explicit (ρ : ℝ) _ hρ hρ' hfloor hscales

/-- The critical single-coin variance/null-work lower bound, with one universal
positive constant for every rarity. Extended variance bounds enforce genuine
square integrability; the full population minimax transfer is a separate theorem. -/
theorem critical_base_cost_explicit :
    ∀ (R : Type) [MeasurableSpace R] (ν : Measure R) [IsProbabilityMeasure ν]
      (A : StoppedProcedure R ℝ) (ρ : unitInterval),
      0 < (ρ : ℝ) → (ρ : ℝ) ≤ 1/4 → ∀ (V : ℝ), 0 ≤ V →
      (∀ q : ℝ → unitInterval, CappedPrior criticalGapLaw (ρ : ℝ) q →
        evariance (fun z => A.output (populationInput
          (fun d => criticalParameter d false) (fun d => criticalParameter d true) q z))
          (populationMeasure criticalGapLaw ν) ≤ ENNReal.ofReal V) →
      (∀ q : ℝ → unitInterval, CappedPrior criticalGapLaw (ρ : ℝ) q →
        populationExpectedWork criticalGapLaw ν
          (fun d => criticalParameter d false) (fun d => criticalParameter d true) q A ≠ ∞) →
      (∀ q : ℝ → unitInterval, CappedPrior criticalGapLaw (ρ : ℝ) q →
        |populationMean criticalGapLaw ν
          (fun d => criticalParameter d false) (fun d => criticalParameter d true) q A -
          (∫ d,(q d : ℝ) ∂criticalGapLaw)| ≤ (ρ : ℝ)/64) →
      (1/15000000000 : ℝ)*(ρ : ℝ)*criticalLogFactor (ρ : ℝ) ≤
        V*(populationExpectedWork criticalGapLaw ν
          (fun d => criticalParameter d false) (fun d => criticalParameter d true) (fun _ => 0) A).toReal := by
  intro R _ ν _ A ρ hρ hρ' V hV hv hw hb
  let p₀ := fun d => criticalParameter d false
  let p₁ := fun d => criticalParameter d true
  have hp₀ : Measurable p₀ := measurable_criticalParameter false
  have hp₁ : Measurable p₁ := measurable_criticalParameter true
  have hc₀ := cappedPrior_const criticalGapLaw (ρ : ℝ) 0 (by norm_num) (by simpa using hρ.le)
  have hcρ := cappedPrior_const criticalGapLaw (ρ : ℝ) ρ (by linarith) le_rfl
  have hfloor := population_evariance_floor criticalGapLaw ν p₀ p₁ hp₀ hp₁ ρ hρ hρ' A
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hv _ hc₀))
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hv _ hcρ))
    (by simpa using hb _ hc₀) (by simpa using hb _ hcρ)
  have hVfloor : 2*(ρ : ℝ)/3 ≤ V := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hfloor.trans (hv _ hcρ))
    simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*(ρ : ℝ)/3),
      ENNReal.toReal_ofReal hV] using h
  have hguar : CappedPopulationGuarantee criticalGapLaw ν p₀ p₁ A (ρ : ℝ) (3*V/2) := by
    refine ⟨?_,hw,hb⟩
    intro q hq
    exact population_moment_bound_of_evariance criticalGapLaw ν p₀ p₁ q hp₀ hp₁ hq.1 A
      (ρ : ℝ) V hρ hρ' hVfloor hq.2.2 (hb q hq) (hv q hq)
  have h := critical_raw_base_cost_explicit R ν A ρ hρ hρ' (3*V/2) (by positivity) hguar
  nlinarith

end ThresholdHC.CriticalAllSizes
