import ThresholdHC.CriticalEntropy.Activation
import ThresholdHC.CriticalEntropy.CriticalScale

noncomputable section
open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal
namespace ThresholdHC.CriticalEntropy

theorem population_null_work_ge_activation {D R : Type}
    [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (A : StoppedProcedure R ℝ) :
    ν (activeSeeds A) ≤ populationExpectedWork μ ν p₀ p₁ (fun _ => 0) A := by
  rw [population_work_formula μ ν p₀ p₁ (fun _ => 0) h₀ h₁ measurable_const A]
  norm_num
  calc
    _ = ∫⁻ _d, ν (activeSeeds A) ∂μ := by simp
    _ ≤ _ := lintegral_mono (fun d => activation_probability_le_work ν (p₀ d) A)

/-- The actual conditioned procedure satisfies all BC7 cost bounds. No positive
activation, independence, mean-preservation or conditional-moment hypothesis is supplied. -/
theorem activation_product_bounds {R : Type} [MeasurableSpace R]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : ℝ → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (A : StoppedProcedure R ℝ) (ρ : unitInterval) (hρ : 0 < (ρ : ℝ))
    (hρ' : (ρ : ℝ) ≤ 1/4) (M : ℝ) (hM : 0 ≤ M)
    (hguar : CappedPopulationGuarantee μ ν p₀ p₁ A (ρ : ℝ) M) :
    let p := ν.real (activeSeeds A)
    let m := p*M+2*(ρ : ℝ)^2
    let W := (populationExpectedWork μ ν p₀ p₁ (fun _ => 0) A).toReal
    let WZ := (populationExpectedWork μ (cond ν (activeSeeds A)) p₀ p₁ (fun _ => 0)
      (activeProcedure ν A)).toReal
    ν (activeSeeds A) ≠ 0 ∧
    CappedPopulationGuarantee μ (cond ν (activeSeeds A)) p₀ p₁ (activeProcedure ν A) (ρ : ℝ) m ∧
    2*(ρ : ℝ)/3 ≤ m ∧ 1 ≤ WZ ∧ WZ = W/p ∧
    m ≤ 4*(M*W) ∧ m*WZ ≤ 4*(M*W) ∧ (ρ : ℝ)/6 ≤ M*W := by
  dsimp only
  let p := ν.real (activeSeeds A)
  let m := p*M+2*(ρ : ℝ)^2
  let W := (populationExpectedWork μ ν p₀ p₁ (fun _ => 0) A).toReal
  let WZ := (populationExpectedWork μ (cond ν (activeSeeds A)) p₀ p₁ (fun _ => 0)
    (activeProcedure ν A)).toReal
  obtain ⟨hp,hnew⟩ := active_population_guarantee μ ν p₀ p₁ h₀ h₁ A ρ hρ hρ' M hM hguar
  let : IsProbabilityMeasure (cond ν (activeSeeds A)) := cond_isProbabilityMeasure hp
  have hp₀ : 0 < p := ENNReal.toReal_pos hp (measure_ne_top _ _)
  have hm₀ : 0 ≤ m := by dsimp [m]; positivity
  have hm := capped_guarantee_moment_floor μ (cond ν (activeSeeds A)) p₀ p₁ h₀ h₁
    (activeProcedure ν A) ρ hρ hρ' m hm₀ hnew
  have hc₀ := cappedPrior_const μ (ρ : ℝ) 0 (by norm_num) (by simpa using hρ.le)
  have hWfin := hguar.work _ hc₀
  have hpW : p ≤ W := ENNReal.toReal_mono hWfin (population_null_work_ge_activation μ ν p₀ p₁ h₀ h₁ A)
  have hWZ : WZ = W/p := by
    dsimp [WZ,W,p]
    rw [population_activation_work μ ν p₀ p₁ (fun _ => 0) h₀ h₁ measurable_const A hp,
      ENNReal.toReal_mul,ENNReal.toReal_inv]
    simp only [measureReal_def]
    ring
  have hWZ₁ : 1 ≤ WZ := by
    rw [hWZ]
    exact (le_div_iff₀ hp₀).mpr (by simpa using hpW)
  have hρsq : 2*(ρ : ℝ)^2 ≤ (ρ : ℝ)/2 := by
    nlinarith [mul_nonneg hρ.le (sub_nonneg.mpr hρ')]
  have hpM : (ρ : ℝ)/6 ≤ p*M := by dsimp [m] at hm; linarith
  have hmp : m ≤ 4*(p*M) := by dsimp [m]; linarith
  have hpMW : p*M ≤ M*W := by nlinarith [mul_le_mul_of_nonneg_right hpW hM]
  have hprod : m*WZ ≤ 4*(M*W) := by
    rw [hWZ]
    calc
      _ ≤ (4*(p*M))*(W/p) := mul_le_mul_of_nonneg_right hmp (by positivity)
      _ = _ := by field_simp
  exact ⟨hp,hnew,hm,hWZ₁,hWZ,le_trans hmp (by linarith),hprod,hpM.trans hpMW⟩

theorem critical_product_scale {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R ℝ)
    (ρ : unitInterval) (hρ : 0 < (ρ : ℝ)) (hρ' : (ρ : ℝ) ≤ 1/4)
    (M : ℝ) (hM : 0 ≤ M)
    (hguar : CappedPopulationGuarantee criticalGapLaw ν
      (fun d => criticalParameter d false) (fun d => criticalParameter d true) A (ρ : ℝ) M) :
    let P := M*(populationExpectedWork criticalGapLaw ν
      (fun d => criticalParameter d false) (fun d => criticalParameter d true) (fun _ => 0) A).toReal
    (ρ : ℝ)/6 ≤ P ∧
    ∀ (K : ℕ), 32 ≤ Real.log (K : ℝ) →
      (∀ i : Fin K, 560*P ≤ criticalGapLaw.real (criticalAnnulus (i.val+3))) →
      (ρ : ℝ)*((K : ℝ)*Real.log (K : ℝ)) ≤ (2625536/3)*P := by
  dsimp only
  let p₀ := fun d => criticalParameter d false
  let p₁ := fun d => criticalParameter d true
  obtain ⟨hp,hnew,hm,_hwork,_hidentity,hsmall,hprod,hfloor⟩ :=
    activation_product_bounds criticalGapLaw ν p₀ p₁ (measurable_criticalParameter false)
      (measurable_criticalParameter true) A ρ hρ hρ' M hM hguar
  let : IsProbabilityMeasure (cond ν (activeSeeds A)) := cond_isProbabilityMeasure hp
  refine ⟨hfloor,?_⟩
  intro K hK hmass
  have he := critical_scale_product (cond ν (activeSeeds A)) (activeProcedure ν A) ρ hρ hρ'
    _ hm hnew K hK (fun i => by linarith [hmass i])
  nlinarith

end ThresholdHC.CriticalEntropy
