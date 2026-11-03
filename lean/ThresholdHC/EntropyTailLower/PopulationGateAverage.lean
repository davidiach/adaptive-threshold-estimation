import ThresholdHC.EntropyTailLower.GateAverage
import ThresholdHC.EntropyTailLower.GeneralGoodGaps

/-! Population moment and actual-work bounds for the fixed-repeat gate.
The law may have atoms. Fair activation positivity remains a premise;
no transformed bias guarantee is asserted. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal
namespace ThresholdHC.EntropyTailLower
open ThresholdHC.Tier2 ThresholdHC.CriticalEntropy

theorem population_gateAverage_bounds {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (A : StoppedProcedure R ℝ) (a : ℝ) (ha : 0 < a) (ha4 : a ≤ 1/4)
    (hclose : ∀ᵐ d ∂μ, |(p₀ d:ℝ)-1/2| ≤ a ∧ |(p₁ d:ℝ)-1/2| ≤ a)
    (c : unitInterval) (hc : 0 < (c:ℝ))
    (hm₀ : populationSecondMoment μ ν p₀ p₁ (fun _ => 0) A ≠ ∞)
    (hm₁ : populationSecondMoment μ ν p₀ p₁ (fun _ => c) A ≠ ∞)
    (hw₀ : populationExpectedWork μ ν p₀ p₁ (fun _ => 0) A ≠ ∞)
    (hw₁ : populationExpectedWork μ ν p₀ p₁ (fun _ => c) A ≠ ∞)
    (hact : 0 < fairActivation ν A a) (q : D → unitInterval) (hq : Measurable q) :
    let β := fairActivation ν A a
    let Z := gateAverage A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊ β
    let η := Measure.pi (fun _ : Fin ((gateBatchCount β-1)+1) => ν)
    populationSecondMoment μ η p₀ p₁ q Z ≤
      ENNReal.ofReal ((1+exp 12)*β)*populationSecondMoment μ ν p₀ p₁ q A ∧
    populationExpectedWork μ η p₀ p₁ q Z ≤
      ENNReal.ofReal (2/β)*populationExpectedWork μ ν p₀ p₁ q A := by
  dsimp only
  have hf := (population_conditional_finiteness μ ν p₀ p₁ h₀ h₁ c hc A hm₀ hm₁ hw₀ hw₁).1
  constructor
  · rw [population_second_moment_formula _ _ _ _ _ h₀ h₁ hq,
      population_second_moment_formula _ _ _ _ _ h₀ h₁ hq,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono_ae
    filter_upwards [hf,hclose] with d hd hp
    have hM₀ := (conditionalSecondMoment_finite_iff ν (p₀ d) A).mpr hd.1
    have hM₁ := (conditionalSecondMoment_finite_iff ν (p₁ d) A).mpr hd.2.1
    have hb₀ := scaled_gateAverage_secondMoment_le ν A a ha ha4 hact (p₀ d) hp.1 hd.2.2.1 hM₀
    have hb₁ := scaled_gateAverage_secondMoment_le ν A a ha ha4 hact (p₁ d) hp.2 hd.2.2.2 hM₁
    calc
      _ ≤ ENNReal.ofReal (q d:ℝ)*(ENNReal.ofReal ((1+exp 12)*fairActivation ν A a)*
          conditionalSecondMoment ν (p₁ d) A)+
          ENNReal.ofReal (1-(q d:ℝ))*(ENNReal.ofReal ((1+exp 12)*fairActivation ν A a)*
            conditionalSecondMoment ν (p₀ d) A) :=
        add_le_add (mul_le_mul' le_rfl hb₁) (mul_le_mul' le_rfl hb₀)
      _ = _ := by ring
  · rw [population_work_formula _ _ _ _ _ h₀ h₁ hq,
      population_work_formula _ _ _ _ _ h₀ h₁ hq,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono_ae
    filter_upwards [hf] with d hd
    have hb₀ := gateAverage_work_le ν (p₀ d) A hd.2.2.1 ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊
      (fairActivation ν A a) hact measureReal_le_one
    have hb₁ := gateAverage_work_le ν (p₁ d) A hd.2.2.2 ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊
      (fairActivation ν A a) hact measureReal_le_one
    calc
      _ ≤ ENNReal.ofReal (q d:ℝ)*(ENNReal.ofReal (2/fairActivation ν A a)*
          expectedStoppedProcedureWork ν (p₁ d) A)+
          ENNReal.ofReal (1-(q d:ℝ))*(ENNReal.ofReal (2/fairActivation ν A a)*
            expectedStoppedProcedureWork ν (p₀ d) A) :=
        add_le_add (mul_le_mul' le_rfl hb₁) (mul_le_mul' le_rfl hb₀)
      _ = _ := by ring

theorem population_gate_activation_bound {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (A : StoppedProcedure R E) (a : ℝ) (ha : 0 < a) (ha4 : a ≤ 1/4)
    (hclose : ∀ᵐ d ∂μ, |(p₀ d:ℝ)-1/2| ≤ a) :
    ENNReal.ofReal (fairActivation ν A a) ≤
      ENNReal.ofReal (2*exp 12*a^2)*populationExpectedWork μ ν p₀ p₁ (fun _ => 0) A := by
  have hp : ∀ᵐ d ∂μ, ENNReal.ofReal (fairActivation ν A a) ≤
      ENNReal.ofReal (2*exp 12*a^2)*expectedStoppedProcedureWork ν (p₀ d) A := by
    filter_upwards [hclose] with d hd
    simpa only [fairActivation,measureReal_def,ENNReal.ofReal_toReal (measure_ne_top _ _)] using
      activationGate_fair_probability_le_biased_work ν A a ha ha4 (p₀ d) hd
  have h := lintegral_mono_ae hp
  rw [lintegral_const,measure_univ,mul_one,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h
  rw [population_work_formula _ _ _ _ _ h₀ h₁ measurable_const]
  simpa using h

theorem population_gateAverage_uniform {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (A : StoppedProcedure R ℝ) (ρ : unitInterval) (hρ : 0 < (ρ:ℝ)) (hρ4 : (ρ:ℝ) ≤ 1/4)
    (m : ℝ) (hguar : CappedPopulationGuarantee μ ν p₀ p₁ A (ρ:ℝ) m)
    (a : ℝ) (ha : 0 < a) (ha4 : a ≤ 1/4)
    (hclose : ∀ᵐ d ∂μ, |(p₀ d:ℝ)-1/2| ≤ a ∧ |(p₁ d:ℝ)-1/2| ≤ a)
    (hact : 0 < fairActivation ν A a) :
    let β := fairActivation ν A a
    let Z := gateAverage A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊ β
    let η := Measure.pi (fun _ : Fin ((gateBatchCount β-1)+1) => ν)
    ∀ q, CappedPrior μ (ρ:ℝ) q →
      populationSecondMoment μ η p₀ p₁ q Z ≤ ENNReal.ofReal (((1+exp 12)*β)*m) ∧
      populationExpectedWork μ η p₀ p₁ q Z ≠ ∞ := by
  dsimp only
  intro q hq
  have hc₀ := cappedPrior_const μ (ρ:ℝ) 0 (by norm_num) (by simpa using hρ.le)
  have hcρ := cappedPrior_const μ (ρ:ℝ) ρ (by linarith) le_rfl
  have hm₀ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hguar.moment _ hc₀)
  have hm₁ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hguar.moment _ hcρ)
  have hb := population_gateAverage_bounds μ ν p₀ p₁ h₀ h₁ A a ha ha4 hclose ρ hρ
    hm₀ hm₁ (hguar.work _ hc₀) (hguar.work _ hcρ) hact q hq.1
  refine ⟨?_,ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hguar.work q hq)) hb.2⟩
  calc
    _ ≤ ENNReal.ofReal ((1+exp 12)*fairActivation ν A a)*populationSecondMoment μ ν p₀ p₁ q A := hb.1
    _ ≤ ENNReal.ofReal ((1+exp 12)*fairActivation ν A a)*ENNReal.ofReal m :=
      mul_le_mul' le_rfl (hguar.moment q hq)
    _ = _ := (ENNReal.ofReal_mul (by positivity)).symm

theorem population_gateAverage_tradeoff {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (A : StoppedProcedure R ℝ) (ρ : unitInterval) (hρ : 0 < (ρ:ℝ)) (hρ4 : (ρ:ℝ) ≤ 1/4)
    (m : ℝ) (hm : 0 ≤ m) (hguar : CappedPopulationGuarantee μ ν p₀ p₁ A (ρ:ℝ) m)
    (a : ℝ) (ha : 0 < a) (ha4 : a ≤ 1/4)
    (hclose : ∀ᵐ d ∂μ, |(p₀ d:ℝ)-1/2| ≤ a ∧ |(p₁ d:ℝ)-1/2| ≤ a)
    (hact : 0 < fairActivation ν A a) :
    let β := fairActivation ν A a
    let Z := gateAverage A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊ β
    let η := Measure.pi (fun _ : Fin ((gateBatchCount β-1)+1) => ν)
    let mZ := (1+exp 12)*β*m
    mZ ≤ 2*exp 12*(1+exp 12)*a^2*m*(populationExpectedWork μ ν p₀ p₁ (fun _ => 0) A).toReal ∧
    mZ*(populationExpectedWork μ η p₀ p₁ (fun _ => 0) Z).toReal ≤
      2*(1+exp 12)*m*(populationExpectedWork μ ν p₀ p₁ (fun _ => 0) A).toReal := by
  dsimp only
  have hc₀ := cappedPrior_const μ (ρ:ℝ) 0 (by norm_num) (by simpa using hρ.le)
  have hcρ := cappedPrior_const μ (ρ:ℝ) ρ (by linarith) le_rfl
  have hm₀ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hguar.moment _ hc₀)
  have hm₁ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hguar.moment _ hcρ)
  have hw₀ := hguar.work _ hc₀
  have hb := population_gateAverage_bounds μ ν p₀ p₁ h₀ h₁ A a ha ha4 hclose ρ hρ
    hm₀ hm₁ hw₀ (hguar.work _ hcρ) hact (fun _ => 0) measurable_const
  have hp := population_gate_activation_bound μ ν p₀ p₁ h₀ h₁ A a ha ha4
    (hclose.mono (fun _ h => h.1))
  have hpr := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hw₀) hp
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal hact.le,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 2*exp 12*a^2)] at hpr
  have hwr := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hw₀) hb.2
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity : 0 ≤ 2/fairActivation ν A a)] at hwr
  constructor
  · calc
      _ = ((1+exp 12)*m)*fairActivation ν A a := by ring
      _ ≤ ((1+exp 12)*m)*(2*exp 12*a^2*(populationExpectedWork μ ν p₀ p₁ (fun _ => 0) A).toReal) :=
        mul_le_mul_of_nonneg_left hpr (by positivity)
      _ = _ := by ring
  · calc
      _ ≤ ((1+exp 12)*fairActivation ν A a*m)*
          ((2/fairActivation ν A a)*(populationExpectedWork μ ν p₀ p₁ (fun _ => 0) A).toReal) :=
        mul_le_mul_of_nonneg_left hwr (by positivity)
      _ = _ := by field_simp [hact.ne']

end ThresholdHC.EntropyTailLower
