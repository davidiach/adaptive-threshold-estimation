import ThresholdHC.CriticalEntropy.PopulationMixture

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace ThresholdHC.CriticalEntropy

theorem population_memLp_of_moment {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) (ν : Measure R)
    (p₀ p₁ q : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (hq : Measurable q) (A : StoppedProcedure R ℝ)
    (hfin : populationSecondMoment μ ν p₀ p₁ q A ≠ ∞) :
    MemLp (fun z => A.output (populationInput p₀ p₁ q z)) 2 (populationMeasure μ ν) := by
  have hm : Measurable (fun z => A.output (populationInput p₀ p₁ q z)) :=
    A.measurable_output.comp (measurable_populationInput p₀ p₁ q h₀ h₁ hq)
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
  exact (lintegral_ofReal_ne_top_iff_integrable (hm.pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z => sq_nonneg _))).mp hfin

theorem population_second_moment_toReal {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) (ν : Measure R)
    (p₀ p₁ q : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (hq : Measurable q) (A : StoppedProcedure R ℝ)
    (hfin : populationSecondMoment μ ν p₀ p₁ q A ≠ ∞) :
    (∫ z, (A.output (populationInput p₀ p₁ q z))^2 ∂populationMeasure μ ν) =
      (populationSecondMoment μ ν p₀ p₁ q A).toReal := by
  exact integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (fun z => sq_nonneg _))
    (population_memLp_of_moment μ ν p₀ p₁ q h₀ h₁ hq A hfin).integrable_sq.aestronglyMeasurable

theorem variance_lower_of_mixture {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y₀ Y₁ Y : Ω → ℝ)
    (h₀ : MemLp Y₀ 2 μ) (h₁ : MemLp Y₁ 2 μ) (hY : MemLp Y 2 μ)
    (c : ℝ) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    (hm : (∫ z, Y z ∂μ) = c*(∫ z, Y₁ z ∂μ)+(1-c)*(∫ z, Y₀ z ∂μ))
    (hs : (∫ z, (Y z)^2 ∂μ) = c*(∫ z, (Y₁ z)^2 ∂μ)+(1-c)*(∫ z, (Y₀ z)^2 ∂μ)) :
    c*(1-c)*((∫ z, Y₁ z ∂μ)-(∫ z, Y₀ z ∂μ))^2 ≤ variance Y μ := by
  have hv₀ := variance_nonneg Y₀ μ
  have hv₁ := variance_nonneg Y₁ μ
  rw [variance_eq_sub h₀] at hv₀
  rw [variance_eq_sub h₁] at hv₁
  rw [variance_eq_sub hY]
  simp only [Pi.pow_apply] at *
  rw [hm,hs]
  have hp₀ := mul_nonneg (sub_nonneg.mpr hc₁) hv₀
  have hp₁ := mul_nonneg hc₀ hv₁
  nlinarith

theorem population_second_moment_const {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (c : unitInterval) (A : StoppedProcedure R ℝ) :
    populationSecondMoment μ ν p₀ p₁ (fun _ => c) A =
      ENNReal.ofReal (c : ℝ)*populationSecondMoment μ ν p₀ p₁ (fun _ => 1) A +
      ENNReal.ofReal (1-(c : ℝ))*populationSecondMoment μ ν p₀ p₁ (fun _ => 0) A := by
  have hsq : Measurable (fun z => ENNReal.ofReal ((A.output z)^2)) :=
    ENNReal.measurable_ofReal.comp (A.measurable_output.pow_const 2)
  unfold populationSecondMoment populationMeasure
  rw [population_lintegral_const μ ν p₀ p₁ h₀ h₁ c _ hsq,
    population_lintegral_const μ ν p₀ p₁ h₀ h₁ 1 _ hsq,
    population_lintegral_const μ ν p₀ p₁ h₀ h₁ 0 _ hsq]
  norm_num

theorem population_mean_const {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (c : unitInterval) (A : StoppedProcedure R ℝ)
    (hm₀ : populationSecondMoment μ ν p₀ p₁ (fun _ => 0) A ≠ ∞)
    (hm₁ : populationSecondMoment μ ν p₀ p₁ (fun _ => 1) A ≠ ∞) :
    populationMean μ ν p₀ p₁ (fun _ => c) A =
      (c : ℝ)*populationMean μ ν p₀ p₁ (fun _ => 1) A +
      (1-(c : ℝ))*populationMean μ ν p₀ p₁ (fun _ => 0) A := by
  have hsq : Measurable (fun z => ENNReal.ofReal ((A.output z)^2)) :=
    ENNReal.measurable_ofReal.comp (A.measurable_output.pow_const 2)
  have hi := population_finite_components μ ν p₀ p₁ h₀ h₁ 1 (by norm_num) _ hsq hm₀ hm₁
  have hi₀ := conditionalMean_integrable_of_moment μ ν p₀ h₀ A hi.1
  have hi₁ := conditionalMean_integrable_of_moment μ ν p₁ h₁ A hi.2
  have hfin : populationSecondMoment μ ν p₀ p₁ (fun _ => c) A ≠ ∞ :=
    population_finite_all μ ν p₀ p₁ h₀ h₁ 1 (by norm_num) _ hsq hm₀ hm₁ _ measurable_const
  have he₀ := population_mean_formula μ ν p₀ p₁ (fun _ => 0) h₀ h₁ measurable_const A hm₀
  have he₁ := population_mean_formula μ ν p₀ p₁ (fun _ => 1) h₀ h₁ measurable_const A hm₁
  norm_num at he₀ he₁
  rw [population_mean_formula μ ν p₀ p₁ (fun _ => c) h₀ h₁ measurable_const A hfin,
    he₀,he₁,integral_add (hi₁.const_mul _) (hi₀.const_mul _),integral_const_mul,integral_const_mul]

theorem population_variance_mixture_lower {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (c : unitInterval) (A : StoppedProcedure R ℝ)
    (hm₀ : populationSecondMoment μ ν p₀ p₁ (fun _ => 0) A ≠ ∞)
    (hm₁ : populationSecondMoment μ ν p₀ p₁ (fun _ => 1) A ≠ ∞) :
    (c : ℝ)*(1-(c : ℝ))*(populationMean μ ν p₀ p₁ (fun _ => 1) A -
      populationMean μ ν p₀ p₁ (fun _ => 0) A)^2 ≤
    variance (fun z => A.output (populationInput p₀ p₁ (fun _ => c) z)) (populationMeasure μ ν) := by
  let : IsProbabilityMeasure (populationMeasure μ ν) := by
    unfold populationMeasure; infer_instance
  have hsq : Measurable (fun z => ENNReal.ofReal ((A.output z)^2)) :=
    ENNReal.measurable_ofReal.comp (A.measurable_output.pow_const 2)
  have hfin : populationSecondMoment μ ν p₀ p₁ (fun _ => c) A ≠ ∞ :=
    population_finite_all μ ν p₀ p₁ h₀ h₁ 1 (by norm_num) _ hsq hm₀ hm₁ _ measurable_const
  have hreal := congrArg ENNReal.toReal (population_second_moment_const μ ν p₀ p₁ h₀ h₁ c A)
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hm₁)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hm₀)] at hreal
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal c.property.1,
    ENNReal.toReal_ofReal (sub_nonneg.mpr c.property.2)] at hreal
  apply variance_lower_of_mixture (populationMeasure μ ν)
    (fun z => A.output (populationInput p₀ p₁ (fun _ => 0) z))
    (fun z => A.output (populationInput p₀ p₁ (fun _ => 1) z)) _
    (population_memLp_of_moment μ ν p₀ p₁ _ h₀ h₁ measurable_const A hm₀)
    (population_memLp_of_moment μ ν p₀ p₁ _ h₀ h₁ measurable_const A hm₁)
    (population_memLp_of_moment μ ν p₀ p₁ _ h₀ h₁ measurable_const A hfin)
    (c : ℝ) c.property.1 c.property.2
  · exact population_mean_const μ ν p₀ p₁ h₀ h₁ c A hm₀ hm₁
  · simpa only [population_second_moment_toReal μ ν p₀ p₁ _ h₀ h₁ measurable_const A hfin,
      population_second_moment_toReal μ ν p₀ p₁ _ h₀ h₁ measurable_const A hm₁,
      population_second_moment_toReal μ ν p₀ p₁ _ h₀ h₁ measurable_const A hm₀] using hreal

/-- The paper's variance floor follows from bias at just the null and one
constant prior, with actual population moments supplying all integrability. -/
theorem population_variance_floor {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (ρ : unitInterval) (hρ : 0 < (ρ : ℝ)) (hρ' : (ρ : ℝ) ≤ 1/4)
    (A : StoppedProcedure R ℝ)
    (hm₀ : populationSecondMoment μ ν p₀ p₁ (fun _ => 0) A ≠ ∞)
    (hmρ : populationSecondMoment μ ν p₀ p₁ (fun _ => ρ) A ≠ ∞)
    (hb₀ : |populationMean μ ν p₀ p₁ (fun _ => 0) A| ≤ (ρ : ℝ)/64)
    (hbρ : |populationMean μ ν p₀ p₁ (fun _ => ρ) A-(ρ : ℝ)| ≤ (ρ : ℝ)/64) :
    2*(ρ : ℝ)/3 ≤
      variance (fun z => A.output (populationInput p₀ p₁ (fun _ => ρ) z)) (populationMeasure μ ν) := by
  have hsq : Measurable (fun z => ENNReal.ofReal ((A.output z)^2)) :=
    ENNReal.measurable_ofReal.comp (A.measurable_output.pow_const 2)
  have hm₁ : populationSecondMoment μ ν p₀ p₁ (fun _ => 1) A ≠ ∞ :=
    population_finite_all μ ν p₀ p₁ h₀ h₁ ρ hρ _ hsq hm₀ hmρ _ measurable_const
  have he := population_mean_const μ ν p₀ p₁ h₀ h₁ ρ A hm₀ hm₁
  have hd : (31 : ℝ)/32 ≤ populationMean μ ν p₀ p₁ (fun _ => 1) A -
      populationMean μ ν p₀ p₁ (fun _ => 0) A := by
    apply (mul_le_mul_iff_right₀ hρ).mp
    calc
      (ρ : ℝ)*(31/32) ≤ populationMean μ ν p₀ p₁ (fun _ => ρ) A -
          populationMean μ ν p₀ p₁ (fun _ => 0) A := by
        linarith [(abs_le.mp hb₀).2,(abs_le.mp hbρ).1]
      _ = (ρ : ℝ)*(populationMean μ ν p₀ p₁ (fun _ => 1) A -
          populationMean μ ν p₀ p₁ (fun _ => 0) A) := by rw [he]; ring
  have hd2 : ((31 : ℝ)/32)^2 ≤ (populationMean μ ν p₀ p₁ (fun _ => 1) A -
      populationMean μ ν p₀ p₁ (fun _ => 0) A)^2 := by nlinarith
  calc
    2*(ρ : ℝ)/3 ≤ (ρ : ℝ)*(1-(ρ : ℝ))*((31 : ℝ)/32)^2 := by
      nlinarith [mul_nonneg hρ.le (show 0 ≤ 1/4-(ρ : ℝ) by linarith)]
    _ ≤ (ρ : ℝ)*(1-(ρ : ℝ))*(populationMean μ ν p₀ p₁ (fun _ => 1) A -
        populationMean μ ν p₀ p₁ (fun _ => 0) A)^2 :=
      mul_le_mul_of_nonneg_left hd2 (mul_nonneg hρ.le (sub_nonneg.mpr ρ.property.2))
    _ ≤ _ := population_variance_mixture_lower μ ν p₀ p₁ h₀ h₁ ρ A hm₀ hm₁

theorem conditionalMean_sq_le_moment {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (p : unitInterval) (A : StoppedProcedure R ℝ)
    (hf : conditionalSecondMoment ν p A ≠ ∞) :
    (conditionalMean ν p A)^2 ≤ (conditionalSecondMoment ν p A).toReal := by
  have hi := (conditionalSecondMoment_finite_iff ν p A).mp hf
  let : IsProbabilityMeasure ((ν.prod (Tier2.tapeMeasure p)).map A.output) :=
    by infer_instance
  have hv := variance_nonneg id ((ν.prod (Tier2.tapeMeasure p)).map A.output)
  rw [variance_eq_sub hi] at hv
  simp only [Pi.pow_apply, id_eq] at hv
  rw [conditionalMean_output_law ν p A, conditionalSecondMoment_output_law ν p A hf] at hv
  linarith

theorem population_moment_bound_of_variance {D R : Type}
    [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (hq : Measurable q) (A : StoppedProcedure R ℝ)
    (ρ V : ℝ) (hρ : 0 < ρ) (hρ' : ρ ≤ 1/4) (hV : 2*ρ/3 ≤ V)
    (hfin : populationSecondMoment μ ν p₀ p₁ q A ≠ ∞)
    (hqρ : (∫ d, (q d : ℝ) ∂μ) ≤ ρ)
    (hb : |populationMean μ ν p₀ p₁ q A - (∫ d, (q d : ℝ) ∂μ)| ≤ ρ/64)
    (hv : variance (fun z => A.output (populationInput p₀ p₁ q z))
      (populationMeasure μ ν) ≤ V) :
    (populationSecondMoment μ ν p₀ p₁ q A).toReal ≤ 3*V/2 := by
  let : IsProbabilityMeasure (populationMeasure μ ν) := by
    unfold populationMeasure; infer_instance
  have hq₀ : 0 ≤ (∫ d, (q d : ℝ) ∂μ) := integral_nonneg (fun d => (q d).property.1)
  have hm₀ : -(65*ρ/64) ≤ populationMean μ ν p₀ p₁ q A := by
    linarith [(abs_le.mp hb).1]
  have hm₁ : populationMean μ ν p₀ p₁ q A ≤ 65*ρ/64 := by
    linarith [(abs_le.mp hb).2]
  have hm2 : (populationMean μ ν p₀ p₁ q A)^2 ≤ (65*ρ/64)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hm₁) (sub_nonneg.mpr hm₀)]
  have hs : (65*ρ/64)^2 ≤ V/2 := by
    nlinarith [mul_nonneg hρ.le (show 0 ≤ 1/4-ρ by linarith)]
  rw [variance_eq_sub (population_memLp_of_moment μ ν p₀ p₁ q h₀ h₁ hq A hfin)] at hv
  simp only [Pi.pow_apply] at hv
  rw [population_second_moment_toReal μ ν p₀ p₁ q h₀ h₁ hq A hfin] at hv
  change (populationSecondMoment μ ν p₀ p₁ q A).toReal -
    (populationMean μ ν p₀ p₁ q A)^2 ≤ V at hv
  linarith

/-- Finiteness is stated for extended variance. The ordinary real variance is
totalized and cannot by itself certify square integrability. -/
theorem population_moment_finite_of_evariance {D R : Type}
    [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (hq : Measurable q) (A : StoppedProcedure R ℝ)
    (hv : evariance (fun z => A.output (populationInput p₀ p₁ q z))
      (populationMeasure μ ν) ≠ ∞) :
    populationSecondMoment μ ν p₀ p₁ q A ≠ ∞ := by
  let : IsProbabilityMeasure (populationMeasure μ ν) := by
    unfold populationMeasure; infer_instance
  have hme : Measurable (fun z => A.output (populationInput p₀ p₁ q z)) :=
    A.measurable_output.comp (measurable_populationInput p₀ p₁ q h₀ h₁ hq)
  have hL2 := (evariance_lt_top_iff_memLp hme.aestronglyMeasurable).mp (lt_top_iff_ne_top.mpr hv)
  exact (lintegral_ofReal_ne_top_iff_integrable (hme.pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z => sq_nonneg _))).mpr hL2.integrable_sq

theorem population_evariance_floor {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (ρ : unitInterval) (hρ : 0 < (ρ : ℝ)) (hρ' : (ρ : ℝ) ≤ 1/4)
    (A : StoppedProcedure R ℝ)
    (hv₀ : evariance (fun z => A.output (populationInput p₀ p₁ (fun _ => 0) z))
      (populationMeasure μ ν) ≠ ∞)
    (hvρ : evariance (fun z => A.output (populationInput p₀ p₁ (fun _ => ρ) z))
      (populationMeasure μ ν) ≠ ∞)
    (hb₀ : |populationMean μ ν p₀ p₁ (fun _ => 0) A| ≤ (ρ : ℝ)/64)
    (hbρ : |populationMean μ ν p₀ p₁ (fun _ => ρ) A-(ρ : ℝ)| ≤ (ρ : ℝ)/64) :
    ENNReal.ofReal (2*(ρ : ℝ)/3) ≤
      evariance (fun z => A.output (populationInput p₀ p₁ (fun _ => ρ) z)) (populationMeasure μ ν) := by
  let : IsProbabilityMeasure (populationMeasure μ ν) := by
    unfold populationMeasure; infer_instance
  have hm₀ := population_moment_finite_of_evariance μ ν p₀ p₁ _ h₀ h₁ measurable_const A hv₀
  have hmρ := population_moment_finite_of_evariance μ ν p₀ p₁ _ h₀ h₁ measurable_const A hvρ
  have h := population_variance_floor μ ν p₀ p₁ h₀ h₁ ρ hρ hρ' A hm₀ hmρ hb₀ hbρ
  rw [← ofReal_variance (population_memLp_of_moment μ ν p₀ p₁ _ h₀ h₁ measurable_const A hmρ)]
  exact ENNReal.ofReal_le_ofReal h

theorem population_moment_bound_of_evariance {D R : Type}
    [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (hq : Measurable q) (A : StoppedProcedure R ℝ)
    (ρ V : ℝ) (hρ : 0 < ρ) (hρ' : ρ ≤ 1/4) (hV : 2*ρ/3 ≤ V)
    (hqρ : (∫ d, (q d : ℝ) ∂μ) ≤ ρ)
    (hb : |populationMean μ ν p₀ p₁ q A - (∫ d, (q d : ℝ) ∂μ)| ≤ ρ/64)
    (hv : evariance (fun z => A.output (populationInput p₀ p₁ q z))
      (populationMeasure μ ν) ≤ ENNReal.ofReal V) :
    populationSecondMoment μ ν p₀ p₁ q A ≤ ENNReal.ofReal (3*V/2) := by
  have hV₀ : 0 ≤ V := by linarith
  have hfin := population_moment_finite_of_evariance μ ν p₀ p₁ q h₀ h₁ hq A
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hv)
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hv
  rw [ENNReal.toReal_ofReal hV₀] at hreal
  have hm := population_moment_bound_of_variance μ ν p₀ p₁ q h₀ h₁ hq A ρ V hρ hρ' hV
    hfin hqρ hb hreal
  simpa only [ENNReal.ofReal_toReal hfin] using ENNReal.ofReal_le_ofReal hm

end ThresholdHC.CriticalEntropy
