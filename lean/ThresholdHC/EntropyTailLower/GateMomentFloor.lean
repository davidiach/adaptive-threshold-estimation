import ThresholdHC.EntropyTailLower.GatedGoodGaps
import ThresholdHC.CriticalEntropy.PopulationVariance

/-! A moment floor for the actual gated average absorbs the additive rarity
term in the good-gap bound. The hypotheses retain the small-work regime. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal
namespace ThresholdHC.EntropyTailLower
open ThresholdHC.Tier2 ThresholdHC.CriticalEntropy ThresholdHC.BlindUpper

theorem population_moment_floor_of_mean_gap {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (A : StoppedProcedure R ℝ) (ρ : unitInterval) (hρ : 0 < (ρ:ℝ)) (hρ4 : (ρ:ℝ) ≤ 1/4)
    (m : ℝ) (hm : 0 ≤ m)
    (hmoment : ∀ q, CappedPrior μ (ρ:ℝ) q → populationSecondMoment μ ν p₀ p₁ q A ≤ ENNReal.ofReal m)
    (hwork : ∀ q, CappedPrior μ (ρ:ℝ) q → populationExpectedWork μ ν p₀ p₁ q A ≠ ∞)
    (hgap : (27:ℝ)/32 ≤ ∫ d, conditionalMean ν (p₁ d) A-conditionalMean ν (p₀ d) A ∂μ) :
    (ρ:ℝ)/2 ≤ m := by
  let : IsProbabilityMeasure (populationMeasure μ ν) := by unfold populationMeasure; infer_instance
  have hc₀ := cappedPrior_const μ (ρ:ℝ) 0 (by norm_num) (by simpa using hρ.le)
  have hcρ := cappedPrior_const μ (ρ:ℝ) ρ (by linarith) le_rfl
  have hm₀ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hmoment _ hc₀)
  have hmρ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hmoment _ hcρ)
  have hf := population_conditional_finiteness μ ν p₀ p₁ h₀ h₁ ρ hρ A
    hm₀ hmρ (hwork _ hc₀) (hwork _ hcρ)
  have hm₁ : populationSecondMoment μ ν p₀ p₁ (fun _ => 1) A ≠ ∞ :=
    population_finite_all μ ν p₀ p₁ h₀ h₁ ρ hρ _
      (ENNReal.measurable_ofReal.comp (A.measurable_output.pow_const 2)) hm₀ hmρ _ measurable_const
  have hmean₀ := population_mean_formula μ ν p₀ p₁ (fun _ => 0) h₀ h₁ measurable_const A hm₀
  have hmean₁ := population_mean_formula μ ν p₀ p₁ (fun _ => 1) h₀ h₁ measurable_const A hm₁
  norm_num at hmean₀ hmean₁
  have he : populationMean μ ν p₀ p₁ (fun _ => 1) A-populationMean μ ν p₀ p₁ (fun _ => 0) A =
      ∫ d, conditionalMean ν (p₁ d) A-conditionalMean ν (p₀ d) A ∂μ := by
    rw [hmean₀,hmean₁]
    exact (integral_sub hf.2.2 hf.2.1).symm
  have hv := population_variance_mixture_lower μ ν p₀ p₁ h₀ h₁ ρ A hm₀ hm₁
  rw [he] at hv
  have hs : ((27:ℝ)/32)^2 ≤ (∫ d, conditionalMean ν (p₁ d) A-conditionalMean ν (p₀ d) A ∂μ)^2 :=
    by nlinarith only [hgap]
  have hnum : (ρ:ℝ)/2 ≤ (ρ:ℝ)*(1-(ρ:ℝ))*((27:ℝ)/32)^2 := by
    nlinarith [mul_nonneg hρ.le (show 0 ≤ 1/4-(ρ:ℝ) by linarith)]
  have hl := hnum.trans ((mul_le_mul_of_nonneg_left hs
    (mul_nonneg hρ.le (sub_nonneg.mpr ρ.property.2))).trans hv)
  have hL := population_memLp_of_moment μ ν p₀ p₁ (fun _ => ρ) h₀ h₁ measurable_const A hmρ
  have hvM := variance_le_expectation_sq hL.aestronglyMeasurable
  simp only [Pi.pow_apply] at hvM
  rw [population_second_moment_toReal μ ν p₀ p₁ (fun _ => ρ) h₀ h₁ measurable_const A hmρ] at hvM
  have hMb := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hmoment _ hcρ)
  rw [ENNReal.toReal_ofReal hm] at hMb
  exact hl.trans (hvM.trans hMb)

theorem population_gate_moment_floor {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (A : StoppedProcedure R ℝ) (ρ : unitInterval) (hρ : 0 < (ρ:ℝ)) (hρ4 : (ρ:ℝ) ≤ 1/4)
    (m : ℝ) (hm : 0 < m) (hguar : CappedPopulationGuarantee μ ν p₀ p₁ A (ρ:ℝ) m)
    (a : ℝ) (ha : 0 < a) (ha4 : a ≤ 1/4)
    (hclose : ∀ᵐ d ∂μ, |(p₀ d:ℝ)-1/2| ≤ a ∧ (p₀ d:ℝ)+(p₁ d:ℝ) = 1)
    (hsmall : 64*exp 48*a^2*m*(populationExpectedWork μ ν p₀ p₁ (fun _ => 0) A).toReal ≤ 1/64) :
    (ρ:ℝ)/2 ≤ (1+exp 12)*fairActivation ν A a*m := by
  let β := fairActivation ν A a
  let Z := gateAverage A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊ β
  let η := Measure.pi (fun _ : Fin ((gateBatchCount β-1)+1) => ν)
  let mZ := (1+exp 12)*β*m
  have hβ : 0 < β := fair_activation_positive_of_small_work μ ν p₀ p₁ h₀ h₁ A ρ hρ hρ4 m hm.le hguar
    a ha ha4 hclose (hsmall.trans (by norm_num))
  have hboth : ∀ᵐ d ∂μ, |(p₀ d:ℝ)-1/2| ≤ a ∧ |(p₁ d:ℝ)-1/2| ≤ a := by
    filter_upwards [hclose] with d hd
    refine ⟨hd.1,?_⟩
    have he : (p₁ d:ℝ)-1/2 = -((p₀ d:ℝ)-1/2) := by linarith [hd.2]
    simpa only [he,abs_neg] using hd.1
  have hnew := population_gateAverage_uniform μ ν p₀ p₁ h₀ h₁ A ρ hρ hρ4 m hguar a ha ha4 hboth hβ
  have hc₀ := cappedPrior_const μ (ρ:ℝ) 0 (by norm_num) (by simpa using hρ.le)
  have hcρ := cappedPrior_const μ (ρ:ℝ) ρ (by linarith) le_rfl
  have hm₀ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hguar.moment _ hc₀)
  have hm₁ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hguar.moment _ hcρ)
  have hf := population_conditional_finiteness μ ν p₀ p₁ h₀ h₁ ρ hρ A
    hm₀ hm₁ (hguar.work _ hc₀) (hguar.work _ hcρ)
  have hmoment := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hguar.moment _ hc₀)
  rw [ENNReal.toReal_ofReal hm.le] at hmoment
  have hrel : ∀ᵐ d ∂μ, conditionalMean ν (p₁ d) A-conditionalMean ν (p₀ d) A ≤
      (conditionalMean η (p₁ d) Z-conditionalMean η (p₀ d) Z)+1/8 := by
    filter_upwards [hf.1,hclose,hboth] with d hd hp hb
    have he₀ := gateAverage_mean_decomposition ν (p₀ d) A hd.2.2.1
      ((conditionalSecondMoment_finite_iff _ _ _).mpr hd.1) ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊ β
    have he₁ := gateAverage_mean_decomposition ν (p₁ d) A hd.2.2.2
      ((conditionalSecondMoment_finite_iff _ _ _).mpr hd.2.1) ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊ β
    have hearly := population_early_mean_difference μ ν p₀ p₁ h₀ h₁ A a ha ha4
      (hclose.mono (fun _ h => h.1)) hm₀ (hguar.work _ hc₀) (p₁ d) (p₀ d) hb.2 (by linarith [hp.2])
    have hscale := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hmoment (by positivity : 0 ≤ 64*exp 48*a^2))
      (ENNReal.toReal_nonneg (a := populationExpectedWork μ ν p₀ p₁ (fun _ => 0) A))
    have hs := hearly.trans (hscale.trans hsmall)
    have hmearly : conditionalMean ν (p₁ d) (earlyProcedure A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊)-
        conditionalMean ν (p₀ d) (earlyProcedure A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊) ≤ 1/8 := by nlinarith only [hs]
    change conditionalMean ν (p₀ d) _+conditionalMean η (p₀ d) Z = _ at he₀
    change conditionalMean ν (p₁ d) _+conditionalMean η (p₁ d) Z = _ at he₁
    linarith
  have hMz₀ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hnew _ hc₀).1
  have hMzρ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hnew _ hcρ).1
  have hfZ := population_conditional_finiteness μ η p₀ p₁ h₀ h₁ ρ hρ Z
    hMz₀ hMzρ (hnew _ hc₀).2 (hnew _ hcρ).2
  have hi := integral_mono_ae (hf.2.2.sub hf.2.1)
    ((hfZ.2.2.sub hfZ.2.1).add (integrable_const (1/8:ℝ))) hrel
  have hadd := integral_add (hfZ.2.2.sub hfZ.2.1) (integrable_const (1/8:ℝ))
  simp only [Pi.sub_apply,Pi.add_apply] at hi hadd
  rw [hadd] at hi
  simp only [integral_const,probReal_univ,one_smul] at hi
  have hgapA := capped_guarantee_integrated_mean_separation μ ν p₀ p₁ h₀ h₁ A ρ hρ hρ4 m hguar
  have hgapZ : (27:ℝ)/32 ≤ ∫ d, conditionalMean η (p₁ d) Z-conditionalMean η (p₀ d) Z ∂μ := by linarith
  exact population_moment_floor_of_mean_gap μ η p₀ p₁ h₀ h₁ Z ρ hρ hρ4 mZ
    (by dsimp [mZ]; positivity) (fun q hq => (hnew q hq).1) (fun q hq => (hnew q hq).2) hgapZ

theorem population_gate_good_gaps_mass {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (A : StoppedProcedure R ℝ) (ρ : unitInterval) (hρ : 0 < (ρ:ℝ)) (hρ4 : (ρ:ℝ) ≤ 1/4)
    (m : ℝ) (hm : 0 < m) (hguar : CappedPopulationGuarantee μ ν p₀ p₁ A (ρ:ℝ) m)
    (a : ℝ) (ha : 0 < a) (ha4 : a ≤ 1/4)
    (hclose : ∀ᵐ d ∂μ, |(p₀ d:ℝ)-1/2| ≤ a ∧ (p₀ d:ℝ)+(p₁ d:ℝ) = 1)
    (hsmall : 64*exp 48*a^2*m*(populationExpectedWork μ ν p₀ p₁ (fun _ => 0) A).toReal ≤ 1/64) :
    let β := fairActivation ν A a
    let Z := gateAverage A ⌈(a^2)⁻¹⌉₊ ⌈a⁻¹⌉₊ β
    let η := Measure.pi (fun _ : Fin ((gateBatchCount β-1)+1) => ν)
    let mZ := (1+exp 12)*β*m
    0 < β ∧ ∃ G : Set D, MeasurableSet G ∧ μ.real Gᶜ ≤ 72*mZ ∧
      ∀ d ∈ G, PopulationGoodGap η p₀ p₁ Z (ρ:ℝ) mZ d := by
  obtain ⟨hβ,G,hG,hbad,hgood⟩ := population_gate_good_gaps μ ν p₀ p₁ h₀ h₁ A ρ hρ hρ4 m hm hguar
    a ha ha4 hclose hsmall
  have hfloor := population_gate_moment_floor μ ν p₀ p₁ h₀ h₁ A ρ hρ hρ4 m hm hguar
    a ha ha4 hclose hsmall
  refine ⟨hβ,G,hG,?_,hgood⟩
  linarith

end ThresholdHC.EntropyTailLower
