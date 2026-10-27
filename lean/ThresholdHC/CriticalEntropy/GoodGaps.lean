import ThresholdHC.CriticalEntropy.HalfPrior
import ThresholdHC.CriticalEntropy.GapSelection

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThresholdHC.CriticalEntropy

/-- Quantitative good-gap selection from uniform guarantees over the capped
global population class. No conditional mean, moment, or work bound is an
assumption. The same observable procedure and seed law serve every population. -/
theorem population_good_gaps {R : Type} [MeasurableSpace R]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : ℝ → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (a b : ℝ) (hab : a ≤ b) (hsupport : μ (Ioc a b)ᶜ = 0)
    (ρ : unitInterval) (hρ : 0 < (ρ : ℝ)) (hρ' : (ρ : ℝ) ≤ 1/4)
    (m : ℝ) (hm : 2*(ρ : ℝ)/3 ≤ m) (A : StoppedProcedure R ℝ)
    (hguar : CappedPopulationGuarantee μ ν p₀ p₁ A (ρ : ℝ) m) :
    ∃ G : Set ℝ, MeasurableSet G ∧ G ⊆ Ioc a b ∧ μ.real Gᶜ ≤ 70*m ∧
      ∀ d ∈ G, PopulationGoodGap ν p₀ p₁ A (ρ : ℝ) m d := by
  have hmpos : 0 < m := by linarith
  have hc₀ : CappedPrior μ (ρ : ℝ) (fun _ => 0) :=
    cappedPrior_const μ (ρ : ℝ) 0 (by norm_num) (by simpa using hρ.le)
  have hcρ : CappedPrior μ (ρ : ℝ) (fun _ => ρ) :=
    cappedPrior_const μ (ρ : ℝ) ρ (by linarith) le_rfl
  have hm₀ : populationSecondMoment μ ν p₀ p₁ (fun _ => 0) A ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hguar.moment _ hc₀)
  have hmρ : populationSecondMoment μ ν p₀ p₁ (fun _ => ρ) A ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hguar.moment _ hcρ)
  obtain ⟨hM₀,hM₁,hMa⟩ := conditional_moment_pair_integrable μ ν p₀ p₁ h₀ h₁ ρ hρ A hm₀ hmρ
  obtain ⟨hFa,hF₀,hF₁⟩ := population_conditional_finiteness μ ν p₀ p₁ h₀ h₁ ρ hρ A
    hm₀ hmρ (hguar.work _ hc₀) (hguar.work _ hcρ)
  let M₀ : ℝ → ℝ := fun d => (conditionalSecondMoment ν (p₀ d) A).toReal
  let M₁ : ℝ → ℝ := fun d => (conditionalSecondMoment ν (p₁ d) A).toReal
  let f : ℝ → ℝ := fun d => conditionalMean ν (p₁ d) A-conditionalMean ν (p₀ d) A
  have hMm₀ : Measurable M₀ := ((measurable_conditionalSecondMoment ν A).comp h₀).ennreal_toReal
  have hMm₁ : Measurable M₁ := ((measurable_conditionalSecondMoment ν A).comp h₁).ennreal_toReal
  have hfm : Measurable f := ((measurable_conditionalMean ν A).comp h₁).sub
    ((measurable_conditionalMean ν A).comp h₀)
  have hfi : Integrable f μ := hF₁.sub hF₀
  have hreal (q : ℝ → unitInterval) (hq : CappedPrior μ (ρ : ℝ) q) :
      (populationSecondMoment μ ν p₀ p₁ q A).toReal ≤ m := by
    simpa only [ENNReal.toReal_ofReal hmpos.le] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top (hguar.moment q hq)
  let B₀ : Set ℝ := {d | (1 : ℝ)/64 ≤ M₀ d}
  let B₁ : Set ℝ := Ioc a b ∩ {d | 2*m/(ρ : ℝ) ≤ M₁ d-M₀ d}
  let Bf : Set ℝ := Ioc a b ∩ {d | f d ≤ (3 : ℝ)/4}
  have hB₀ : MeasurableSet B₀ := measurableSet_le measurable_const hMm₀
  have hB₁ : MeasurableSet B₁ := measurableSet_Ioc.inter
    (measurableSet_le measurable_const (hMm₁.sub hMm₀))
  have hBf : MeasurableSet Bf := measurableSet_Ioc.inter (measurableSet_le hfm measurable_const)
  have hb₀ : μ.real B₀ ≤ 64*m := by
    have he := population_second_moment_real_formula μ ν p₀ p₁ h₀ h₁ ρ hρ A hm₀ hmρ
      (fun _ => 0) measurable_const
    norm_num at he
    have hmark := mul_meas_ge_le_integral_of_nonneg
      (Filter.Eventually.of_forall (fun d => ENNReal.toReal_nonneg)) hM₀ ((1 : ℝ)/64)
    rw [← he] at hmark
    change (1 : ℝ)/64 * μ.real B₀ ≤ _ at hmark
    linarith [hreal (fun _ => 0) hc₀]
  have hb₁ : μ.real B₁ < 2*(ρ : ℝ) := by
    apply bad_set_mass_lt_of_integral_upper (Ioc a b) measurableSet_Ioc
      a b (2*(ρ : ℝ)) (2*m/(ρ : ℝ)) (2*m) hab subset_rfl (by positivity)
      (fun d => M₁ d-M₀ d) (hMm₁.sub hMm₀) (hM₁.sub hM₀)
    · have he : (2*m/(ρ : ℝ))*(2*(ρ : ℝ)) = 4*m := by field_simp; ring
      rw [he]; linarith
    · intro E hE _ hEr
      have hcE := cappedPrior_half μ (ρ : ℝ) E hE (le_of_eq hEr)
      have he := population_halfPrior_moment μ ν p₀ p₁ h₀ h₁ ρ hρ A hm₀ hmρ E hE
      change (populationSecondMoment μ ν p₀ p₁ (halfPrior E) A).toReal =
        (populationSecondMoment μ ν p₀ p₁ (fun _ => 0) A).toReal +
        (1/2)*(∫ d in E, M₁ d-M₀ d ∂μ) at he
      linarith [hreal (halfPrior E) hcE,
        ENNReal.toReal_nonneg (a := populationSecondMoment μ ν p₀ p₁ (fun _ => 0) A)]
  have hbf : μ.real Bf < 2*(ρ : ℝ) := by
    apply bad_set_mass_lt_of_integral_lower (Ioc a b) measurableSet_Ioc
      a b (2*(ρ : ℝ)) (3/4) (31*(ρ : ℝ)/16) hab subset_rfl (by positivity)
      f hfm hfi (by linarith)
    intro E hE _ hEr
    have hcE := cappedPrior_half μ (ρ : ℝ) E hE (le_of_eq hEr)
    have hbe := hguar.bias (halfPrior E) hcE
    have hb0 := hguar.bias (fun _ => 0) hc₀
    have he := population_halfPrior_mean μ ν p₀ p₁ h₀ h₁ ρ hρ A hm₀ hmρ E hE
    change populationMean μ ν p₀ p₁ (halfPrior E) A =
      populationMean μ ν p₀ p₁ (fun _ => 0) A+(1/2)*(∫ d in E, f d ∂μ) at he
    rw [halfPrior_integral μ E hE,hEr] at hbe
    norm_num at hb0 hbe
    linarith [(abs_le.mp hb0).2,(abs_le.mp hbe).1]
  let S : Set ℝ := {d | conditionalSecondMoment ν (p₀ d) A ≠ ∞ ∧
    conditionalSecondMoment ν (p₁ d) A ≠ ∞ ∧ expectedStoppedProcedureWork ν (p₀ d) A ≠ ∞ ∧
    expectedStoppedProcedureWork ν (p₁ d) A ≠ ∞}
  have hSm : MeasurableSet S :=
    (measurableSet_eq_fun ((measurable_conditionalSecondMoment ν A).comp h₀) measurable_const).compl.inter
      ((measurableSet_eq_fun ((measurable_conditionalSecondMoment ν A).comp h₁) measurable_const).compl.inter
        ((measurableSet_eq_fun ((measurable_conditionalWork ν A).comp h₀) measurable_const).compl.inter
          (measurableSet_eq_fun ((measurable_conditionalWork ν A).comp h₁) measurable_const).compl))
  have hSa : ∀ᵐ d ∂μ, d ∈ S := by
    filter_upwards [hMa,hFa] with d hmd hfd
    exact ⟨hmd.1,hmd.2,hfd.2.2.1,hfd.2.2.2⟩
  have hSn : μ.real Sᶜ = 0 := by
    have hz : μ Sᶜ = 0 := by
      rw [ae_iff] at hSa
      exact hSa
    simp [measureReal_def,hz]
  let G : Set ℝ := (Ioc a b ∩ S) \ ((B₀ ∪ B₁) ∪ Bf)
  refine ⟨G,(measurableSet_Ioc.inter hSm).diff ((hB₀.union hB₁).union hBf),
    fun d hd => hd.1.1,?_,?_⟩
  · have hset : Gᶜ ⊆ (Ioc a b)ᶜ ∪ Sᶜ ∪ ((B₀ ∪ B₁) ∪ Bf) := by
      intro d hd
      simp only [G,mem_compl_iff,mem_sdiff,mem_inter_iff,mem_union] at *
      tauto
    have hsreal : μ.real (Ioc a b)ᶜ = 0 := by simp [measureReal_def,hsupport]
    have hmeasure := (measureReal_mono (μ := μ) hset).trans (measureReal_union_le _ _)
    have hnull := measureReal_union_le (Ioc a b)ᶜ Sᶜ (μ := μ)
    have hbad := measureReal_union_le (B₀ ∪ B₁) Bf (μ := μ)
    have hbad' := measureReal_union_le B₀ B₁ (μ := μ)
    rw [hsreal,hSn] at hnull
    linarith
  · intro d hd
    have hsd := hd.1.2
    have hM0 : M₀ d < (1 : ℝ)/64 := by
      by_contra hn
      exact hd.2 (Or.inl (Or.inl (not_lt.mp hn)))
    have hMdiff : M₁ d-M₀ d < 2*m/(ρ : ℝ) := by
      by_contra hn
      exact hd.2 (Or.inl (Or.inr ⟨hd.1.1,not_lt.mp hn⟩))
    have hf : (3 : ℝ)/4 < f d := by
      by_contra hn
      exact hd.2 (Or.inr ⟨hd.1.1,not_lt.mp hn⟩)
    have hmeanSq := conditionalMean_sq_le_moment ν (p₀ d) A hsd.1
    have hmean : |conditionalMean ν (p₀ d) A| ≤ (1 : ℝ)/8 := by
      rw [abs_le]
      change M₀ d < (1 : ℝ)/64 at hM0
      change (conditionalMean ν (p₀ d) A)^2 ≤ M₀ d at hmeanSq
      constructor <;> nlinarith
    refine ⟨hsd.1,hsd.2.1,hsd.2.2.1,hsd.2.2.2,hmean,?_,hM0.le,?_⟩
    · change (3 : ℝ)/4 < conditionalMean ν (p₁ d) A-conditionalMean ν (p₀ d) A at hf
      linarith [(abs_le.mp hmean).1]
    · change M₁ d ≤ (1 : ℝ)/64+2*m/(ρ : ℝ)
      linarith

end ThresholdHC.CriticalEntropy
