import ThresholdHC.EntropyTailLower.FractionalPrior

/-! Good gaps for arbitrary probability measures, including atoms. Global
rarity is tested with fractional event priors; no prescribed-mass subset or
atomlessness premise is needed. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThresholdHC.EntropyTailLower
open ThresholdHC.CriticalEntropy

theorem population_good_gaps_general {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (ρ : unitInterval) (hρ : 0 < (ρ:ℝ)) (hρ' : (ρ:ℝ) ≤ 1/4)
    (m : ℝ) (hm : 2*(ρ:ℝ)/3 ≤ m) (A : StoppedProcedure R ℝ)
    (hguar : CappedPopulationGuarantee μ ν p₀ p₁ A (ρ:ℝ) m) :
    ∃ G : Set D, MeasurableSet G ∧ μ.real Gᶜ ≤ 70*m ∧
      ∀ d ∈ G, PopulationGoodGap ν p₀ p₁ A (ρ:ℝ) m d := by
  have hmpos : 0 < m := by linarith
  have hc₀ : CappedPrior μ (ρ:ℝ) (fun _ => 0) :=
    cappedPrior_const μ (ρ:ℝ) 0 (by norm_num) (by simpa using hρ.le)
  have hcρ : CappedPrior μ (ρ:ℝ) (fun _ => ρ) :=
    cappedPrior_const μ (ρ:ℝ) ρ (by linarith) le_rfl
  have hm₀ : populationSecondMoment μ ν p₀ p₁ (fun _ => 0) A ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hguar.moment _ hc₀)
  have hmρ : populationSecondMoment μ ν p₀ p₁ (fun _ => ρ) A ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hguar.moment _ hcρ)
  obtain ⟨hM₀,hM₁,hMa⟩ := conditional_moment_pair_integrable μ ν p₀ p₁ h₀ h₁ ρ hρ A hm₀ hmρ
  obtain ⟨hFa,hF₀,hF₁⟩ := population_conditional_finiteness μ ν p₀ p₁ h₀ h₁ ρ hρ A
    hm₀ hmρ (hguar.work _ hc₀) (hguar.work _ hcρ)
  let M₀ : D → ℝ := fun d => (conditionalSecondMoment ν (p₀ d) A).toReal
  let M₁ : D → ℝ := fun d => (conditionalSecondMoment ν (p₁ d) A).toReal
  let f : D → ℝ := fun d => conditionalMean ν (p₁ d) A-conditionalMean ν (p₀ d) A
  have hMm₀ : Measurable M₀ := ((measurable_conditionalSecondMoment ν A).comp h₀).ennreal_toReal
  have hMm₁ : Measurable M₁ := ((measurable_conditionalSecondMoment ν A).comp h₁).ennreal_toReal
  have hfm : Measurable f := ((measurable_conditionalMean ν A).comp h₁).sub
    ((measurable_conditionalMean ν A).comp h₀)
  have hfi : Integrable f μ := hF₁.sub hF₀
  have hreal (q : D → unitInterval) (hq : CappedPrior μ (ρ:ℝ) q) :
      (populationSecondMoment μ ν p₀ p₁ q A).toReal ≤ m := by
    simpa only [ENNReal.toReal_ofReal hmpos.le] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top (hguar.moment q hq)
  let B₀ : Set D := {d | (1:ℝ)/64 ≤ M₀ d}
  let B₁ : Set D := {d | 2*m/(ρ:ℝ) ≤ M₁ d-M₀ d}
  let Bf : Set D := {d | f d ≤ (3:ℝ)/4}
  have hB₀ : MeasurableSet B₀ := measurableSet_le measurable_const hMm₀
  have hB₁ : MeasurableSet B₁ := measurableSet_le measurable_const (hMm₁.sub hMm₀)
  have hBf : MeasurableSet Bf := measurableSet_le hfm measurable_const
  have hb₀ : μ.real B₀ ≤ 64*m := by
    have he := population_second_moment_real_formula μ ν p₀ p₁ h₀ h₁ ρ hρ A hm₀ hmρ
      (fun _ => 0) measurable_const
    norm_num at he
    have hmark := mul_meas_ge_le_integral_of_nonneg
      (Filter.Eventually.of_forall (fun d => ENNReal.toReal_nonneg)) hM₀ ((1:ℝ)/64)
    rw [← he] at hmark
    change (1:ℝ)/64*μ.real B₀ ≤ _ at hmark
    linarith [hreal (fun _ => 0) hc₀]
  have hb₁ : μ.real B₁ < 2*(ρ:ℝ) := by
    by_contra hn
    obtain ⟨c,hc,hch,he⟩ := exists_fractional_mass μ B₁ (ρ:ℝ) hρ (not_lt.mp hn)
    have hcp := cappedPrior_event μ (ρ:ℝ) B₁ hB₁ c hch he.le
    have hmom := population_eventPrior_moment μ ν p₀ p₁ h₀ h₁ ρ hρ A hm₀ hmρ B₁ hB₁ c
    have hi : (2*m/(ρ:ℝ))*μ.real B₁ ≤ ∫ d in B₁, M₁ d-M₀ d ∂μ := by
      calc
        _ = ∫ _ in B₁, (2*m/(ρ:ℝ)) ∂μ := by simp [mul_comm]
        _ ≤ _ := setIntegral_mono_on (integrable_const _) (hM₁.sub hM₀).integrableOn hB₁
          (fun d hd => hd)
    have hscale := mul_le_mul_of_nonneg_left hi hc.le
    have heq : (c:ℝ)*((2*m/(ρ:ℝ))*μ.real B₁) = 2*m := by
      calc
        _ = (2*m/(ρ:ℝ))*((c:ℝ)*μ.real B₁) := by ring
        _ = 2*m := by rw [he]; exact div_mul_cancel₀ _ hρ.ne'
    rw [heq] at hscale
    change (populationSecondMoment μ ν p₀ p₁ (eventPrior B₁ c) A).toReal =
      (populationSecondMoment μ ν p₀ p₁ (fun _ => 0) A).toReal+
        (c:ℝ)*(∫ d in B₁, M₁ d-M₀ d ∂μ) at hmom
    linarith [hreal _ hcp,ENNReal.toReal_nonneg
      (a := populationSecondMoment μ ν p₀ p₁ (fun _ => 0) A)]
  have hbf : μ.real Bf < 2*(ρ:ℝ) := by
    by_contra hn
    obtain ⟨c,hc,hch,he⟩ := exists_fractional_mass μ Bf (ρ:ℝ) hρ (not_lt.mp hn)
    have hcp := cappedPrior_event μ (ρ:ℝ) Bf hBf c hch he.le
    have hbe := hguar.bias _ hcp
    have hb0 := hguar.bias _ hc₀
    have hmean := population_eventPrior_mean μ ν p₀ p₁ h₀ h₁ ρ hρ A hm₀ hmρ Bf hBf c
    rw [eventPrior_integral μ Bf hBf c,he] at hbe
    norm_num at hb0
    have hi : (∫ d in Bf, f d ∂μ) ≤ (3/4)*μ.real Bf := by
      calc
        _ ≤ ∫ _ in Bf, (3/4:ℝ) ∂μ :=
          setIntegral_mono_on hfi.integrableOn (integrable_const _) hBf (fun d hd => hd)
        _ = _ := by simp [mul_comm]
    have hscale := mul_le_mul_of_nonneg_left hi hc.le
    have heq : (c:ℝ)*((3/4)*μ.real Bf) = (3/4)*(ρ:ℝ) := by
      calc
        _ = (3/4)*((c:ℝ)*μ.real Bf) := by ring
        _ = _ := by rw [he]
    rw [heq] at hscale
    change populationMean μ ν p₀ p₁ (eventPrior Bf c) A =
      populationMean μ ν p₀ p₁ (fun _ => 0) A+(c:ℝ)*(∫ d in Bf, f d ∂μ) at hmean
    linarith [(abs_le.mp hb0).2,(abs_le.mp hbe).1]
  let S : Set D := {d | conditionalSecondMoment ν (p₀ d) A ≠ ∞ ∧
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
    have hz : μ Sᶜ = 0 := by rw [ae_iff] at hSa; exact hSa
    simp [measureReal_def,hz]
  let G : Set D := S \ ((B₀ ∪ B₁) ∪ Bf)
  refine ⟨G,hSm.diff ((hB₀.union hB₁).union hBf),?_,?_⟩
  · have hset : Gᶜ ⊆ Sᶜ ∪ ((B₀ ∪ B₁) ∪ Bf) := by
      intro d hd
      simp only [G,mem_compl_iff,mem_sdiff,mem_union] at *
      tauto
    have hmeasure := (measureReal_mono (μ := μ) hset).trans (measureReal_union_le _ _)
    have hbad := measureReal_union_le (B₀ ∪ B₁) Bf (μ := μ)
    have hbad' := measureReal_union_le B₀ B₁ (μ := μ)
    rw [hSn] at hmeasure
    linarith
  · intro d hd
    have hsd := hd.1
    have hM0 : M₀ d < (1:ℝ)/64 := by
      by_contra hn
      exact hd.2 (Or.inl (Or.inl (not_lt.mp hn)))
    have hMdiff : M₁ d-M₀ d < 2*m/(ρ:ℝ) := by
      by_contra hn
      exact hd.2 (Or.inl (Or.inr (not_lt.mp hn)))
    have hf : (3:ℝ)/4 < f d := by
      by_contra hn
      exact hd.2 (Or.inr (not_lt.mp hn))
    have hmeanSq := conditionalMean_sq_le_moment ν (p₀ d) A hsd.1
    have hmean : |conditionalMean ν (p₀ d) A| ≤ (1:ℝ)/8 := by
      rw [abs_le]
      change (conditionalMean ν (p₀ d) A)^2 ≤ M₀ d at hmeanSq
      constructor <;> nlinarith
    refine ⟨hsd.1,hsd.2.1,hsd.2.2.1,hsd.2.2.2,hmean,?_,hM0.le,?_⟩
    · change (3:ℝ)/4 < conditionalMean ν (p₁ d) A-conditionalMean ν (p₀ d) A at hf
      linarith [(abs_le.mp hmean).1]
    · change M₁ d ≤ (1:ℝ)/64+2*m/(ρ:ℝ)
      linarith

end ThresholdHC.EntropyTailLower
