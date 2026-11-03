import ThresholdHC.EntropyTailLower.EarlyMean
import ThresholdHC.EntropyTailLower.PopulationGateAverage

/-! Good gaps for the actual finite-average gated estimator. Mean separation
comes from the original capped guarantee and the early-output estimate;
no original bias guarantee is assumed for the transformed estimator.
The exceptional mass is bounded by 64 times its moment bound plus 4 rho. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal
namespace ThresholdHC.EntropyTailLower
open ThresholdHC.Tier2 ThresholdHC.CriticalEntropy ThresholdHC.BlindUpper

theorem population_good_gaps_of_mean_tail {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (ρ : unitInterval) (hρ : 0 < (ρ:ℝ)) (hρ' : (ρ:ℝ) ≤ 1/4)
    (m : ℝ) (hmpos : 0 < m) (A : StoppedProcedure R ℝ)
    (hmoment : ∀ q, CappedPrior μ (ρ:ℝ) q → populationSecondMoment μ ν p₀ p₁ q A ≤ ENNReal.ofReal m)
    (hwork : ∀ q, CappedPrior μ (ρ:ℝ) q → populationExpectedWork μ ν p₀ p₁ q A ≠ ∞)
    (hmean : μ.real {d | conditionalMean ν (p₁ d) A-conditionalMean ν (p₀ d) A ≤ 3/4} < 2*(ρ:ℝ)) :
    ∃ G : Set D, MeasurableSet G ∧ μ.real Gᶜ ≤ 64*m+4*(ρ:ℝ) ∧
      ∀ d ∈ G, PopulationGoodGap ν p₀ p₁ A (ρ:ℝ) m d := by
  have hc₀ : CappedPrior μ (ρ:ℝ) (fun _ => 0) :=
    cappedPrior_const μ (ρ:ℝ) 0 (by norm_num) (by simpa using hρ.le)
  have hcρ : CappedPrior μ (ρ:ℝ) (fun _ => ρ) :=
    cappedPrior_const μ (ρ:ℝ) ρ (by linarith) le_rfl
  have hm₀ : populationSecondMoment μ ν p₀ p₁ (fun _ => 0) A ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hmoment _ hc₀)
  have hmρ : populationSecondMoment μ ν p₀ p₁ (fun _ => ρ) A ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hmoment _ hcρ)
  obtain ⟨hM₀,hM₁,hMa⟩ := conditional_moment_pair_integrable μ ν p₀ p₁ h₀ h₁ ρ hρ A hm₀ hmρ
  obtain ⟨hFa,hF₀,hF₁⟩ := population_conditional_finiteness μ ν p₀ p₁ h₀ h₁ ρ hρ A
    hm₀ hmρ (hwork _ hc₀) (hwork _ hcρ)
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
      ENNReal.toReal_mono ENNReal.ofReal_ne_top (hmoment q hq)
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
  have hbf : μ.real Bf < 2*(ρ:ℝ) := hmean
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

theorem capped_guarantee_bad_mean_mass {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (ρ : unitInterval) (hρ : 0 < (ρ:ℝ)) (hρ4 : (ρ:ℝ) ≤ 1/4)
    (m : ℝ) (A : StoppedProcedure R ℝ)
    (hguar : CappedPopulationGuarantee μ ν p₀ p₁ A (ρ:ℝ) m)
    (t : ℝ) (ht : t < 31/32) :
    μ.real {d | conditionalMean ν (p₁ d) A-conditionalMean ν (p₀ d) A ≤ t} < 2*(ρ:ℝ) := by
  have hc₀ := cappedPrior_const μ (ρ:ℝ) 0 (by norm_num) (by simpa using hρ.le)
  have hcρ := cappedPrior_const μ (ρ:ℝ) ρ (by linarith) le_rfl
  have hm₀ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hguar.moment _ hc₀)
  have hmρ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hguar.moment _ hcρ)
  have hf := population_conditional_finiteness μ ν p₀ p₁ h₀ h₁ ρ hρ A
    hm₀ hmρ (hguar.work _ hc₀) (hguar.work _ hcρ)
  let f := fun d => conditionalMean ν (p₁ d) A-conditionalMean ν (p₀ d) A
  have hfi : Integrable f μ := hf.2.2.sub hf.2.1
  have hfm : Measurable f := ((measurable_conditionalMean ν A).comp h₁).sub
    ((measurable_conditionalMean ν A).comp h₀)
  let Bf := {d | f d ≤ t}
  have hBf : MeasurableSet Bf := measurableSet_le hfm measurable_const
  change μ.real Bf < 2*(ρ:ℝ)
  by_contra hn
  obtain ⟨c,hc,hch,he⟩ := exists_fractional_mass μ Bf (ρ:ℝ) hρ (not_lt.mp hn)
  have hcp := cappedPrior_event μ (ρ:ℝ) Bf hBf c hch he.le
  have hbe := hguar.bias _ hcp
  have hb0 := hguar.bias _ hc₀
  have hmean := population_eventPrior_mean μ ν p₀ p₁ h₀ h₁ ρ hρ A hm₀ hmρ Bf hBf c
  rw [eventPrior_integral μ Bf hBf c,he] at hbe
  norm_num at hb0
  have hi : (∫ d in Bf, f d ∂μ) ≤ t*μ.real Bf := by
    calc
      _ ≤ ∫ _ in Bf, t ∂μ :=
        setIntegral_mono_on hfi.integrableOn (integrable_const _) hBf (fun d hd => hd)
      _ = _ := by simp [mul_comm]
  have hscale := mul_le_mul_of_nonneg_left hi hc.le
  have heq : (c:ℝ)*(t*μ.real Bf) = t*(ρ:ℝ) := by
    calc
      _ = t*((c:ℝ)*μ.real Bf) := by ring
      _ = _ := by rw [he]
  rw [heq] at hscale
  change populationMean μ ν p₀ p₁ (eventPrior Bf c) A =
    populationMean μ ν p₀ p₁ (fun _ => 0) A+(c:ℝ)*(∫ d in Bf, f d ∂μ) at hmean
  nlinarith [(abs_le.mp hb0).2,(abs_le.mp hbe).1,mul_pos hρ (sub_pos.mpr ht)]


theorem gateAverage_mean_decomposition {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (p : unitInterval) (A : StoppedProcedure R ℝ)
    (hW : expectedStoppedProcedureWork ν p A ≠ ∞) (hM : conditionalSecondMoment ν p A ≠ ∞)
    (M H : ℕ) (β : ℝ) :
    conditionalMean ν p (earlyProcedure A M H)+
      conditionalMean (Measure.pi (fun _ : Fin ((gateBatchCount β-1)+1) => ν)) p (gateAverage A M H β) =
      conditionalMean ν p A := by
  have he := averageProcedure_mean ν p (gatedProcedure A M H) hW
    (ne_top_of_le_ne_top hM (gatedProcedure_secondMoment_le ν p A M H)) (gateBatchCount β-1)
  change conditionalMean _ _ (gateAverage A M H β) = _ at he
  rw [he]
  exact early_gated_mean_sum ν p A hM M H

theorem population_gate_good_gaps {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
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
    0 < β ∧ ∃ G : Set D, MeasurableSet G ∧ μ.real Gᶜ ≤ 64*mZ+4*(ρ:ℝ) ∧
      ∀ d ∈ G, PopulationGoodGap η p₀ p₁ Z (ρ:ℝ) mZ d := by
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
  have hf := (population_conditional_finiteness μ ν p₀ p₁ h₀ h₁ ρ hρ A
    hm₀ hm₁ (hguar.work _ hc₀) (hguar.work _ hcρ)).1
  have hmoment := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hguar.moment _ hc₀)
  rw [ENNReal.toReal_ofReal hm.le] at hmoment
  let BZ := {d | conditionalMean η (p₁ d) Z-conditionalMean η (p₀ d) Z ≤ 3/4}
  let BA := {d | conditionalMean ν (p₁ d) A-conditionalMean ν (p₀ d) A ≤ 7/8}
  have hsub : BZ ≤ᵐ[μ] BA := by
    filter_upwards [hf,hclose,hboth] with d hd hp hb
    intro hz
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
    change conditionalMean η (p₁ d) Z-conditionalMean η (p₀ d) Z ≤ 3/4 at hz
    change conditionalMean ν (p₁ d) A-conditionalMean ν (p₀ d) A ≤ 7/8
    change conditionalMean ν (p₀ d) _+conditionalMean η (p₀ d) Z = _ at he₀
    change conditionalMean ν (p₁ d) _+conditionalMean η (p₁ d) Z = _ at he₁
    linarith
  have hbad : μ.real BZ < 2*(ρ:ℝ) :=
    (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)).trans_lt
      (capped_guarantee_bad_mean_mass μ ν p₀ p₁ h₀ h₁ ρ hρ hρ4 m A hguar (7/8) (by norm_num))
  change 0 < β ∧ _
  refine ⟨hβ,?_⟩
  exact population_good_gaps_of_mean_tail μ η p₀ p₁ h₀ h₁ ρ hρ hρ4 mZ (by dsimp [mZ]; positivity) Z
    (fun q hq => (hnew q hq).1) (fun q hq => (hnew q hq).2) hbad

end ThresholdHC.EntropyTailLower
