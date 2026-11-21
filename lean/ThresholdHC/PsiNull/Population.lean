import ThresholdHC.PsiNull.Specification
import ThresholdHC.PsiNull.Response
import ThresholdHC.CriticalEntropy.ConditionalMoments
import ThresholdHC.CriticalEntropy.HalfPrior
import ThresholdHC.UnbiasedConverse.TwoPoint
import ThresholdHC.Tier3.OptimizerModel

/-! Population step of Proposition prop:psi-null.

For a capped procedure with bounded output whose extended variance is at most `V`
and whose bias is at most `b` on the capped prior class, every feasible
allocation `v` of `Ψ_{μ,ρ}` satisfies
`∫ min{v, h√v/d} dμ ≤ 4b + h √(192 V W₀)`, where `W₀` is the expected work of
the all-negative population (`psi_objective_bound`). The proof follows the paper:

* the allocation is clamped pointwise into `[0,1]`, which changes it only on a
  null set, so `q = w/2` and `q = v_h/2` with `v_h = min{w, h√w/d}` are capped
  sign priors;
* the constant priors `0` and `ρ` give the variance floor `2ρ/3 ≤ V`, so the
  second moment at `q = w/2` is at most `3V/2`, and hence
  `∫ w (A₋ + A₊) dμ ≤ 3V` (`allocation_moment_bound`);
* comparing the mean at `q = v_h/2` with the null mean and using both bias bounds
  gives `∫ v_h f dμ ≥ ∫ v_h dμ - 4b` (`allocation_response_lower`);
* the per-gap response bound `f² ≤ 64 d² w₋ (A₋ + A₊)` and `v_h ≤ h√w/d` give
  the pointwise bound `v_h |f| ≤ 8h √w₋ √(w (A₋ + A₊))`, and Cauchy–Schwarz
  against `∫ w₋ dμ = W₀` finishes.

Bounded output and the cap make every conditional function bounded, so all
integrals are ordinary Bochner integrals and the paper's quotient `w f²/(d² w₋)`
and its truncation argument are not needed. -/
noncomputable section
namespace ThresholdHC.PsiNull
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open ThresholdHC.Tier6 ThresholdHC.CriticalEntropy
open ThresholdHC.ObservableSimulation (gapParameter measurable_gapParameter)

/-- A bounded output has conditional second moment at most the squared bound. -/
theorem conditionalSecondMoment_toReal_le_sq {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R ℝ)
    {C : ℝ} (hC : ∀ z, |A.output z| ≤ C) (p : unitInterval) :
    (conditionalSecondMoment ν p A).toReal ≤ C^2 := by
  rw [conditionalSecondMoment_toReal_eq]
  calc
    _ ≤ ∫ _z, C^2 ∂ν.prod (Tier2.tapeMeasure p) := by
      refine integral_mono (output_memLp_two_of_bound ν A hC p).integrable_sq
        (integrable_const _) (fun z => ?_)
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hC z) 2
    _ = C^2 := by simp

/-- A bounded output has conditional mean bounded by the same constant. -/
theorem abs_conditionalMean_le {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν] (A : StoppedProcedure R ℝ)
    {C : ℝ} (hC : ∀ z, |A.output z| ≤ C) (p : unitInterval) :
    |conditionalMean ν p A| ≤ C := by
  unfold conditionalMean
  calc
    _ ≤ ∫ z, |A.output z| ∂ν.prod (Tier2.tapeMeasure p) := abs_integral_le_integral_abs
    _ ≤ ∫ _z, C ∂ν.prod (Tier2.tapeMeasure p) :=
      integral_mono (output_integrable_of_bound ν A hC p).abs (integrable_const _) hC
    _ = C := by simp

/-- A bounded output has a finite population second moment under every prior. -/
theorem populationSecondMoment_ne_top_of_bound {D R : Type} [MeasurableSpace D]
    [MeasurableSpace R] (μ : Measure D) [IsProbabilityMeasure μ]
    (ν : Measure R) [IsProbabilityMeasure ν] (p₀ p₁ q : D → unitInterval)
    (A : StoppedProcedure R ℝ) {C : ℝ} (hC : ∀ z, |A.output z| ≤ C) :
    populationSecondMoment μ ν p₀ p₁ q A ≠ ∞ := by
  have hP : IsProbabilityMeasure (populationMeasure μ ν) := by
    unfold populationMeasure
    infer_instance
  refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := C^2)) ?_
  unfold populationSecondMoment
  calc
    _ ≤ ∫⁻ _z, ENNReal.ofReal (C^2) ∂populationMeasure μ ν := by
      apply lintegral_mono
      intro z
      apply ENNReal.ofReal_le_ofReal
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hC _) 2
    _ = _ := by simp

/-- Half of a measurable `[0,1]`-valued function is a measurable sign prior. -/
theorem exists_half_prior {D : Type} [MeasurableSpace D] {g : D → ℝ} (hg : Measurable g)
    (hg0 : ∀ d, 0 ≤ g d) (hg1 : ∀ d, g d ≤ 1) :
    ∃ q : D → unitInterval, Measurable q ∧ ∀ d, (q d : ℝ) = g d / 2 :=
  ⟨fun d => ⟨g d / 2, by linarith [hg0 d], by linarith [hg1 d]⟩,
    (hg.div_const 2).subtype_mk, fun _ => rfl⟩

/-- For a capped procedure, the integrated negative-sign conditional work is the
all-negative population work. -/
theorem integral_negativeWork_eq {D R E : Type}
    [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (A : StoppedProcedure R E) (m : ℕ) (hcap : ∀ z, A.stop z ≤ m) :
    (∫ d, (expectedStoppedProcedureWork ν (p₀ d) A).toReal ∂μ) =
      (populationExpectedWork μ ν p₀ p₁ (fun _ => 0) A).toReal := by
  have he := population_work_formula μ ν p₀ p₁ (fun _ => 0) h₀ h₁ measurable_const A
  norm_num at he
  have hme : Measurable (fun d => expectedStoppedProcedureWork ν (p₀ d) A) :=
    (measurable_conditionalWork ν A).comp h₀
  rw [he, integral_toReal hme.aemeasurable (ae_of_all _ (fun d =>
    lt_of_le_of_lt (expectedStoppedProcedureWork_le_cap ν A m hcap _)
      (ENNReal.natCast_lt_top m)))]

/-- The constant priors `0` and `ρ` force the variance floor `2ρ/3 ≤ V` on any
uniform extended-variance bound `V` when the bias is at most `ρ/64`. -/
theorem variance_floor_of_bounds {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (A : StoppedProcedure R ℝ) {ρ b V : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hbρ : b ≤ ρ/64)
    (hV : 0 ≤ V)
    (hvar : ∀ q : D → unitInterval, CappedPrior μ ρ q →
      evariance (A.output ∘ populationInput p₀ p₁ q) (populationMeasure μ ν) ≤ ENNReal.ofReal V)
    (hbias : ∀ q : D → unitInterval, CappedPrior μ ρ q →
      |populationMean μ ν p₀ p₁ q A - (∫ d, (q d : ℝ) ∂μ)| ≤ b) :
    2*ρ/3 ≤ V := by
  set c : unitInterval := ⟨ρ, hρ.le, by linarith⟩
  have hcv : (c : ℝ) = ρ := rfl
  have h0 : CappedPrior μ ρ (fun _ => (0 : unitInterval)) :=
    cappedPrior_const μ ρ 0 (by norm_num) (by simpa using hρ.le)
  have hcp : CappedPrior μ ρ (fun _ => c) :=
    cappedPrior_const μ ρ c (by rw [hcv]; linarith) (by rw [hcv])
  have hv0 := hvar _ h0
  have hvc := hvar _ hcp
  have hb0 := hbias _ h0
  have hbc := hbias _ hcp
  simp only [Set.Icc.coe_zero, integral_const, probReal_univ, smul_eq_mul, mul_zero, sub_zero,
    one_mul] at hb0 hbc
  have h := population_evariance_floor μ ν p₀ p₁ h₀ h₁ c (by rw [hcv]; exact hρ)
    (by rw [hcv]; exact hρ4) A (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hv0)
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvc) (by rw [hcv]; linarith)
    (by rw [hcv]; linarith)
  rw [hcv] at h
  exact (ENNReal.ofReal_le_ofReal_iff hV).mp (h.trans hvc)

/-- Moment step at `q = g/2`: for a measurable allocation `0 ≤ g ≤ 1` with
`∫ g ≤ 2ρ`, the prior `g/2` is capped, its second moment is at most `3V/2`, and
hence `∫ g (A₋ + A₊) dμ ≤ 3V`. -/
theorem allocation_moment_bound {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (A : StoppedProcedure R ℝ) {C : ℝ} (hC : ∀ z, |A.output z| ≤ C)
    {ρ b V : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hbρ : b ≤ ρ/64) (hV : 0 ≤ V)
    (hvar : ∀ q : D → unitInterval, CappedPrior μ ρ q →
      evariance (A.output ∘ populationInput p₀ p₁ q) (populationMeasure μ ν) ≤ ENNReal.ofReal V)
    (hbias : ∀ q : D → unitInterval, CappedPrior μ ρ q →
      |populationMean μ ν p₀ p₁ q A - (∫ d, (q d : ℝ) ∂μ)| ≤ b)
    {g : D → ℝ} (hg : Measurable g) (hg0 : ∀ d, 0 ≤ g d) (hg1 : ∀ d, g d ≤ 1)
    (hgρ : (∫ d, g d ∂μ) ≤ 2*ρ) :
    (∫ d, g d * ((conditionalSecondMoment ν (p₀ d) A).toReal +
      (conditionalSecondMoment ν (p₁ d) A).toReal) ∂μ) ≤ 3*V := by
  obtain ⟨q, hqm, hq⟩ := exists_half_prior hg hg0 hg1
  have hqint : (∫ d, (q d : ℝ) ∂μ) = (∫ d, g d ∂μ) / 2 := by
    rw [← integral_div]
    exact integral_congr_ae (ae_of_all _ hq)
  have hqc : CappedPrior μ ρ q :=
    ⟨hqm, fun d => by rw [hq d]; linarith [hg1 d], by rw [hqint]; linarith⟩
  have hfloor := variance_floor_of_bounds μ ν p₀ p₁ h₀ h₁ A hρ hρ4 hbρ hV hvar hbias
  have hM := population_moment_bound_of_evariance μ ν p₀ p₁ q h₀ h₁ hqm A ρ V hρ hρ4 hfloor
    hqc.2.2 ((hbias q hqc).trans hbρ) (hvar q hqc)
  have hMr : (populationSecondMoment μ ν p₀ p₁ q A).toReal ≤ 3*V/2 :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hM
  set c : unitInterval := ⟨1/2, by norm_num, by norm_num⟩ with hc
  have hformula := population_second_moment_real_formula μ ν p₀ p₁ h₀ h₁ c
    (by rw [hc]; norm_num) A (populationSecondMoment_ne_top_of_bound μ ν p₀ p₁ _ A hC)
    (populationSecondMoment_ne_top_of_bound μ ν p₀ p₁ _ A hC) q hqm
  set Am := fun d => (conditionalSecondMoment ν (p₀ d) A).toReal
  set Ap := fun d => (conditionalSecondMoment ν (p₁ d) A).toReal
  have hAmm : Measurable Am := ((measurable_conditionalSecondMoment ν A).comp h₀).ennreal_toReal
  have hApm : Measurable Ap := ((measurable_conditionalSecondMoment ν A).comp h₁).ennreal_toReal
  have hAm0 : ∀ d, 0 ≤ Am d := fun d => ENNReal.toReal_nonneg
  have hAp0 : ∀ d, 0 ≤ Ap d := fun d => ENNReal.toReal_nonneg
  have hAm1 : ∀ d, Am d ≤ C^2 := fun d => conditionalSecondMoment_toReal_le_sq ν A hC _
  have hAp1 : ∀ d, Ap d ≤ C^2 := fun d => conditionalSecondMoment_toReal_le_sq ν A hC _
  have hint1 : Integrable (fun d => g d * (Am d + Ap d)) μ := by
    refine Integrable.of_bound (hg.mul (hAmm.add hApm)).aestronglyMeasurable (2*C^2)
      (ae_of_all _ (fun d => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hg0 d) (add_nonneg (hAm0 d) (hAp0 d)))]
    nlinarith [hg0 d, hg1 d, hAm0 d, hAp0 d, hAm1 d, hAp1 d,
      mul_nonneg (sub_nonneg.2 (hg1 d)) (add_nonneg (hAm0 d) (hAp0 d))]
  have hint2 : Integrable (fun d => 2 * ((q d : ℝ) * Ap d + (1 - (q d : ℝ)) * Am d)) μ := by
    refine Integrable.of_bound (measurable_const.mul
      (((measurable_subtype_coe.comp hqm).mul hApm).add
        ((measurable_const.sub (measurable_subtype_coe.comp hqm)).mul hAmm))).aestronglyMeasurable
      (2*C^2) (ae_of_all _ (fun d => ?_))
    have hq0 := (q d).property.1
    have hq1 := (q d).property.2
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [mul_nonneg hq0 (sub_nonneg.2 (hAp1 d)),
      mul_nonneg (sub_nonneg.2 hq1) (sub_nonneg.2 (hAm1 d))]
  calc
    _ ≤ ∫ d, 2 * ((q d : ℝ) * Ap d + (1 - (q d : ℝ)) * Am d) ∂μ := by
      refine integral_mono hint1 hint2 (fun d => ?_)
      simp only [hq d]
      nlinarith [mul_nonneg (sub_nonneg.2 (hg1 d)) (hAm0 d)]
    _ = 2 * (populationSecondMoment μ ν p₀ p₁ q A).toReal := by
      rw [integral_const_mul, hformula]
    _ ≤ 3*V := by linarith

/-- Response step at `q = g/2`: for a measurable allocation `0 ≤ g ≤ 1` with
`∫ g ≤ 2ρ`, comparing the mean at the capped prior `g/2` with the null mean and
using both bias bounds gives `∫ g (E₊ - E₋) dμ ≥ ∫ g dμ - 4b`. -/
theorem allocation_response_lower {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (A : StoppedProcedure R ℝ) {C : ℝ} (hC : ∀ z, |A.output z| ≤ C)
    {ρ b : ℝ} (hρ : 0 < ρ)
    (hbias : ∀ q : D → unitInterval, CappedPrior μ ρ q →
      |populationMean μ ν p₀ p₁ q A - (∫ d, (q d : ℝ) ∂μ)| ≤ b)
    {g : D → ℝ} (hg : Measurable g) (hg0 : ∀ d, 0 ≤ g d) (hg1 : ∀ d, g d ≤ 1)
    (hgρ : (∫ d, g d ∂μ) ≤ 2*ρ) :
    (∫ d, g d ∂μ) - 4*b ≤
      ∫ d, g d * (conditionalMean ν (p₁ d) A - conditionalMean ν (p₀ d) A) ∂μ := by
  obtain ⟨q, hqm, hq⟩ := exists_half_prior hg hg0 hg1
  have hqint : (∫ d, (q d : ℝ) ∂μ) = (∫ d, g d ∂μ) / 2 := by
    rw [← integral_div]
    exact integral_congr_ae (ae_of_all _ hq)
  have hqc : CappedPrior μ ρ q :=
    ⟨hqm, fun d => by rw [hq d]; linarith [hg1 d], by rw [hqint]; linarith⟩
  have h0 : CappedPrior μ ρ (fun _ => (0 : unitInterval)) :=
    cappedPrior_const μ ρ 0 (by norm_num) (by simpa using hρ.le)
  have hbq := hbias q hqc
  have hb0 := hbias _ h0
  simp only [Set.Icc.coe_zero, integral_const, probReal_univ, smul_eq_mul, mul_zero,
    sub_zero] at hb0
  set Em := fun d => conditionalMean ν (p₀ d) A
  set Ep := fun d => conditionalMean ν (p₁ d) A
  have hEmm : Measurable Em := (measurable_conditionalMean ν A).comp h₀
  have hEpm : Measurable Ep := (measurable_conditionalMean ν A).comp h₁
  have hEm1 : ∀ d, |Em d| ≤ C := fun d => abs_conditionalMean_le ν A hC _
  have hEp1 : ∀ d, |Ep d| ≤ C := fun d => abs_conditionalMean_le ν A hC _
  have hmq := population_mean_formula μ ν p₀ p₁ q h₀ h₁ hqm A
    (populationSecondMoment_ne_top_of_bound μ ν p₀ p₁ _ A hC)
  have hm0 := population_mean_formula μ ν p₀ p₁ (fun _ => 0) h₀ h₁ measurable_const A
    (populationSecondMoment_ne_top_of_bound μ ν p₀ p₁ _ A hC)
  simp only [Set.Icc.coe_zero, zero_mul, zero_add, sub_zero, one_mul] at hm0
  have hint1 : Integrable (fun d => (q d : ℝ) * Ep d + (1 - (q d : ℝ)) * Em d) μ := by
    refine Integrable.of_bound (((measurable_subtype_coe.comp hqm).mul hEpm).add
      ((measurable_const.sub (measurable_subtype_coe.comp hqm)).mul hEmm)).aestronglyMeasurable
      C (ae_of_all _ (fun d => ?_))
    have hq0 := (q d).property.1
    have hq1 := (q d).property.2
    rw [Real.norm_eq_abs]
    calc
      _ ≤ |(q d : ℝ) * Ep d| + |(1 - (q d : ℝ)) * Em d| := abs_add_le _ _
      _ = (q d : ℝ) * |Ep d| + (1 - (q d : ℝ)) * |Em d| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hq0, abs_of_nonneg (sub_nonneg.2 hq1)]
      _ ≤ (q d : ℝ) * C + (1 - (q d : ℝ)) * C :=
        add_le_add (mul_le_mul_of_nonneg_left (hEp1 d) hq0)
          (mul_le_mul_of_nonneg_left (hEm1 d) (sub_nonneg.2 hq1))
      _ = C := by ring
  have hint2 : Integrable Em μ :=
    Integrable.of_bound hEmm.aestronglyMeasurable C
      (ae_of_all _ (fun d => by rw [Real.norm_eq_abs]; exact hEm1 d))
  have hdiff : populationMean μ ν p₀ p₁ q A - populationMean μ ν p₀ p₁ (fun _ => 0) A =
      (∫ d, g d * (Ep d - Em d) ∂μ) / 2 := by
    rw [hmq, hm0, ← integral_sub hint1 hint2, ← integral_div]
    congr 1
    funext d
    rw [hq d]
    ring
  rw [hqint] at hbq
  have k1 := (abs_le.mp hbq).1
  have k2 := (abs_le.mp hb0).2
  linarith

/-- Population step of Proposition prop:psi-null. Under the hypotheses of
`NullVarianceObstruction` for the original coin parameters (a capped procedure
with bounded output, extended variance at most `V` and bias at most `b ≤ ρ/64`
on the capped prior class, `0 < ρ ≤ 1/4`), every feasible allocation `v` of
`Ψ_{μ,ρ}(h)`, `h ≥ 0`, satisfies `∫ min{v, h√v/d} dμ ≤ 4b + h √(192 V W₀)`,
where `W₀` is the expected work of the all-negative population. -/
theorem psi_objective_bound {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (A : StoppedProcedure R ℝ) (m : ℕ) (hcap : ∀ z, A.stop z ≤ m)
    {C : ℝ} (hC : ∀ z, |A.output z| ≤ C)
    {ρ b V h : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hbρ : b ≤ ρ/64) (hh : 0 ≤ h) (hV : 0 ≤ V)
    (hvar : ∀ q : Gap → unitInterval, CappedPrior μ ρ q →
      evariance (A.output ∘ populationInput (gapParameter false) (gapParameter true) q)
        (populationMeasure μ ν) ≤ ENNReal.ofReal V)
    (hbias : ∀ q : Gap → unitInterval, CappedPrior μ ρ q →
      |populationMean μ ν (gapParameter false) (gapParameter true) q A -
        (∫ d, (q d : ℝ) ∂μ)| ≤ b)
    {v : Gap → ℝ} (hv : Tier3.FeasibleAllocation μ ρ v) :
    Tier3.rareObjective μ (fun d => (d : ℝ)) h v ≤
      4*b + h * Real.sqrt (192 * V * (populationExpectedWork μ ν (gapParameter false)
        (gapParameter true) (fun _ => 0) A).toReal) := by
  have h₀ : Measurable (gapParameter false) := measurable_gapParameter false
  have h₁ : Measurable (gapParameter true) := measurable_gapParameter true
  -- A nonnegative output bound.
  set K := max C 0
  have hCK : ∀ z, |A.output z| ≤ K := fun z => (hC z).trans (le_max_left _ _)
  -- Clamp the a.e. feasible allocation pointwise into `[0,1]`.
  set w : Gap → ℝ := fun d => max 0 (min 1 (v d)) with hwdef
  have hwm : Measurable w := measurable_const.max (measurable_const.min hv.1)
  have hw0 : ∀ d, 0 ≤ w d := fun d => le_max_left _ _
  have hw1 : ∀ d, w d ≤ 1 := fun d => max_le zero_le_one (min_le_left _ _)
  have hwv : ∀ᵐ d ∂μ, w d = v d := by
    filter_upwards [hv.2.1] with d hd
    simp only [hwdef, min_eq_right hd.2, max_eq_right hd.1]
  have hwint : Integrable w μ :=
    Integrable.of_bound hwm.aestronglyMeasurable 1 (ae_of_all _ (fun d => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hw0 d)]; exact hw1 d))
  have hwρ : (∫ d, w d ∂μ) ≤ ρ := (integral_congr_ae hwv).trans_le hv.2.2
  -- The objective allocation `v_h = min{w, h√w/d}`.
  set vh : Gap → ℝ := fun d => min (w d) (h * Real.sqrt (w d) / d) with hvhdef
  have hvhm : Measurable vh :=
    hwm.min ((measurable_const.mul hwm.sqrt).div measurable_subtype_coe)
  have hvh0 : ∀ d, 0 ≤ vh d := fun d =>
    le_min (hw0 d) (div_nonneg (mul_nonneg hh (Real.sqrt_nonneg _)) d.property.1.le)
  have hvhw : ∀ d, vh d ≤ w d := fun d => min_le_left _ _
  have hvh1 : ∀ d, vh d ≤ 1 := fun d => (hvhw d).trans (hw1 d)
  have hvhint : Integrable vh μ :=
    Integrable.of_bound hvhm.aestronglyMeasurable 1 (ae_of_all _ (fun d => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hvh0 d)]; exact hvh1 d))
  have hobj : Tier3.rareObjective μ (fun d => (d : ℝ)) h v = ∫ d, vh d ∂μ := by
    unfold Tier3.rareObjective
    refine integral_congr_ae ?_
    filter_upwards [hwv] with d hd
    simp only [hvhdef, hd]
  have hvhρ : (∫ d, vh d ∂μ) ≤ 2*ρ :=
    (integral_mono hvhint hwint hvhw).trans (by linarith)
  -- The two integrated steps and the null work.
  have hresp := allocation_response_lower μ ν (gapParameter false) (gapParameter true) h₀ h₁ A
    hCK hρ hbias hvhm hvh0 hvh1 hvhρ
  have hmom := allocation_moment_bound μ ν (gapParameter false) (gapParameter true) h₀ h₁ A
    hCK hρ hρ4 hbρ hV hvar hbias hwm hw0 hw1 (by linarith)
  have hwork := integral_negativeWork_eq μ ν (gapParameter false) (gapParameter true) h₀ h₁
    A m hcap
  set W₀ := (populationExpectedWork μ ν (gapParameter false) (gapParameter true)
    (fun _ => 0) A).toReal
  have hW₀ : 0 ≤ W₀ := ENNReal.toReal_nonneg
  -- Conditional second moments and negative work as functions of the gap.
  set Am := fun d => (conditionalSecondMoment ν (gapParameter false d) A).toReal with hAmdef
  set Ap := fun d => (conditionalSecondMoment ν (gapParameter true d) A).toReal with hApdef
  set wm := fun d => (expectedStoppedProcedureWork ν (gapParameter false d) A).toReal
  have hAmm : Measurable Am := ((measurable_conditionalSecondMoment ν A).comp h₀).ennreal_toReal
  have hApm : Measurable Ap := ((measurable_conditionalSecondMoment ν A).comp h₁).ennreal_toReal
  have hwmm : Measurable wm := ((measurable_conditionalWork ν A).comp h₀).ennreal_toReal
  have hS0 : ∀ d, 0 ≤ Am d + Ap d := fun d => add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hS1 : ∀ d, Am d + Ap d ≤ 2*K^2 := fun d => by
    have := conditionalSecondMoment_toReal_le_sq ν A hCK (gapParameter false d)
    have := conditionalSecondMoment_toReal_le_sq ν A hCK (gapParameter true d)
    simp only [hAmdef, hApdef]
    linarith
  have hwm0 : ∀ d, 0 ≤ wm d := fun d => ENNReal.toReal_nonneg
  have hwm1 : ∀ d, wm d ≤ m := fun d =>
    ENNReal.toReal_le_of_le_ofReal (Nat.cast_nonneg m)
      (by rw [ENNReal.ofReal_natCast]; exact expectedStoppedProcedureWork_le_cap ν A m hcap _)
  -- The two square-integrable factors of the weighted Cauchy–Schwarz step.
  set F := fun d => Real.sqrt (wm d) with hFdef
  set G := fun d => Real.sqrt (w d * (Am d + Ap d)) with hGdef
  have hFm : Measurable F := hwmm.sqrt
  have hGm : Measurable G := (hwm.mul (hAmm.add hApm)).sqrt
  have hF : MemLp F 2 μ :=
    MemLp.of_bound hFm.aestronglyMeasurable (Real.sqrt m) (ae_of_all _ (fun d => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact Real.sqrt_le_sqrt (hwm1 d)))
  have hG : MemLp G 2 μ :=
    MemLp.of_bound hGm.aestronglyMeasurable (Real.sqrt (2*K^2)) (ae_of_all _ (fun d => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      apply Real.sqrt_le_sqrt
      nlinarith [hw0 d, hw1 d, hS0 d, hS1 d, mul_nonneg (sub_nonneg.2 (hw1 d)) (hS0 d)]))
  -- Pointwise: `v_h f ≤ 8h √w₋ √(w (A₋ + A₊))`.
  have hpt : ∀ d, vh d * (conditionalMean ν (gapParameter true d) A -
      conditionalMean ν (gapParameter false d) A) ≤ 8 * h * (F d * G d) := by
    intro d
    set f := conditionalMean ν (gapParameter true d) A -
      conditionalMean ν (gapParameter false d) A
    have hd0 : 0 < (d : ℝ) := d.property.1
    have hresp_d : f^2 ≤ 64 * (d : ℝ)^2 * wm d * (Am d + Ap d) :=
      gap_response_bound ν A m hcap K hCK d
    have hvd : vh d * d ≤ h * Real.sqrt (w d) :=
      (le_div_iff₀ hd0).mp (min_le_right (w d) (h * Real.sqrt (w d) / d))
    have hvd2 : vh d ^ 2 * (d : ℝ)^2 ≤ h^2 * w d := by
      rw [← mul_pow]
      calc
        (vh d * d)^2 ≤ (h * Real.sqrt (w d))^2 :=
          pow_le_pow_left₀ (mul_nonneg (hvh0 d) hd0.le) hvd 2
        _ = h^2 * w d := by rw [mul_pow, Real.sq_sqrt (hw0 d)]
    have hRHS : 0 ≤ 8 * h * (F d * G d) :=
      mul_nonneg (mul_nonneg (by norm_num) hh) (mul_nonneg (Real.sqrt_nonneg _)
        (Real.sqrt_nonneg _))
    have hRHS2 : (8 * h * (F d * G d))^2 = 64 * h^2 * (wm d * (w d * (Am d + Ap d))) := by
      simp only [hFdef, hGdef]
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (hwm0 d),
        Real.sq_sqrt (mul_nonneg (hw0 d) (hS0 d))]
      ring
    have key : (vh d * |f|)^2 ≤ (8 * h * (F d * G d))^2 := by
      rw [hRHS2, mul_pow, sq_abs]
      calc
        vh d ^ 2 * f^2 ≤ vh d ^ 2 * (64 * (d : ℝ)^2 * wm d * (Am d + Ap d)) :=
          mul_le_mul_of_nonneg_left hresp_d (sq_nonneg _)
        _ = (vh d ^ 2 * (d : ℝ)^2) * (64 * wm d * (Am d + Ap d)) := by ring
        _ ≤ (h^2 * w d) * (64 * wm d * (Am d + Ap d)) :=
          mul_le_mul_of_nonneg_right hvd2
            (mul_nonneg (mul_nonneg (by norm_num) (hwm0 d)) (hS0 d))
        _ = _ := by ring
    calc
      vh d * f ≤ vh d * |f| := mul_le_mul_of_nonneg_left (le_abs_self _) (hvh0 d)
      _ ≤ _ := (le_abs_self _).trans (abs_le_of_sq_le_sq key hRHS)
  -- Weighted Cauchy–Schwarz against `∫ w₋ dμ = W₀`.
  have hCS := ThresholdHC.UnbiasedConverse.integral_mul_sq_le μ hF hG
  have hF2 : (∫ d, F d ^ 2 ∂μ) = W₀ :=
    (integral_congr_ae (ae_of_all _ (fun d => Real.sq_sqrt (hwm0 d)))).trans hwork
  have hG2 : (∫ d, G d ^ 2 ∂μ) = ∫ d, w d * (Am d + Ap d) ∂μ :=
    integral_congr_ae (ae_of_all _ (fun d => Real.sq_sqrt (mul_nonneg (hw0 d) (hS0 d))))
  rw [hF2, hG2] at hCS
  have hX : (∫ d, F d * G d ∂μ) ≤ Real.sqrt (W₀ * (3*V)) :=
    Real.le_sqrt_of_sq_le (hCS.trans (mul_le_mul_of_nonneg_left hmom hW₀))
  have hvf : Integrable (fun d => vh d * (conditionalMean ν (gapParameter true d) A -
      conditionalMean ν (gapParameter false d) A)) μ := by
    refine Integrable.of_bound (hvhm.mul (((measurable_conditionalMean ν A).comp h₁).sub
      ((measurable_conditionalMean ν A).comp h₀))).aestronglyMeasurable (2*K)
      (ae_of_all _ (fun d => ?_))
    have e1 := abs_conditionalMean_le ν A hCK (gapParameter true d)
    have e2 := abs_conditionalMean_le ν A hCK (gapParameter false d)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hvh0 d)]
    calc
      _ ≤ 1 * |conditionalMean ν (gapParameter true d) A -
          conditionalMean ν (gapParameter false d) A| :=
        mul_le_mul_of_nonneg_right (hvh1 d) (abs_nonneg _)
      _ ≤ 2*K := by
        rw [one_mul]
        exact (abs_sub _ _).trans (by linarith)
  have hFG : Integrable (fun d => 8 * h * (F d * G d)) μ :=
    (hF.integrable_mul hG).const_mul (8*h)
  have hI : (∫ d, vh d * (conditionalMean ν (gapParameter true d) A -
      conditionalMean ν (gapParameter false d) A) ∂μ) ≤ 8 * h * ∫ d, F d * G d ∂μ := by
    rw [← integral_const_mul]
    exact integral_mono hvf hFG hpt
  have hsqrt : Real.sqrt (192 * V * W₀) = 8 * Real.sqrt (W₀ * (3*V)) := by
    rw [show 192 * V * W₀ = 8^2 * (W₀ * (3*V)) by ring, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  have h8 := mul_le_mul_of_nonneg_left hX (by positivity : (0 : ℝ) ≤ 8*h)
  rw [hobj, hsqrt]
  linarith

end ThresholdHC.PsiNull
