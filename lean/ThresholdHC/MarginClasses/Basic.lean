import ThresholdHC.MarginClasses.Specification
import ThresholdHC.Envelope.Minimax
import ThresholdHC.SubcriticalPower.Sublinear
import ThresholdHC.RareAboveTwo.Margin

/-! Generic lemmas for the margin-class corollaries: budget monotonicity, the
numerical cutoff, the budget floor forced on a valid estimator, the confidence
scale of an inverted budget, the reference power scale `C^{-1/α}` and its laws,
modulus bounds, and the common blind confidence family. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.MarginClasses
open ThresholdHC.Tier6 ThresholdHC.Confidence ThresholdHC.Envelope ThresholdHC.BlindUpper
open ThresholdHC.OracleLower ThresholdHC.RareAboveTwo ThresholdHC.SubcriticalPower

theorem budget_mono {R : Type} [MeasurableSpace R] {ν : Measure Gap} [IsProbabilityMeasure ν]
    {A : AdaptiveEstimator R} {B B' : ℝ} (h : UniformBudget ν A B) (hB : B ≤ B') :
    UniformBudget ν A B' :=
  fun q => (h q).trans (ENNReal.ofReal_le_ofReal hB)

/-- The universal lower comparison constant exceeds the cutoff `1/25`. -/
theorem cutoff_lt : (1:ℝ)/25 < 15/(256*Real.sqrt 2) := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hs0 := Real.sqrt_nonneg (2:ℝ)
  rw [lt_div_iff₀ (by positivity)]
  nlinarith

theorem lower_const_sq : (15/(256*Real.sqrt 2))^2 = (225/131072 : ℝ) := by
  rw [div_pow,mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

theorem log_ge {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1/4) : 3/4 ≤ Real.log (1/δ) := by
  have h := Real.one_sub_inv_le_log_of_pos (one_div_pos.mpr hδ)
  have he : (1/δ)⁻¹ = δ := by rw [one_div,inv_inv]
  rw [he] at h
  linarith

/-- An estimator valid at accuracy `ε ≤ 1/25` with `0 < δ ≤ 1/4`, at any law,
has budget at least one: below one the confidence lower bound runs at scale at
least `1/2`, where the modulus is one. -/
theorem valid_budget_ge_one {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) {B ε δ : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1/25) (hδ : 0 < δ) (hδ' : δ ≤ 1/4)
    (hw : UniformBudget μ A B) (hc : UniformConfidence μ A ε δ) : 1 ≤ B := by
  by_contra hB
  have h1 := hidden_confidence_lower μ A 1 δ ε le_rfl hδ hδ' hε
    (budget_mono hw (lt_of_not_ge hB).le) hc
  have hL := log_ge hδ hδ'
  have hs : 1/2 ≤ confidenceScale 1 δ := by
    rw [confidenceScale,div_one]
    apply (Real.le_sqrt (by norm_num) (by linarith)).mpr
    linarith
  rw [modulus_eq_one_of_half_le μ hs,mul_one] at h1
  linarith [cutoff_lt]

/-- A valid witness forces `1 ≤ B` and the confidence lower bound at its scale. -/
theorem witness_lower {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) {B ε δ : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1/25) (hδ : 0 < δ) (hδ' : δ ≤ 1/4)
    (hw : UniformBudget μ A B) (hc : UniformConfidence μ A ε δ) :
    1 ≤ B ∧ (15/(256*Real.sqrt 2))*modulus μ (confidenceScale B δ) ≤ ε := by
  have hB := valid_budget_ge_one μ A hε.le hε' hδ hδ' hw hc
  exact ⟨hB,hidden_confidence_lower μ A B δ ε hB hδ hδ' hε.le hw hc⟩

theorem scale_sq {B δ : ℝ} (hB : 0 < B) (hδ : 0 < δ) (hδ' : δ ≤ 1/4) :
    (confidenceScale B δ)^2 * B = Real.log (1/δ) := by
  rw [confidenceScale,Real.sq_sqrt (div_nonneg (confidence_log_pos hδ hδ').le hB.le)]
  exact div_mul_cancel₀ _ hB.ne'

theorem scale_eq {B δ x : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1/4) (hx : 0 < x)
    (hB : B * x^2 = Real.log (1/δ)) : confidenceScale B δ = x := by
  have hL := confidence_log_pos hδ hδ'
  have hx2 : 0 < x^2 := by positivity
  have hB0 : 0 < B := by
    by_contra h
    have h' : B * x^2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) hx2.le
    linarith
  have he : Real.log (1/δ) / B = x^2 := by
    rw [← hB]
    field_simp
  rw [confidenceScale,he,Real.sqrt_sq hx.le]

/-! The reference power scale `a = C^{-1/α}`. -/

theorem ref_pos {α C : ℝ} (hC : 0 < C) : 0 < C^(-(1/α)) := Real.rpow_pos_of_pos hC _

theorem class_const_pos {α C : ℝ} (hC : 2^α ≤ C) : 0 < C :=
  lt_of_lt_of_le (Real.rpow_pos_of_pos (by norm_num) α) hC

theorem ref_root_ge {α C : ℝ} (hα : 0 < α) (hC : 2^α ≤ C) : 2 ≤ C^(1/α) := by
  have h := Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) α) hC (one_div_pos.mpr hα).le
  rwa [← Real.rpow_mul (by norm_num),mul_one_div_cancel hα.ne',Real.rpow_one] at h

theorem ref_le_half {α C : ℝ} (hα : 0 < α) (hC : 2^α ≤ C) : C^(-(1/α)) ≤ 1/2 := by
  rw [Real.rpow_neg (class_const_pos hC).le,one_div 2]
  exact inv_anti₀ (by norm_num) (ref_root_ge hα hC)

theorem ref_mul {α C : ℝ} (hC : 0 < C) : C^(1/α) * C^(-(1/α)) = 1 := by
  rw [Real.rpow_neg hC.le,mul_inv_cancel₀ (Real.rpow_pos_of_pos hC _).ne']

theorem ref_power {α C x : ℝ} (hα : 0 < α) (hC : 0 < C) (hx : 0 ≤ x) :
    (x / C^(-(1/α)))^α = C * x^α := by
  rw [Real.div_rpow hx (Real.rpow_nonneg hC.le _),← Real.rpow_mul hC.le,neg_mul,
    one_div_mul_cancel hα.ne',Real.rpow_neg_one,div_inv_eq_mul,mul_comm]

/-- A law of the polynomial class has the power margin at the reference scale. -/
theorem powerClass_margin {α C : ℝ} (hα : 0 < α) (hC : 2^α ≤ C) {ν : Measure Gap}
    (h : PowerClass α C ν) : PowerMargin ν α (C^(-(1/α))) := by
  intro x hx hxa
  rw [ref_power hα (class_const_pos hC) hx.le]
  exact h x hx (hxa.le.trans (ref_le_half hα hC))

/-- The exact reference power law lies in the class. -/
theorem refLaw_mem {α C : ℝ} (hα : 0 < α) (hC : 2^α ≤ C) :
    PowerClass α C (powerGapLaw α (C^(-(1/α))) hα (ref_pos (class_const_pos hC)) (ref_le_half hα hC)) := by
  intro t ht _
  rw [powerGapLaw_cdf _ _ _ _ _ t ht,← ref_power hα (class_const_pos hC) ht.le]
  exact min_le_right _ _

/-- For `α ≤ 1` the linear law at the reference scale lies in the class. -/
theorem linearLaw_mem {α C : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hC : 2^α ≤ C) :
    PowerClass α C (powerGapLaw 1 (C^(-(1/α))) (by norm_num) (ref_pos (class_const_pos hC))
      (ref_le_half hα hC)) := by
  intro t ht _
  have ha := ref_pos (α := α) (class_const_pos hC)
  rw [powerGapLaw_cdf _ _ _ _ _ t ht,Real.rpow_one,← ref_power hα (class_const_pos hC) ht.le]
  by_cases h1 : t / C^(-(1/α)) ≤ 1
  · exact (min_le_right _ _).trans (Real.self_le_rpow_of_le_one (div_nonneg ht.le ha.le) h1 hα1)
  · exact (min_le_left _ _).trans (Real.one_le_rpow (le_of_not_ge h1) hα.le)

/-- The point mass at the largest gap lies in every polynomial class. -/
theorem diracHalf_mem {α C : ℝ} (hα : 0 < α) (hC : 2^α ≤ C) :
    PowerClass α C (Measure.dirac (⟨1/2,by norm_num,le_rfl⟩ : Gap)) := by
  intro t ht _
  by_cases h2 : 1/2 ≤ t
  · apply measureReal_le_one.trans
    have h1 : 1 ≤ (2*t)^α := Real.one_le_rpow (by linarith) hα.le
    rw [Real.mul_rpow (by norm_num) ht.le] at h1
    have ht' : 0 ≤ t^α := Real.rpow_nonneg ht.le α
    nlinarith
  · have hm : MeasurableSet {d : Gap | (d:ℝ) ≤ t} :=
      measurableSet_le measurable_subtype_coe measurable_const
    have hn : (⟨1/2,by norm_num,le_rfl⟩ : Gap) ∉ {d : Gap | (d:ℝ) ≤ t} := fun h => h2 h
    rw [measureReal_def,Measure.dirac_apply' _ hm,Set.indicator_of_notMem hn]
    simp only [ENNReal.toReal_zero]
    exact mul_nonneg (class_const_pos hC).le (Real.rpow_nonneg ht.le α)

/-! Modulus bounds. -/

theorem modulus_dirac (g : Gap) (h : ℝ) : modulus (Measure.dirac g) h = min 1 (h / (g:ℝ)) := by
  simp only [modulus,integral_dirac,clippedGap]

theorem mass_le_modulus (ν : Measure Gap) [IsProbabilityMeasure ν] {h : ℝ} (hh : 0 ≤ h) :
    ν.real {d : Gap | (d:ℝ) ≤ h} ≤ modulus ν h :=
  mass_le_tail ν hh

theorem modulus_le_inverse (ν : Measure Gap) [IsProbabilityMeasure ν]
    (hi : Integrable (fun d : Gap => (d:ℝ)⁻¹) ν) {h : ℝ} (hh : 0 ≤ h) :
    modulus ν h ≤ h * ∫ d : Gap, (d:ℝ)⁻¹ ∂ν := by
  rw [← integral_const_mul]
  exact integral_mono (integrable_clippedGap ν hh) (hi.const_mul h)
    (fun d => (min_le_right _ _).trans_eq (div_eq_mul_inv _ _))

/-- The inverse moment of a law in the class with `α > 1`. -/
theorem power_inverse {α C : ℝ} (hα : 1 < α) (hC : 2^α ≤ C) (ν : Measure Gap) [IsProbabilityMeasure ν]
    (h : PowerClass α C ν) :
    Integrable (fun d : Gap => (d:ℝ)⁻¹) ν ∧ (∫ d : Gap, (d:ℝ)⁻¹ ∂ν) ≤ α * C^(1/α) / (α - 1) := by
  have hα0 : 0 < α := by linarith
  have hC0 := class_const_pos hC
  have ha := ref_pos (α := α) hC0
  have hm := powerClass_margin hα0 hC h
  have hi := margin_inverse_integrable ν α (C^(-(1/α))) 1 ha one_pos hα hm
  have hI := margin_inverse_integral ν α (C^(-(1/α))) 1 ha one_pos hα hm
  have he : (fun d : Gap => (C^(-(1/α))/(d:ℝ))^(1:ℝ)) = fun d : Gap => C^(-(1/α)) * (d:ℝ)⁻¹ := by
    funext d
    rw [Real.rpow_one,div_eq_mul_inv]
  rw [he] at hi hI
  have hi' : Integrable (fun d : Gap => (d:ℝ)⁻¹) ν := by
    have h2 := hi.const_mul (C^(-(1/α)))⁻¹
    simp only [← mul_assoc,inv_mul_cancel₀ ha.ne',one_mul] at h2
    exact h2
  refine ⟨hi',?_⟩
  rw [integral_const_mul,div_one] at hI
  have hJ : 1 + 1/(α-1) = α/(α-1) := by
    field_simp
    ring
  rw [hJ] at hI
  have hr := ref_mul (α := α) hC0
  have hr0 : 0 < C^(1/α) := Real.rpow_pos_of_pos hC0 _
  calc (∫ d : Gap, (d:ℝ)⁻¹ ∂ν) = C^(1/α) * (C^(-(1/α)) * ∫ d : Gap, (d:ℝ)⁻¹ ∂ν) := by
        rw [← mul_assoc,hr,one_mul]
    _ ≤ C^(1/α) * (α/(α-1)) := mul_le_mul_of_nonneg_left hI hr0.le
    _ = α * C^(1/α) / (α - 1) := by ring

/-! The common blind confidence family. -/

/-- One `(B,δ)` family, chosen before every class parameter: at budget `B` it is
valid at accuracy `ε` for every law below an envelope whose modulus at the
confidence scale is at most `ε/8192`. -/
theorem common_rule : ∃ (R : Type) (_ : MeasurableSpace R) (rule : ℝ → ℝ → AdaptiveEstimator R),
    ∀ (B δ ε : ℝ), 1 ≤ B → 0 < δ → δ ≤ 1/4 →
      ∀ (μ ν : Measure Gap) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν], Within μ ν →
        8192 * modulus μ (confidenceScale B δ) ≤ ε →
        UniformBudget ν (rule B δ) B ∧ UniformConfidence ν (rule B δ) ε δ := by
  obtain ⟨R,mR,rule,h⟩ := blind_confidence_upper
  refine ⟨R,mR,rule,?_⟩
  intro B δ ε hB hδ hδ' μ ν _ _ hw hm
  obtain ⟨hb,hc⟩ := h B δ hB hδ hδ' μ ν hw
  exact ⟨hb,fun q => (failureProbability_mono ν _ q hm).trans (hc q)⟩

end ThresholdHC.MarginClasses
