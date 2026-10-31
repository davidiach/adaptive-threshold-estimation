import ThresholdHC.StoppingProgram.RarityOptimality

/-! Fractional selection at a cutoff atom. Averaging the optimal prior on
that level set preserves its mass and objective, including a null level set. -/

noncomputable section
open MeasureTheory Set

namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 (Gap SignLaw signMean)
open ThresholdHC.RareAboveTwo

def levelPriorMass (μ : Measure Gap) (f : Gap → ℝ) (ell : ℝ) (q : SignLaw) : ℝ :=
  ∫ d, {d | f d = ell}.indicator q.val d ∂μ

def levelAverage (μ : Measure Gap) (f : Gap → ℝ) (ell : ℝ) (q : SignLaw) : ℝ :=
  levelPriorMass μ f ell q/μ.real {d | f d = ell}

theorem levelPriorMass_bounds (μ : Measure Gap) [IsProbabilityMeasure μ]
    (f : Gap → ℝ) (hf : Measurable f) (ell : ℝ) (q : SignLaw) :
    0 ≤ levelPriorMass μ f ell q ∧ levelPriorMass μ f ell q ≤ μ.real {d | f d = ell} := by
  have hs : MeasurableSet {d | f d = ell} := measurableSet_eq_fun hf measurable_const
  constructor
  · apply integral_nonneg
    intro d
    exact indicator_nonneg (fun d _ => (q.property.2 d).1) d
  · have hh := integral_mono ((integrable_sign_prior μ q).indicator hs)
      ((integrable_const (1:ℝ)).indicator hs)
      (fun d => indicator_le_indicator (q.property.2 d).2)
    rw [integral_indicator_const (1:ℝ) hs] at hh
    simp only [smul_eq_mul,mul_one] at hh
    exact hh

theorem levelAverage_properties (μ : Measure Gap) [IsProbabilityMeasure μ]
    (f : Gap → ℝ) (hf : Measurable f) (ell : ℝ) (q : SignLaw) :
    (0 ≤ levelAverage μ f ell q ∧ levelAverage μ f ell q ≤ 1) ∧
      levelAverage μ f ell q*μ.real {d | f d = ell} = levelPriorMass μ f ell q := by
  obtain ⟨ha,hb⟩ := levelPriorMass_bounds μ f hf ell q
  have hm : 0 ≤ μ.real {d | f d = ell} := measureReal_nonneg
  by_cases hm0 : μ.real {d | f d = ell} = 0
  · have ha0 : levelPriorMass μ f ell q = 0 := by rw [hm0] at hb; linarith
    simp [levelAverage,hm0,ha0]
  · have hm' : 0 < μ.real {d | f d = ell} := lt_of_le_of_ne hm (Ne.symm hm0)
    exact ⟨⟨div_nonneg ha hm,(div_le_one hm').mpr hb⟩,div_mul_cancel₀ _ hm0⟩

def fractionalUpperPrior (f : Gap → ℝ) (hf : Measurable f) (ell c : ℝ) (hc : 0 ≤ c ∧ c ≤ 1) : SignLaw :=
  ⟨fun d => if ell < f d then 1 else if f d = ell then c else 0,
    Measurable.ite (measurableSet_lt measurable_const hf) measurable_const
      (Measurable.ite (measurableSet_eq_fun hf measurable_const) measurable_const measurable_const),
    fun d => by dsimp only; split_ifs <;> first | exact hc | norm_num⟩

theorem fractionalUpperPrior_decomposition (f : Gap → ℝ) (hf : Measurable f)
    (ell c : ℝ) (hc : 0 ≤ c ∧ c ≤ 1) (d : Gap) :
    (fractionalUpperPrior f hf ell c hc).val d =
      (upperLevelPrior f hf ell).val d+{d | f d = ell}.indicator (fun _ => c) d := by
  by_cases hhi : ell < f d
  · have hne : f d ≠ ell := ne_of_gt hhi
    simp [fractionalUpperPrior,upperLevelPrior,hhi,hne]
  · by_cases he : f d = ell <;> simp [fractionalUpperPrior,upperLevelPrior,hhi,he]

theorem cutoff_prior_decomposition (μ : Measure Gap) (f : Gap → ℝ) (hf : Measurable f)
    (ell : ℝ) (q : SignLaw)
    (hcut : ∀ᵐ d ∂μ, (ell < f d → q.val d = 1) ∧ (f d < ell → q.val d = 0)) :
    q.val =ᵐ[μ] (fun d => (upperLevelPrior f hf ell).val d+{d | f d = ell}.indicator q.val d) := by
  filter_upwards [hcut] with d hd
  by_cases hhi : ell < f d
  · have hne : f d ≠ ell := ne_of_gt hhi
    simp [upperLevelPrior,hhi,hne,hd.1 hhi]
  · by_cases he : f d = ell
    · simp [upperLevelPrior,he]
    · have hlo : f d < ell := lt_of_le_of_ne (le_of_not_gt hhi) he
      simp [upperLevelPrior,hhi,he,hd.2 hlo]

theorem fractional_cutoff_preserves (μ : Measure Gap) [IsProbabilityMeasure μ]
    (f : Gap → ℝ) (hf : Measurable f) (hi : Integrable f μ) (ell : ℝ) (q : SignLaw)
    (hcut : ∀ᵐ d ∂μ, (ell < f d → q.val d = 1) ∧ (f d < ell → q.val d = 0)) :
    let c := levelAverage μ f ell q
    let r := fractionalUpperPrior f hf ell c (levelAverage_properties μ f hf ell q).1
    signMean μ r.val = signMean μ q.val ∧ (∫ d, r.val d*f d ∂μ) = ∫ d, q.val d*f d ∂μ := by
  let c := levelAverage μ f ell q
  let r := fractionalUpperPrior f hf ell c (levelAverage_properties μ f hf ell q).1
  have hs : MeasurableSet {d | f d = ell} := measurableSet_eq_fun hf measurable_const
  have hmeanQ : signMean μ q.val = signMean μ (upperLevelPrior f hf ell).val+levelPriorMass μ f ell q := by
    rw [signMean,integral_congr_ae (cutoff_prior_decomposition μ f hf ell q hcut),
      integral_add (integrable_sign_prior μ _) ((integrable_sign_prior μ q).indicator hs)]
    rfl
  have hmeanR : signMean μ r.val = signMean μ q.val := by
    rw [hmeanQ]
    change (∫ d, r.val d ∂μ) = _
    rw [integral_congr_ae (Filter.Eventually.of_forall (fractionalUpperPrior_decomposition f hf ell c _)),
      integral_add (integrable_sign_prior μ _) ((integrable_const c).indicator hs),integral_indicator_const c hs]
    simp only [smul_eq_mul]
    rw [mul_comm (μ.real {d | f d = ell}) c,(levelAverage_properties μ f hf ell q).2]
    rfl
  refine ⟨hmeanR,?_⟩
  have he : (∫ d, r.val d*(f d-ell) ∂μ) = ∫ d, q.val d*(f d-ell) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hcut] with d hd
    by_cases hhi : ell < f d
    · simp [r,fractionalUpperPrior,hhi,hd.1 hhi]
    · by_cases heq : f d = ell
      · simp [heq]
      · have hlo : f d < ell := lt_of_le_of_ne (le_of_not_gt hhi) heq
        simp [r,fractionalUpperPrior,hhi,heq,hd.2 hlo]
  rw [← prior_excess_integral μ r f hi ell,← prior_excess_integral μ q f hi ell,hmeanR] at he
  linarith

end ThresholdHC.StoppingProgram
