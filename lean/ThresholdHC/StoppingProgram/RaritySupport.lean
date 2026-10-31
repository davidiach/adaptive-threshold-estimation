import ThresholdHC.StoppingProgram.RarityMultiplier

/-! The attained scalar upper-tail formula for the original rarity support
function, without a finite-support or atomlessness assumption. -/

noncomputable section
open MeasureTheory

namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 (Gap SignLaw signMean)
open ThresholdHC.RareAboveTwo

theorem integrable_sign_prior (μ : Measure Gap) [IsFiniteMeasure μ] (q : SignLaw) : Integrable q.val μ := by
  apply (integrable_const (1:ℝ)).mono' q.property.1.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun d => by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (q.property.2 d).1] using (q.property.2 d).2)

def upperLevelPrior (f : Gap → ℝ) (hf : Measurable f) (ell : ℝ) : SignLaw :=
  ⟨fun d => if ell < f d then 1 else 0,
    Measurable.ite (measurableSet_lt measurable_const hf) measurable_const measurable_const,
    fun d => by dsimp only; split_ifs <;> norm_num⟩

theorem prior_excess_integral (μ : Measure Gap) [IsFiniteMeasure μ] (q : SignLaw)
    (f : Gap → ℝ) (hf : Integrable f μ) (ell : ℝ) :
    (∫ d, q.val d*f d ∂μ)-ell*signMean μ q.val = ∫ d, q.val d*(f d-ell) ∂μ := by
  rw [show (fun d => q.val d*(f d-ell)) = (fun d => q.val d*f d-ell*q.val d) by funext d; ring]
  rw [integral_sub (integrable_prior_function μ q hf) ((integrable_sign_prior μ q).const_mul ell),
    integral_const_mul]
  rfl

theorem upperLevelPrior_excess (μ : Measure Gap) [IsFiniteMeasure μ]
    (f : Gap → ℝ) (hf : Measurable f) (hi : Integrable f μ) (ell : ℝ) :
    (∫ d, (upperLevelPrior f hf ell).val d*f d ∂μ)-ell*signMean μ (upperLevelPrior f hf ell).val =
      ∫ d, max (f d-ell) 0 ∂μ := by
  rw [prior_excess_integral μ _ f hi ell]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun d => by
    change (if ell < f d then (1:ℝ) else 0)*(f d-ell) = max (f d-ell) 0
    by_cases hd : ell < f d
    · rw [ite_eq_left hd,one_mul,max_eq_left (by linarith)]
    · rw [ite_eq_right hd,zero_mul,max_eq_right (by linarith)])

theorem prior_function_upper_tail (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ : ℝ} (f : Gap → ℝ) (hi : Integrable f μ) (q : SignLaw) (hq : RarePrior μ ρ q)
    {ell : ℝ} (hell : 0 ≤ ell) :
    (∫ d, q.val d*f d ∂μ) ≤ ρ*ell+∫ d, max (f d-ell) 0 ∂μ := by
  have hpoint (d : Gap) : q.val d*(f d-ell) ≤ max (f d-ell) 0 := by
    have hq0 := (q.property.2 d).1
    have hq1 := (q.property.2 d).2
    by_cases hd : 0 ≤ f d-ell
    · rw [max_eq_left hd]
      nlinarith
    · rw [max_eq_right (le_of_not_ge hd)]
      exact mul_nonpos_of_nonneg_of_nonpos hq0 (le_of_not_ge hd)
  have hI := integral_mono (integrable_prior_function μ q (hi.sub (integrable_const ell)))
    (hi.sub (integrable_const ell)).pos_part hpoint
  simp only [Pi.sub_apply] at hI
  rw [← prior_excess_integral μ q f hi ell] at hI
  have hmass := mul_le_mul_of_nonneg_left hq hell
  nlinarith

theorem rareFunctional_upper_tail (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ : ℝ} (hρ : 0 ≤ ρ) (f : Gap → ℝ) (hf : MemLp f 2 μ)
    {ell : ℝ} (hell : 0 ≤ ell) :
    rareFunctional μ ρ f ≤ ρ*ell+∫ d, max (f d-ell) 0 ∂μ := by
  obtain ⟨q,hq,he⟩ := rareFunctional_attained μ hρ f hf
  rw [he]
  exact prior_function_upper_tail μ f (hf.integrable (by norm_num)) q hq hell

theorem rarity_support_formula (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ : ℝ} (hρ : 0 < ρ) (f : Gap → ℝ) (hf : Measurable f) (hLp : MemLp f 2 μ) :
    (∃ q : SignLaw, RarePrior μ ρ q ∧ rareFunctional μ ρ f = ∫ d, q.val d*f d ∂μ) ∧
    ∃ ell : ℝ, 0 ≤ ell ∧ rareFunctional μ ρ f = ρ*ell+∫ d, max (f d-ell) 0 ∂μ ∧
      ∀ t : ℝ, 0 ≤ t → rareFunctional μ ρ f ≤ ρ*t+∫ d, max (f d-t) 0 ∂μ := by
  refine ⟨rareFunctional_attained μ hρ.le f hLp,?_⟩
  obtain ⟨ell,hell,hh⟩ := rarity_function_multiplier μ hρ f hLp
  have hu := hh (upperLevelPrior f hf ell)
  rw [upperLevelPrior_excess μ f hf (hLp.integrable (by norm_num)) ell] at hu
  have hl := rareFunctional_upper_tail μ hρ.le f hLp hell
  refine ⟨ell,hell,?_,fun t ht => rareFunctional_upper_tail μ hρ.le f hLp ht⟩
  linarith

theorem rarity_support_formula_bounded_above (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ M : ℝ} (hρ : 0 < ρ) (hM : 0 ≤ M) (f : Gap → ℝ) (hf : Measurable f)
    (hLp : MemLp f 2 μ) (hb : ∀ᵐ d ∂μ, f d ≤ M) :
    (∃ q : SignLaw, RarePrior μ ρ q ∧ rareFunctional μ ρ f = ∫ d, q.val d*f d ∂μ) ∧
    ∃ ell : ℝ, 0 ≤ ell ∧ ell ≤ M ∧
      rareFunctional μ ρ f = ρ*ell+∫ d, max (f d-ell) 0 ∂μ ∧
      ∀ t : ℝ, 0 ≤ t → rareFunctional μ ρ f ≤ ρ*t+∫ d, max (f d-t) 0 ∂μ := by
  obtain ⟨hq,ell,hell,he,hmin⟩ := rarity_support_formula μ hρ f hf hLp
  have hMzero : (∫ d, max (f d-M) 0 ∂μ) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hb] with d hd
    change max (f d-M) 0 = 0
    rw [max_eq_right (by linarith)]
  have hbound : ell ≤ M := by
    by_contra hn
    have hellM : M < ell := lt_of_not_ge hn
    have hzero : (∫ d, max (f d-ell) 0 ∂μ) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hb] with d hd
      change max (f d-ell) 0 = 0
      rw [max_eq_right (by linarith)]
    rw [hzero,add_zero] at he
    have hh := hmin M hM
    rw [hMzero,add_zero,he] at hh
    nlinarith
  exact ⟨hq,ell,hell,hbound,he,hmin⟩

theorem bounded_rarity_support_formula (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ M : ℝ} (hρ : 0 < ρ) (hM : 0 ≤ M) (f : Gap → ℝ) (hf : Measurable f)
    (hb : ∀ d, ‖f d‖ ≤ M) :
    (∃ q : SignLaw, RarePrior μ ρ q ∧ rareFunctional μ ρ f = ∫ d, q.val d*f d ∂μ) ∧
    ∃ ell : ℝ, 0 ≤ ell ∧ ell ≤ M ∧
      rareFunctional μ ρ f = ρ*ell+∫ d, max (f d-ell) 0 ∂μ ∧
      ∀ t : ℝ, 0 ≤ t → rareFunctional μ ρ f ≤ ρ*t+∫ d, max (f d-t) 0 ∂μ := by
  exact rarity_support_formula_bounded_above μ hρ hM f hf
    (MemLp.of_bound hf.aestronglyMeasurable M (Filter.Eventually.of_forall hb))
    (Filter.Eventually.of_forall (fun d => (le_abs_self (f d)).trans (by simpa only [Real.norm_eq_abs] using hb d)))

end ThresholdHC.StoppingProgram
