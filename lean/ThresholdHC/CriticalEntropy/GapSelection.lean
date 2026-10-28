import Mathlib

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThresholdHC.CriticalEntropy

/-- A bounded measurable bad-gap set in an atomless real law can be trimmed to
any prescribed smaller mass. This supplies the population perturbations used
by the capped global class, rather than assuming a pointwise cap on q. -/
theorem exists_subset_real_measure {μ : Measure ℝ} [IsFiniteMeasure μ]
    [NullSingletonClass μ] (B : Set ℝ) (hB : MeasurableSet B)
    (a b r : ℝ) (hab : a ≤ b) (hbounded : B ⊆ Ioc a b)
    (hr₀ : 0 ≤ r) (hrB : r ≤ μ.real B) :
    ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ B ∧ μ.real E = r := by
  let F : ℝ → ℝ := fun t => ∫ _ in Iic t, (1 : ℝ) ∂μ.restrict B
  have hF (t : ℝ) : F t = μ.real (Iic t ∩ B) := by
    simp [F, Measure.real]
  have hi : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Iic b) (μ.restrict B) := integrable_const 1
  have hc : ContinuousOn F (Icc a b) :=
    hi.continuousOn_Iic_primitive_Iic.mono Icc_subset_Iic_self
  have ha : Iic a ∩ B = ∅ := by
    ext x
    simp only [mem_inter_iff,mem_Iic,mem_empty_iff_false,iff_false,not_and]
    intro hx hxb
    exact (not_lt_of_ge hx) (hbounded hxb).1
  have hb : Iic b ∩ B = B := inter_eq_right.mpr (fun x hx => (hbounded hx).2)
  have hFa : F a = 0 := by rw [hF,ha]; simp
  have hFb : F b = μ.real B := by rw [hF,hb]
  obtain ⟨t,ht,he⟩ := intermediate_value_Icc hab hc
    (show r ∈ Icc (F a) (F b) by rw [hFa,hFb]; exact ⟨hr₀,hrB⟩)
  exact ⟨Iic t ∩ B,measurableSet_Iic.inter hB,inter_subset_right,(hF t).symm.trans he⟩

theorem bad_set_mass_lt_of_integral_lower {μ : Measure ℝ} [IsFiniteMeasure μ]
    [NullSingletonClass μ] (B : Set ℝ) (hB : MeasurableSet B)
    (a b r c k : ℝ) (hab : a ≤ b) (hbounded : B ⊆ Ioc a b) (hr : 0 ≤ r)
    (f : ℝ → ℝ) (hf : Measurable f) (hint : Integrable f μ) (hck : c*r < k)
    (hlower : ∀ E : Set ℝ, MeasurableSet E → E ⊆ B → μ.real E = r →
      k ≤ ∫ x in E, f x ∂μ) :
    μ.real (B ∩ {x | f x ≤ c}) < r := by
  by_contra hn
  have hbad : MeasurableSet (B ∩ {x | f x ≤ c}) :=
    hB.inter (measurableSet_le hf measurable_const)
  obtain ⟨E,hE,hEB,hEr⟩ := exists_subset_real_measure (B ∩ {x | f x ≤ c}) hbad
    a b r hab (fun x hx => hbounded hx.1) hr (not_lt.mp hn)
  have he : E ⊆ B := hEB.trans inter_subset_left
  have hle : (∫ x in E, f x ∂μ) ≤ ∫ _ in E, c ∂μ := by
    apply integral_mono_ae hint.integrableOn (integrable_const c)
    filter_upwards [ae_restrict_mem hE] with x hx using (hEB hx).2
  have hconst : (∫ _ in E, c ∂μ) = c*r := by
    simp [hEr, mul_comm]
  rw [hconst] at hle
  exact (not_le_of_gt hck) ((hlower E hE he hEr).trans hle)

theorem bad_set_mass_lt_of_integral_upper {μ : Measure ℝ} [IsFiniteMeasure μ]
    [NullSingletonClass μ] (B : Set ℝ) (hB : MeasurableSet B)
    (a b r c k : ℝ) (hab : a ≤ b) (hbounded : B ⊆ Ioc a b) (hr : 0 ≤ r)
    (f : ℝ → ℝ) (hf : Measurable f) (hint : Integrable f μ) (hck : k < c*r)
    (hupper : ∀ E : Set ℝ, MeasurableSet E → E ⊆ B → μ.real E = r →
      (∫ x in E, f x ∂μ) ≤ k) :
    μ.real (B ∩ {x | c ≤ f x}) < r := by
  have h := bad_set_mass_lt_of_integral_lower B hB a b r (-c) (-k) hab hbounded hr
    (fun x => -f x) hf.neg hint.neg (by linarith) (by
      intro E hE hEB hEr
      rw [integral_neg]
      exact neg_le_neg (hupper E hE hEB hEr))
  simpa only [neg_le_neg_iff] using h

end ThresholdHC.CriticalEntropy
