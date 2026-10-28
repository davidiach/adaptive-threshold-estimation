import ThresholdHC.CriticalEntropy.FiniteRMS
import ThresholdHC.CriticalEntropy.SymmetricReduction

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open Classical
namespace ThresholdHC.CriticalEntropy

/-- A fixed projection onto the common support; its value off the support is
irrelevant under every law to which the projection is applied. -/
def finiteSupportRetraction {I : Type} (s : Set I) (hs : s.Nonempty) (i : I) : s :=
  if h : i ∈ s then ⟨i,h⟩ else ⟨hs.choose,hs.choose_spec⟩

theorem finiteSupportRetraction_val {I : Type} (s : Set I) (hs : s.Nonempty)
    (i : I) (hi : i ∈ s) : (finiteSupportRetraction s hs i).val = i := by
  simp [finiteSupportRetraction,hi]

theorem finite_support_sum {I : Type} [Fintype I] (s : Set I)
    (f : I → ℝ) (hf : ∀ i ∉ s, f i = 0) : (∑ i : s, f i) = ∑ i, f i := by
  classical
  have h := Fintype.sum_subtype_add_sum_subtype (fun i => i ∈ s) f
  have hz : (∑ i : {i // i ∉ s}, f i) = 0 := Finset.sum_eq_zero (fun i hi => hf i i.property)
  rw [hz,add_zero] at h
  exact h

theorem finite_support_map_mass {I : Type} [Fintype I] [MeasurableSpace I]
    [MeasurableSingletonClass I] (μ : Measure I) (s : Set I) (hs : s.Nonempty)
    (hzero : ∀ i ∉ s, μ {i} = 0) (i : s) :
    (μ.map (finiteSupportRetraction s hs)) {i} = μ {i.val} := by
  classical
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton i)]
  apply measure_congr
  have hae : ∀ᵐ j ∂μ, j ∈ s := ae_iff_of_countable.mpr (fun j hj => by
    by_contra hjs
    exact hj (hzero j hjs))
  filter_upwards [hae] with j hj
  simp only [mem_preimage,mem_singleton_iff]
  apply propext
  constructor
  · intro he
    have he' := congrArg Subtype.val he
    simpa only [finiteSupportRetraction_val s hs j hj] using he'
  · intro he
    apply Subtype.ext
    rw [finiteSupportRetraction_val s hs j hj,he]

theorem finite_support_affinity {I : Type} [Fintype I] (s : Set I)
    (p q : I → ℝ) (hp : ∀ i ∉ s, p i = 0) :
    realFiniteAffinity (fun i : s => p i) (fun i : s => q i) = realFiniteAffinity p q := by
  unfold realFiniteAffinity
  apply finite_support_sum s (fun i => Real.sqrt (p i*q i))
  intro i hi
  simp [hp i hi]

theorem evariance_map_measurable {I J : Type} [MeasurableSpace I] [MeasurableSpace J]
    (μ : Measure I) (g : I → J) (f : J → ℝ) (hg : Measurable g) (hf : Measurable f) :
    evariance f (μ.map g) = evariance (f ∘ g) μ := by
  unfold evariance
  rw [integral_map hg.aemeasurable hf.aestronglyMeasurable,
    lintegral_map (by fun_prop) hg]
  rfl

/-- The finite convex comparison on a fixed support, reduced to one observation.
The same score is used for every population, and variance remains extended. -/
theorem finite_convex_one_run {E I : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype I]
    [MeasurableSpace I] [MeasurableSingletonClass I]
    (X : Set E) (hXn : X.Nonempty) (hXc : IsCompact X) (hXv : Convex ℝ X)
    (p : E →ᵃ[ℝ] (I → ℝ)) (ell : E →ᵃ[ℝ] ℝ)
    (hpc : Continuous p) (helc : Continuous ell)
    (s : Set I) (hsn : s.Nonempty)
    (hp : ∀ x ∈ X, ∀ i ∈ s, 0 < p x i)
    (hz : ∀ x ∈ X, ∀ i ∉ s, p x i = 0)
    (hs : ∀ x ∈ X, ∑ i, p x i = 1)
    (n : ℕ) (R : ℝ) (hR : 0 ≤ R)
    (hsep : ∀ x ∈ X, ∀ y ∈ X, 1/2 ≤ (realFiniteAffinity (p x) (p y))^n → ell x-ell y < 2*R) :
    ∃ f : I → ℝ, ∀ x ∈ X, ∀ (μ : Measure I) [IsProbabilityMeasure μ],
      (∀ i, μ.real {i} = p x i) →
      ((∫ i, f i ∂μ)-ell x)^2 ≤ 9*R^2 ∧
      evariance f μ ≤ ENNReal.ofReal ((n : ℝ)*(9*R^2)) := by
  classical
  let : Nonempty s := hsn.to_subtype
  let select : (I → ℝ) →ₗ[ℝ] (s → ℝ) :=
    { toFun := fun v i => v i
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let p' := select.toAffineMap.comp p
  have hp' : Continuous p' := continuous_pi (fun i => (continuous_apply i.val).comp hpc)
  obtain ⟨u,c,huc⟩ := finite_convex_rms_comparison X hXn hXc hXv p' ell hp' helc
    (fun x hx i => hp x hx i i.property)
    (fun x hx => (finite_support_sum s (p x) (hz x hx)).trans (hs x hx)) n R hR
    (fun x hx y hy h => hsep x hx y hy (by
      change 1/2 ≤ (realFiniteAffinity (fun i : s => p x i) (fun i : s => p y i))^n at h
      rwa [finite_support_affinity s (p x) (p y) (hz x hx)] at h))
  let r := finiteSupportRetraction s hsn
  refine ⟨fun i => (n : ℝ)*u (r i)+c,?_⟩
  intro x hx μ _ hm
  let ν := μ.map r
  let : IsProbabilityMeasure ν := inferInstanceAs (IsProbabilityMeasure (μ.map r))
  have hm' (i : s) : ν.real {i} = p' x i := by
    change (μ.map r).real {i} = p x i
    rw [measureReal_def,finite_support_map_mass μ s hsn _ i]
    exact hm i
    intro j hj
    exact (ENNReal.toReal_eq_zero_iff _).mp (by rw [← measureReal_def,hm j,hz x hx j hj])
      |>.resolve_right (measure_ne_top _ _)
  have h := symmetric_one_run_reduction ν u (finite_function_memLp ν u) n c (ell x) (9*R^2)
    (huc x hx ν hm')
  have hmean : (∫ i, (n : ℝ)*u i+c ∂ν) = ∫ i, (n : ℝ)*u (r i)+c ∂μ :=
    integral_map (measurable_of_countable r).aemeasurable
      (measurable_of_countable (fun i => (n : ℝ)*u i+c)).aestronglyMeasurable
  have hvar : evariance (fun i => (n : ℝ)*u i+c) ν =
      evariance (fun i => (n : ℝ)*u (r i)+c) μ :=
    evariance_map_measurable μ r _ (measurable_of_countable r) (measurable_of_countable _)
  rwa [hmean,hvar] at h

end ThresholdHC.CriticalEntropy
