import ThresholdHC.CriticalEntropy.FiniteSaddle

noncomputable section
open Set
namespace ThresholdHC.CriticalEntropy

theorem realFiniteAffinity_self {I : Type} [Fintype I] (p : I → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) : realFiniteAffinity p p = 1 := by
  unfold realFiniteAffinity
  simpa only [← sq,Real.sqrt_sq (hp _)] using hs

theorem finiteRepeatedObjective_diagonal {I : Type} [Fintype I] [Nonempty I]
    (p : I → ℝ) (hp : ∀ i, 0 < p i) (hs : ∑ i, p i = 1)
    (n : ℕ) (u : I → ℝ) (a : ℝ) (ha : 0 < a) :
    2*a*Real.log 2 ≤ finiteRepeatedObjective p p 0 n u a := by
  have hl := finite_log_partition_lower p p (fun i => u i/a) hp hp
  rw [realFiniteAffinity_self p (fun i => (hp i).le) hs,Real.log_one,mul_zero] at hl
  have he : -(fun i => u i/a) = (fun i => -u i/a) := by funext i; simp only [Pi.neg_apply,neg_div]
  rw [he] at hl
  have hn := mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) hl
  have hna := mul_nonneg ha.le hn
  unfold finiteRepeatedObjective
  nlinarith

/-- Center a uniform saddle certificate using attained extrema on the actual
compact image. The conclusion is a pair of uniform log-moment bounds. -/
theorem finite_saddle_centering {E I : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype I] [Nonempty I]
    (X : Set E) (hXn : X.Nonempty) (hXc : IsCompact X)
    (p : E →ᵃ[ℝ] (I → ℝ)) (ell : E →ᵃ[ℝ] ℝ)
    (hpc : Continuous p) (helc : Continuous ell)
    (hp : ∀ x ∈ X, ∀ i, 0 < p x i) (hs : ∀ x ∈ X, ∑ i, p x i = 1)
    (n : ℕ) (R : ℝ) (u : I → ℝ) (a : ℝ) (ha : 0 < a)
    (hcert : ∀ x ∈ X, ∀ y ∈ X,
      finiteRepeatedObjective (p x) (p y) (ell x-ell y) n u a < 2*R) :
    a ≤ R/Real.log 2 ∧ ∃ c : ℝ, ∀ x ∈ X,
      (c-ell x)/a+(n : ℝ)*Real.log (finitePartition (p x) (fun i => u i/a)) ≤ R/a-Real.log 2 ∧
      (ell x-c)/a+(n : ℝ)*Real.log (finitePartition (p x) (fun i => -u i/a)) ≤ R/a-Real.log 2 := by
  obtain ⟨x₀,hx₀⟩ := hXn
  have hdiag := finiteRepeatedObjective_diagonal (p x₀) (hp x₀ hx₀) (hs x₀ hx₀) n u a ha
  have hdiag' := hcert x₀ hx₀ x₀ hx₀
  rw [sub_self] at hdiag'
  have has : a*Real.log 2 < R := by linarith
  refine ⟨(le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr has.le,?_⟩
  let U : E → ℝ := fun x => ell x+(n : ℝ)*a*Real.log (finitePartition (p x) (fun i => -u i/a))
  let V : E → ℝ := fun x => -ell x+(n : ℝ)*a*Real.log (finitePartition (p x) (fun i => u i/a))
  have hminus : ContinuousOn (fun x => Real.log (finitePartition (p x) (fun i => -u i/a))) X :=
    (finitePartition_continuous.comp (hpc.prodMk continuous_const)).continuousOn.log
      (fun x hx => (finitePartition_pos _ _ (hp x hx)).ne')
  have hplus : ContinuousOn (fun x => Real.log (finitePartition (p x) (fun i => u i/a))) X :=
    (finitePartition_continuous.comp (hpc.prodMk continuous_const)).continuousOn.log
      (fun x hx => (finitePartition_pos _ _ (hp x hx)).ne')
  have hUc : ContinuousOn U X := helc.continuousOn.add (hminus.const_mul ((n : ℝ)*a))
  have hVc : ContinuousOn V X := helc.neg.continuousOn.add (hplus.const_mul ((n : ℝ)*a))
  obtain ⟨xU,hxU,hU⟩ := hXc.exists_isMaxOn ⟨x₀,hx₀⟩ hUc
  obtain ⟨xV,hxV,hV⟩ := hXc.exists_isMaxOn ⟨x₀,hx₀⟩ hVc
  have huv : U xU+V xV+2*a*Real.log 2 < 2*R := by
    have h := hcert xU hxU xV hxV
    dsimp [U,V,finiteRepeatedObjective] at h ⊢
    nlinarith
  let c := (U xU-V xV)/2
  refine ⟨c,?_⟩
  intro x hx
  have hu := hU hx
  have hv := hV hx
  have hrawP : c-ell x+(n : ℝ)*a*Real.log (finitePartition (p x) (fun i => u i/a)) ≤ R-a*Real.log 2 := by
    dsimp [V,c] at hv ⊢
    linarith
  have hrawM : ell x-c+(n : ℝ)*a*Real.log (finitePartition (p x) (fun i => -u i/a)) ≤ R-a*Real.log 2 := by
    dsimp [U,c] at hu ⊢
    linarith
  constructor
  · calc
      _ = (c-ell x+(n : ℝ)*a*Real.log (finitePartition (p x) (fun i => u i/a)))/a := by field_simp
      _ ≤ (R-a*Real.log 2)/a := div_le_div_of_nonneg_right hrawP ha.le
      _ = _ := by field_simp
  · calc
      _ = (ell x-c+(n : ℝ)*a*Real.log (finitePartition (p x) (fun i => -u i/a)))/a := by field_simp
      _ ≤ (R-a*Real.log 2)/a := div_le_div_of_nonneg_right hrawM ha.le
      _ = _ := by field_simp

end ThresholdHC.CriticalEntropy
