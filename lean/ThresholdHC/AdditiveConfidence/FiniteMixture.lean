import ThresholdHC.ConfidenceLocalization.ConfidenceRate

noncomputable section
namespace ThresholdHC.AdditiveConfidence
open ThresholdHC.CriticalEntropy

theorem finite_affinity_sum {I Z : Type} [Fintype I] [Fintype Z]
    (p q : I → Z → ℝ) (hp : ∀ i z, 0 ≤ p i z) (hq : ∀ i z, 0 ≤ q i z) :
    ∑ i, realFiniteAffinity (p i) (q i) ≤
      realFiniteAffinity (fun z => ∑ i, p i z) (fun z => ∑ i, q i z) := by
  unfold realFiniteAffinity
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro z _
  calc
    _ = ∑ i, Real.sqrt (p i z)*Real.sqrt (q i z) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Real.sqrt_mul (hp i z) _
    _ ≤ Real.sqrt (∑ i, p i z)*Real.sqrt (∑ i, q i z) :=
      Real.sum_sqrt_mul_sqrt_le Finset.univ (fun i => hp i z) (fun i => hq i z)
    _ = _ := (Real.sqrt_mul (Finset.sum_nonneg (fun i _ => hp i z)) _).symm

theorem finite_affinity_scale {Z : Type} [Fintype Z]
    (p q : Z → ℝ) (hp : ∀ z, 0 ≤ p z) (a : ℝ) (ha : 0 ≤ a) :
    realFiniteAffinity (fun z => a*p z) (fun z => a*q z) =
      a*realFiniteAffinity p q := by
  unfold realFiniteAffinity
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [Real.sqrt_mul (mul_nonneg ha (hp z)),sqrt_product_scale a (p z) (q z) ha (hp z)]

theorem finite_affinity_self {Z : Type} [Fintype Z]
    (p : Z → ℝ) (hp : ∀ z, 0 ≤ p z) : realFiniteAffinity p p = ∑ z, p z := by
  unfold realFiniteAffinity
  apply Finset.sum_congr rfl
  intro z _
  rw [← pow_two,Real.sqrt_sq_eq_abs,abs_of_nonneg (hp z)]

/-- The residual component may have any mass and is shared by both endpoints. -/
theorem finite_mixture_loss {I Z : Type} [Fintype I] [Fintype Z]
    (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (p q : I → Z → ℝ)
    (hp : ∀ i z, 0 ≤ p i z) (hq : ∀ i z, 0 ≤ q i z)
    (res : Z → ℝ) (hr : ∀ z, 0 ≤ res z) (hmass : (∑ z, res z)+(∑ i, w i) = 1) :
    1-realFiniteAffinity (fun z => res z+∑ i, w i*p i z) (fun z => res z+∑ i, w i*q i z) ≤
      ∑ i, w i*(1-realFiniteAffinity (p i) (q i)) := by
  let P : Option I → Z → ℝ := fun i => match i with
    | none => res
    | some i => fun z => w i*p i z
  let Q : Option I → Z → ℝ := fun i => match i with
    | none => res
    | some i => fun z => w i*q i z
  have hp' (i : Option I) (z : Z) : 0 ≤ P i z := by
    cases i with
    | none => exact hr z
    | some i => exact mul_nonneg (hw i) (hp i z)
  have hq' (i : Option I) (z : Z) : 0 ≤ Q i z := by
    cases i with
    | none => exact hr z
    | some i => exact mul_nonneg (hw i) (hq i z)
  have h := finite_affinity_sum P Q hp' hq'
  simp only [Fintype.sum_option,P,Q,finite_affinity_self res hr,
    fun i => finite_affinity_scale (p i) (q i) (hp i) (w i) (hw i)] at h
  rw [Finset.sum_congr rfl (fun i _ => by rw [mul_sub,mul_one]),Finset.sum_sub_distrib]
  linarith

end ThresholdHC.AdditiveConfidence
