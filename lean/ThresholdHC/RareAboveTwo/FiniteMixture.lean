import ThresholdHC.RareAboveTwo.MixtureInformation

/-! Finite-distribution form of the rare mixture contraction. -/
noncomputable section
namespace ThresholdHC.RareAboveTwo
open ThresholdHC.Proofs ThresholdHC.Proofs.Transcript ThresholdHC.CriticalEntropy

theorem sum_sqrt_distance {I : Type} [Fintype I] (p q : I → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) (hps : ∑ i, p i = 1) (hqs : ∑ i, q i = 1) :
    (∑ i, (Real.sqrt (p i)-Real.sqrt (q i))^2) = 2*(1-realFiniteAffinity p q) := by
  have he (i) : (Real.sqrt (p i)-Real.sqrt (q i))^2 = p i+q i-2*Real.sqrt (p i*q i) := by
    rw [Real.sqrt_mul (hp i)]
    nlinarith [Real.sq_sqrt (hp i),Real.sq_sqrt (hq i)]
  simp_rw [he]
  rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,hps,hqs]
  unfold realFiniteAffinity
  ring

theorem priorMix_total {I : Type} [Fintype I] (u : ℝ) (p q : I → ℝ)
    (hps : ∑ i, p i = 1) (hqs : ∑ i, q i = 1) : (∑ i, priorMix u (p i) (q i)) = 1 := by
  simp only [priorMix,Finset.sum_add_distrib,← Finset.mul_sum,hps,hqs]
  ring

theorem finite_mixture_distance {I : Type} [Fintype I] (u v : ℝ) (p q : I → ℝ)
    (hu : 0 < u) (huv : u ≤ v) (hv : v ≤ 1/2)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) (hps : ∑ i, p i = 1) (hqs : ∑ i, q i = 1) :
    u*(1-realFiniteAffinity (fun i => priorMix u (p i) (q i)) (fun i => priorMix v (p i) (q i))) ≤
      (v-u)^2*(∑ i, (Real.sqrt (p i)-Real.sqrt (q i))^2) := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => priorMix_sqrt_bound u v (p i) (q i) hu huv hv (hp i) (hq i))
  rw [← Finset.mul_sum,← Finset.mul_sum,sum_sqrt_distance _ _
    (fun i => priorMix_nonneg u _ _ hu.le (by linarith) (hp i) (hq i))
    (fun i => priorMix_nonneg v _ _ (by linarith) (by linarith) (hp i) (hq i))
    (priorMix_total u p q hps hqs) (priorMix_total v p q hps hqs)] at h
  linarith

theorem finite_mixture_kl {I : Type} [Fintype I] (u v : ℝ) (p q : I → ℝ)
    (hu : 0 < u) (huv : u ≤ v) (hv : v ≤ 1/2)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) (hps : ∑ i, p i = 1) (hqs : ∑ i, q i = 1)
    (hzero : ∀ i, p i = 0 ↔ q i = 0) :
    u*(1-realFiniteAffinity (fun i => priorMix u (p i) (q i)) (fun i => priorMix v (p i) (q i))) ≤
      (v-u)^2*klFT p q := by
  have hi (i) : (Real.sqrt (p i)-Real.sqrt (q i))^2 ≤ klTerm (p i) (q i)+q i-p i := by
    by_cases h : p i = 0
    · simp [h,(hzero i).1 h,klTerm]
    · exact sqrt_square_le_kl _ _ (lt_of_le_of_ne (hp i) (Ne.symm h))
        (lt_of_le_of_ne (hq i) (Ne.symm (fun hqz => h ((hzero i).2 hqz))))
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
  rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,hqs,hps,add_sub_cancel_right] at hs
  exact (finite_mixture_distance u v p q hu huv hv hp hq hps hqs).trans
    (mul_le_mul_of_nonneg_left hs (sq_nonneg _))

theorem finite_mixture_activation {I : Type} [Fintype I] (u v : ℝ) (p q : I → ℝ)
    (hu : 0 < u) (huv : u ≤ v) (hv : v ≤ 1/2)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) (hps : ∑ i, p i = 1) (hqs : ∑ i, q i = 1) :
    u*(1-realFiniteAffinity (fun i => priorMix u (p i) (q i)) (fun i => priorMix v (p i) (q i))) ≤
      2*(v-u)^2 := by
  have hs : (∑ i, (Real.sqrt (p i)-Real.sqrt (q i))^2) ≤ 2 := by
    rw [sum_sqrt_distance p q hp hq hps hqs]
    have hn : 0 ≤ realFiniteAffinity p q := Finset.sum_nonneg (fun i _ => Real.sqrt_nonneg _)
    linarith
  have h := (finite_mixture_distance u v p q hu huv hv hp hq hps hqs).trans
    (mul_le_mul_of_nonneg_left hs (sq_nonneg _))
  nlinarith only [h]

end ThresholdHC.RareAboveTwo
