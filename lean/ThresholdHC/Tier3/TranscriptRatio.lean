import ThresholdHC.Proofs.Tier2.TranscriptLikelihood

noncomputable section
namespace ThresholdHC.Tier3
open ThresholdHC ThresholdHC.Proofs

theorem transcriptLaw_le_of_prior_ratio {m n : ℕ}
    (pol : List Bool → Option (Fin m)) (d q r : Fin m → ℝ) (K : ℝ)
    (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1/2)
    (_hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (hr : ∀ i, 0 ≤ r i ∧ r i ≤ 1) (_hK : 0 ≤ K)
    (hqt : ∀ i, r i ≤ K * q i)
    (hqf : ∀ i, 1-r i ≤ K * (1-q i)) (ω : Fin n → Option Bool) :
    transcriptLaw pol d r ω ≤ K^m * transcriptLaw pol d q ω := by
  have hw (s : Fin m → Bool) :
      (∏ i, if s i then r i else 1-r i) ≤
        K^m * (∏ i, if s i then q i else 1-q i) := by
    calc
      _ ≤ ∏ i : Fin m, K * (if s i then q i else 1-q i) := by
        apply Finset.prod_le_prod₀
        · intro i hi
          split_ifs <;> linarith [(hr i).1, (hr i).2]
        · intro i hi
          split_ifs
          · exact hqt i
          · exact hqf i
      _ = _ := by rw [Finset.prod_mul_distrib]; simp
  unfold transcriptLaw
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s hs
  have hp : 0 ≤ pathProb pol (fun i => 1/2 + if s i then d i else -d i) ω := by
    apply pathProb_nonneg
    intro i
    split_ifs <;> constructor <;> linarith [(hd i).1, (hd i).2]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hw s) hp

theorem transcriptLaw_minus_le_plus {m n : ℕ}
    (pol : List Bool → Option (Fin m)) (d η : Fin m → ℝ)
    (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1/2)
    (hη : ∀ i, 0 ≤ η i ∧ η i ≤ 1/8) (ω : Fin n → Option Bool) :
    transcriptLaw pol d (fun i => 1/2-η i) ω ≤
      (5/3:ℝ)^m * transcriptLaw pol d (fun i => 1/2+η i) ω := by
  apply transcriptLaw_le_of_prior_ratio pol d _ _ (5/3) hd
  · intro i; constructor <;> linarith [(hη i).1,(hη i).2]
  · intro i; constructor <;> linarith [(hη i).1,(hη i).2]
  · norm_num
  · intro i; linarith [(hη i).1,(hη i).2]
  · intro i; linarith [(hη i).1,(hη i).2]

theorem transcriptLaw_plus_le_minus {m n : ℕ}
    (pol : List Bool → Option (Fin m)) (d η : Fin m → ℝ)
    (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1/2)
    (hη : ∀ i, 0 ≤ η i ∧ η i ≤ 1/8) (ω : Fin n → Option Bool) :
    transcriptLaw pol d (fun i => 1/2+η i) ω ≤
      (5/3:ℝ)^m * transcriptLaw pol d (fun i => 1/2-η i) ω := by
  apply transcriptLaw_le_of_prior_ratio pol d _ _ (5/3) hd
  · intro i; constructor <;> linarith [(hη i).1,(hη i).2]
  · intro i; constructor <;> linarith [(hη i).1,(hη i).2]
  · norm_num
  · intro i; linarith [(hη i).1,(hη i).2]
  · intro i; linarith [(hη i).1,(hη i).2]

end ThresholdHC.Tier3
