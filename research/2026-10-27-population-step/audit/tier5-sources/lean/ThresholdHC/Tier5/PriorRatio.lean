import ThresholdHC.Proofs.Tier2.TranscriptLikelihood

noncomputable section
namespace ThresholdHC.Tier5
open ThresholdHC ThresholdHC.Proofs

def queriedCoins {m n : ℕ} (pol : List Bool → Option (Fin m))
    (w : Fin n → Option Bool) : Finset (Fin m) :=
  Finset.univ.biUnion fun t => (pol (histBefore w t)).toFinset

theorem queriedCoins_card_le {m n : ℕ} (pol : List Bool → Option (Fin m))
    (w : Fin n → Option Bool) : (queriedCoins pol w).card ≤ n := by
  have h := Finset.card_biUnion_le_card_mul (Finset.univ : Finset (Fin n))
    (fun t => (pol (histBefore w t)).toFinset) 1 (by
      intro t ht
      cases pol (histBefore w t) <;> simp)
  simpa [queriedCoins] using h

theorem coinLike_eq_one_of_not_queried {m n : ℕ}
    (pol : List Bool → Option (Fin m)) (w : Fin n → Option Bool)
    (i : Fin m) (hi : i ∉ queriedCoins pol w) (p : ℝ) : coinLike pol w i p = 1 := by
  apply Finset.prod_eq_one
  intro t ht
  have hn : pol (histBefore w t) ≠ some i := by
    intro he
    apply hi
    simp only [queriedCoins, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨t, by simp [he]⟩
  simp [hn]

/-- Only queried latent signs contribute a prior likelihood ratio. The bound
depends on the observation horizon, not the size of the ambient coin family. -/
theorem finite_transcript_le_of_prior_ratio_horizon {m n : ℕ}
    (pol : List Bool → Option (Fin m)) (d q r : Fin m → ℝ) (K : ℝ)
    (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1/2)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (hr : ∀ i, 0 ≤ r i ∧ r i ≤ 1) (hK : 1 ≤ K)
    (hrt : ∀ i, r i ≤ K * q i) (hrf : ∀ i, 1-r i ≤ K * (1-q i))
    (w : Fin n → Option Bool) :
    transcriptLaw pol d r w ≤ K^n * transcriptLaw pol d q w := by
  classical
  let A : Fin m → ℝ := fun i => coinLike pol w i (1/2+d i)
  let B : Fin m → ℝ := fun i => coinLike pol w i (1/2-d i)
  let F : (Fin m → ℝ) → Fin m → ℝ := fun v i => v i*A i + (1-v i)*B i
  have hA i : 0 ≤ A i := coinLike_nonneg pol w i (by linarith [(hd i).1])
    (by linarith [(hd i).2])
  have hB i : 0 ≤ B i := coinLike_nonneg pol w i (by linarith [(hd i).2])
    (by linarith [(hd i).1])
  have hF v (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1) i : 0 ≤ F v i :=
    add_nonneg (mul_nonneg (hv i).1 (hA i))
      (mul_nonneg (sub_nonneg.mpr (hv i).2) (hB i))
  have hpoint i : F r i ≤ (if i ∈ queriedCoins pol w then K else 1) * F q i := by
    by_cases hi : i ∈ queriedCoins pol w
    · simp only [hi, ↓reduceIte]
      have ha := mul_le_mul_of_nonneg_right (hrt i) (hA i)
      have hb := mul_le_mul_of_nonneg_right (hrf i) (hB i)
      dsimp [F]
      nlinarith
    · have ha : A i = 1 := coinLike_eq_one_of_not_queried pol w i hi _
      have hb : B i = 1 := coinLike_eq_one_of_not_queried pol w i hi _
      simp [F, ha, hb, hi]
  have hprod : (∏ i, F r i) ≤ K^(queriedCoins pol w).card * ∏ i, F q i := by
    calc
      (∏ i, F r i) ≤ ∏ i, (if i ∈ queriedCoins pol w then K else 1) * F q i :=
        Finset.prod_le_prod₀ (fun i _ => hF r hr i) (fun i _ => hpoint i)
      _ = _ := by rw [Finset.prod_mul_distrib]; simp
  have hprod' : (∏ i, F r i) ≤ K^n * ∏ i, F q i :=
    hprod.trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hK (queriedCoins_card_le pol w))
      (Finset.prod_nonneg fun i _ => hF q hq i))
  rw [transcriptLaw_factor, transcriptLaw_factor]
  have hv := pathValidity_nonneg pol w
  change pathValidity pol w * (∏ i, F r i) ≤ K^n * (pathValidity pol w * ∏ i, F q i)
  nlinarith [mul_le_mul_of_nonneg_left hprod' hv]

theorem finite_transcript_plus_le_minus_horizon {m n : ℕ}
    (pol : List Bool → Option (Fin m)) (d η : Fin m → ℝ)
    (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1/2)
    (hη : ∀ i, 0 ≤ η i ∧ η i ≤ 1/8) (w : Fin n → Option Bool) :
    transcriptLaw pol d (fun i => 1/2+η i) w ≤
      (5/3:ℝ)^n * transcriptLaw pol d (fun i => 1/2-η i) w := by
  apply finite_transcript_le_of_prior_ratio_horizon pol d _ _ (5/3) hd
  · intro i; constructor <;> linarith [(hη i).1,(hη i).2]
  · intro i; constructor <;> linarith [(hη i).1,(hη i).2]
  · norm_num
  · intro i; linarith [(hη i).1,(hη i).2]
  · intro i; linarith [(hη i).1,(hη i).2]

theorem finite_transcript_minus_le_plus_horizon {m n : ℕ}
    (pol : List Bool → Option (Fin m)) (d η : Fin m → ℝ)
    (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1/2)
    (hη : ∀ i, 0 ≤ η i ∧ η i ≤ 1/8) (w : Fin n → Option Bool) :
    transcriptLaw pol d (fun i => 1/2-η i) w ≤
      (5/3:ℝ)^n * transcriptLaw pol d (fun i => 1/2+η i) w := by
  apply finite_transcript_le_of_prior_ratio_horizon pol d _ _ (5/3) hd
  · intro i; constructor <;> linarith [(hη i).1,(hη i).2]
  · intro i; constructor <;> linarith [(hη i).1,(hη i).2]
  · norm_num
  · intro i; linarith [(hη i).1,(hη i).2]
  · intro i; linarith [(hη i).1,(hη i).2]

end ThresholdHC.Tier5
