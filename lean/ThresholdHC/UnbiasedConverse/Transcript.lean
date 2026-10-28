import ThresholdHC.Proofs.Tier2.Transcript

/-!
Parameterize the finite-transcript chain by its per-query information bound.
This proof follows the established Tier 2 chain, keeping its zero-mass and
endpoint cases. It supports both directions and the sharp vanishing-tilt limit.
-/

noncomputable section
namespace ThresholdHC.UnbiasedConverse
open ThresholdHC ThresholdHC.Proofs ThresholdHC.Proofs.Transcript

theorem predict_pair {d q r A B : ℝ} (hd : 0 < d) (hd1 : d ≤ 1/2)
    (hq : 0 < q) (hq1 : q < 1) (hr : 0 < r) (hr1 : r < 1)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (_hAB : 0 < A+B) :
    ((0 < mixPredict d q A B ∧ mixPredict d q A B < 1) ∧
      (0 < mixPredict d r A B ∧ mixPredict d r A B < 1)) ∨
      mixPredict d q A B = mixPredict d r A B := by
  by_cases hAz : A = 0
  · right; simp [hAz, mixPredict_zero_left]
  by_cases hBz : B = 0
  · right
    rw [hBz, mixPredict_zero_right hq.ne' hAz, mixPredict_zero_right hr.ne' hAz]
  exact Or.inl ⟨mixPredict_interior hd hd1 hq hq1 (lt_of_le_of_ne hA (Ne.symm hAz))
    (lt_of_le_of_ne hB (Ne.symm hBz)),
    mixPredict_interior hd hd1 hr hr1 (lt_of_le_of_ne hA (Ne.symm hAz))
    (lt_of_le_of_ne hB (Ne.symm hBz))⟩

theorem transcript_kl_step {m n : ℕ} (pol : List Bool → Option (Fin m)) (d q r : Fin m → ℝ)
    (C : ℝ) (hd : ∀ i, 0 < d i ∧ d i ≤ 1/2)
    (hq : ∀ i, 0 < q i ∧ q i < 1) (hr : ∀ i, 0 < r i ∧ r i < 1)
    (hstep : ∀ i A B, 0 ≤ A → 0 ≤ B → 0 < A+B →
      klB (mixPredict (d i) (q i) A B) (mixPredict (d i) (r i) A B) ≤ C)
    (ω : Fin n → Option Bool) :
    (∑ o : Option Bool,
      klTerm (transcriptLaw pol d q (Fin.snoc ω o))
        (transcriptLaw pol d r (Fin.snoc ω o))) ≤
      klTerm (transcriptLaw pol d q ω)
        (transcriptLaw pol d r ω) +
        C * transcriptLaw pol d q ω *
          (if (pol (fullHist ω)).isSome then 1 else 0) := by
  have hd0 i : 0 ≤ d i ∧ d i ≤ 1/2 := ⟨(hd i).1.le, (hd i).2⟩
  have hpNN : ∀ ω : Fin n → Option Bool, 0 ≤ transcriptLaw pol d q ω :=
    (transcript_law_total m n pol d _ hd0 (fun i => ⟨(hq i).1.le,(hq i).2.le⟩)).1
  have hqNN : ∀ ω : Fin n → Option Bool, 0 ≤ transcriptLaw pol d r ω :=
    (transcript_law_total m n pol d _ hd0 (fun i => ⟨(hr i).1.le,(hr i).2.le⟩)).1
  have hpChild : ∀ ω : Fin (n+1) → Option Bool, 0 ≤ transcriptLaw pol d q ω :=
    (transcript_law_total m (n+1) pol d _ hd0 (fun i => ⟨(hq i).1.le,(hq i).2.le⟩)).1
  by_cases hpZ : transcriptLaw pol d q ω = 0
  · have hcZ : ∀ o : Option Bool, transcriptLaw pol d q (Fin.snoc ω o) = 0 := by
      have hsum := transcriptLaw_sum_extensions pol d q ω
      rw [hpZ] at hsum
      exact fun o => (Finset.sum_eq_zero_iff_of_nonneg (fun o _ => hpChild (Fin.snoc ω o))).mp hsum o (Finset.mem_univ o)
    simp only [hcZ, hpZ, klTerm, zero_mul, mul_zero, Finset.sum_const_zero, zero_add, le_refl]
  have hpP : 0 < transcriptLaw pol d q ω := lt_of_le_of_ne (hpNN ω) (Ne.symm hpZ)
  have hqP : 0 < transcriptLaw pol d r ω := by
    apply lt_of_le_of_ne (hqNN ω)
    intro he
    exact hpZ ((transcriptLaw_support pol d _ _ hd0 hq hr ω).mpr he.symm)
  cases hi : pol (fullHist ω) with
  | none =>
    simp only [transcriptLaw_stop pol d _ ω hi, Option.isSome_none, Bool.false_eq_true,
      ↓reduceIte, mul_zero, add_zero, Fintype.sum_option, Fintype.sum_bool]
    simp [klTerm]
  | some i =>
    have hmP := coinMix_ne_of_pos pol d q ω i hpP
    have hmQ := coinMix_ne_of_pos pol d r ω i hqP
    have hA := coinLike_nonneg pol ω i (p:=1/2+d i) (by linarith [(hd i).1]) (by linarith [(hd i).2])
    have hB := coinLike_nonneg pol ω i (p:=1/2-d i) (by linarith [(hd i).2]) (by linarith [(hd i).1])
    have hAB := coinLike_sum_pos_of_pos pol d q hd0 ω i hpP
    have hpair := predict_pair (hd i).1 (hd i).2 (hq i).1 (hq i).2
      (hr i).1 (hr i).2 hA hB hAB
    have hkl := hstep i _ _ hA hB hAB
    rw [Fintype.sum_option, Fintype.sum_bool,
      transcriptLaw_query_none pol d q ω i hi,
      transcriptLaw_query_none pol d r ω i hi,
      transcriptLaw_predict_true pol d q ω i hi hmP,
      transcriptLaw_predict_true pol d r ω i hi hmQ,
      transcriptLaw_predict_false pol d q ω i hi hmP,
      transcriptLaw_predict_false pol d r ω i hi hmQ]
    simp only [show klTerm 0 0 = 0 from by simp [klTerm], zero_add,
      Option.isSome_some, ↓reduceIte, mul_one]
    rw [binary_mass_chain hpP hqP hpair]
    nlinarith [mul_le_mul_of_nonneg_left hkl hpP.le]


theorem transcript_kl_bound (m n : ℕ) (pol : List Bool → Option (Fin m))
    (d q r : Fin m → ℝ) (C : ℝ) (hd : ∀ i, 0 < d i ∧ d i ≤ 1/2)
    (hq : ∀ i, 0 < q i ∧ q i < 1) (hr : ∀ i, 0 < r i ∧ r i < 1)
    (hstep : ∀ i A B, 0 ≤ A → 0 ≤ B → 0 < A+B →
      klB (mixPredict (d i) (q i) A B) (mixPredict (d i) (r i) A B) ≤ C) :
    klFT (transcriptLaw (n:=n) pol d q) (transcriptLaw pol d r) ≤
      C * ∑ w : Fin n → Option Bool, transcriptLaw pol d q w * workOf w := by
  induction n with
  | zero =>
    simp [klFT, transcriptLaw, pathProb, signPrior_total, workOf]
  | succ n ih =>
    calc
      _ = ∑ ω : Fin n → Option Bool, ∑ o : Option Bool,
          klTerm (transcriptLaw pol d q (Fin.snoc ω o))
            (transcriptLaw pol d r (Fin.snoc ω o)) := by
        unfold klFT
        rw [sum_snoc]
        rfl
      _ ≤ ∑ ω : Fin n → Option Bool,
          (klTerm (transcriptLaw pol d q ω)
            (transcriptLaw pol d r ω) +
            C * transcriptLaw pol d q ω *
              (if (pol (fullHist ω)).isSome then 1 else 0)) :=
        Finset.sum_le_sum (fun ω _ => transcript_kl_step pol d q r C hd hq hr hstep ω)
      _ = klFT (transcriptLaw (n:=n) pol d q)
          (transcriptLaw (n:=n) pol d r) +
          C * ∑ ω : Fin n → Option Bool,
            transcriptLaw pol d q ω *
              (if (pol (fullHist ω)).isSome then 1 else 0) := by
        rw [Finset.sum_add_distrib]
        simp only [mul_assoc, ← Finset.mul_sum, klFT, klTerm]
      _ ≤ C * (∑ ω : Fin n → Option Bool,
          transcriptLaw pol d q ω * workOf ω) +
          C * ∑ ω : Fin n → Option Bool,
            transcriptLaw pol d q ω *
              (if (pol (fullHist ω)).isSome then 1 else 0) := add_le_add ih le_rfl
      _ = _ := by
        rw [transcriptLaw_work_succ]
        ring



end ThresholdHC.UnbiasedConverse
