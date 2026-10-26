import ThresholdHC.Proofs.Tier2.TranscriptLikelihood
import ThresholdHC.Proofs.Tier2.TranscriptScalar
import ThresholdHC.Proofs.Tier2.InformationCore

/-!
Stopped-transcript information bounds.

The proof conditions on each finite transcript prefix, identifies the posterior
of the queried coin, and applies the uniform one-query KL bound. Induction over
padded transcript length charges divergence only for actual queries. Finite
data processing then gives the testing lower bound.
-/

noncomputable section
namespace ThresholdHC.Proofs
open Transcript

theorem mixPredict_weighted {d q A B : ℝ} (hm : mixMass q A B ≠ 0) :
    mixMass q A B * mixPredict d q A B =
      q*A*(1/2+d)+(1-q)*B*(1/2-d) := by
  unfold mixPredict pred
  field_simp
  dsimp [mixMass]
  ring

theorem transcriptLaw_predict_true {m n : ℕ} (pol : List Bool → Option (Fin m)) (d q : Fin m → ℝ)
    (ω : Fin n → Option Bool) (i : Fin m) (hi : pol (fullHist ω) = some i)
    (hm : coinMix pol d q ω i ≠ 0) :
    transcriptLaw pol d q (Fin.snoc ω (some true)) = transcriptLaw pol d q ω *
      mixPredict (d i) (q i) (coinLike pol ω i (1/2+d i)) (coinLike pol ω i (1/2-d i)) := by
  rw [transcriptLaw_query pol d q ω i hi, transcriptLaw_split pol d q ω i]
  simp only [obsProb, mul_assoc]
  unfold coinMix at hm ⊢
  change _ = otherMass pol d q ω i * (mixMass _ _ _ * mixPredict _ _ _ _)
  rw [mixPredict_weighted hm]
  ring

theorem transcriptLaw_predict_false {m n : ℕ} (pol : List Bool → Option (Fin m)) (d q : Fin m → ℝ)
    (ω : Fin n → Option Bool) (i : Fin m) (hi : pol (fullHist ω) = some i)
    (hm : coinMix pol d q ω i ≠ 0) :
    transcriptLaw pol d q (Fin.snoc ω (some false)) = transcriptLaw pol d q ω *
      (1-mixPredict (d i) (q i) (coinLike pol ω i (1/2+d i)) (coinLike pol ω i (1/2-d i))) := by
  have ht := transcriptLaw_sum_extensions pol d q ω
  rw [Fintype.sum_option, Fintype.sum_bool, transcriptLaw_query_none pol d q ω i hi,
    transcriptLaw_predict_true pol d q ω i hi hm] at ht
  linarith

theorem transcriptLaw_support {m n : ℕ} (pol : List Bool → Option (Fin m)) (d q r : Fin m → ℝ)
    (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1/2) (hq : ∀ i, 0 < q i ∧ q i < 1)
    (hr : ∀ i, 0 < r i ∧ r i < 1) (ω : Fin n → Option Bool) :
    transcriptLaw pol d q ω = 0 ↔ transcriptLaw pol d r ω = 0 := by
  rw [transcriptLaw_zero_iff pol d q hd hq, transcriptLaw_zero_iff pol d r hd hr]

theorem coinMix_ne_of_pos {m n : ℕ} (pol : List Bool → Option (Fin m)) (d q : Fin m → ℝ)
    (ω : Fin n → Option Bool) (i : Fin m) (ht : 0 < transcriptLaw pol d q ω) :
    coinMix pol d q ω i ≠ 0 := by
  intro hm
  rw [transcriptLaw_split pol d q ω i, hm, mul_zero] at ht
  exact lt_irrefl _ ht

theorem coinLike_sum_pos_of_pos {m n : ℕ} (pol : List Bool → Option (Fin m)) (d q : Fin m → ℝ)
    (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1/2) (ω : Fin n → Option Bool) (i : Fin m)
    (ht : 0 < transcriptLaw pol d q ω) :
    0 < coinLike pol ω i (1/2+d i) + coinLike pol ω i (1/2-d i) := by
  have hA := coinLike_nonneg pol ω i (p:=1/2+d i) (by linarith [(hd i).1]) (by linarith [(hd i).2])
  have hB := coinLike_nonneg pol ω i (p:=1/2-d i) (by linarith [(hd i).2]) (by linarith [(hd i).1])
  by_contra hn
  have hAz : coinLike pol ω i (1/2+d i) = 0 := by linarith
  have hBz : coinLike pol ω i (1/2-d i) = 0 := by linarith
  apply coinMix_ne_of_pos pol d q ω i ht
  simp only [coinMix, hAz, hBz, mul_zero, add_zero]


theorem transcriptLaw_kl_step {m n : ℕ} (pol : List Bool → Option (Fin m)) (d η : Fin m → ℝ)
    (h : ℝ) (hh : 0 < h) (hd : ∀ i, 0 < d i ∧ d i ≤ 1/2)
    (hη : ∀ i, 0 ≤ η i ∧ η i ≤ 1/8) (hdη : ∀ i, d i*η i ≤ h/8)
    (ω : Fin n → Option Bool) :
    (∑ o : Option Bool,
      klTerm (transcriptLaw pol d (fun i => 1/2+η i) (Fin.snoc ω o))
        (transcriptLaw pol d (fun i => 1/2-η i) (Fin.snoc ω o))) ≤
      klTerm (transcriptLaw pol d (fun i => 1/2+η i) ω)
        (transcriptLaw pol d (fun i => 1/2-η i) ω) +
        (128/225)*h^2 * transcriptLaw pol d (fun i => 1/2+η i) ω *
          (if (pol (fullHist ω)).isSome then 1 else 0) := by
  have hd0 i : 0 ≤ d i ∧ d i ≤ 1/2 := ⟨(hd i).1.le, (hd i).2⟩
  have hq i : 0 < (1/2:ℝ)+η i ∧ (1/2:ℝ)+η i < 1 := by constructor <;> linarith [(hη i).1,(hη i).2]
  have hr i : 0 < (1/2:ℝ)-η i ∧ (1/2:ℝ)-η i < 1 := by constructor <;> linarith [(hη i).1,(hη i).2]
  have hpNN : ∀ ω : Fin n → Option Bool, 0 ≤ transcriptLaw pol d (fun i => 1/2+η i) ω :=
    (transcript_law_total m n pol d _ hd0 (fun i => ⟨(hq i).1.le,(hq i).2.le⟩)).1
  have hqNN : ∀ ω : Fin n → Option Bool, 0 ≤ transcriptLaw pol d (fun i => 1/2-η i) ω :=
    (transcript_law_total m n pol d _ hd0 (fun i => ⟨(hr i).1.le,(hr i).2.le⟩)).1
  have hpChild : ∀ ω : Fin (n+1) → Option Bool, 0 ≤ transcriptLaw pol d (fun i => 1/2+η i) ω :=
    (transcript_law_total m (n+1) pol d _ hd0 (fun i => ⟨(hq i).1.le,(hq i).2.le⟩)).1
  by_cases hpZ : transcriptLaw pol d (fun i => 1/2+η i) ω = 0
  · have hcZ : ∀ o : Option Bool, transcriptLaw pol d (fun i => 1/2+η i) (Fin.snoc ω o) = 0 := by
      have hsum := transcriptLaw_sum_extensions pol d (fun i => 1/2+η i) ω
      rw [hpZ] at hsum
      exact fun o => (Finset.sum_eq_zero_iff_of_nonneg (fun o _ => hpChild (Fin.snoc ω o))).mp hsum o (Finset.mem_univ o)
    simp only [hcZ, hpZ, klTerm, zero_mul, mul_zero, Finset.sum_const_zero, zero_add, le_refl]
  have hpP : 0 < transcriptLaw pol d (fun i => 1/2+η i) ω := lt_of_le_of_ne (hpNN ω) (Ne.symm hpZ)
  have hqP : 0 < transcriptLaw pol d (fun i => 1/2-η i) ω := by
    apply lt_of_le_of_ne (hqNN ω)
    intro he
    exact hpZ ((transcriptLaw_support pol d _ _ hd0 hq hr ω).mpr he.symm)
  cases hi : pol (fullHist ω) with
  | none =>
    simp only [transcriptLaw_stop pol d _ ω hi, Option.isSome_none, Bool.false_eq_true,
      ↓reduceIte, mul_zero, add_zero, Fintype.sum_option, Fintype.sum_bool]
    simp [klTerm]
  | some i =>
    have hmP := coinMix_ne_of_pos pol d (fun j => 1/2+η j) ω i hpP
    have hmQ := coinMix_ne_of_pos pol d (fun j => 1/2-η j) ω i hqP
    have hA := coinLike_nonneg pol ω i (p:=1/2+d i) (by linarith [(hd i).1]) (by linarith [(hd i).2])
    have hB := coinLike_nonneg pol ω i (p:=1/2-d i) (by linarith [(hd i).2]) (by linarith [(hd i).1])
    have hAB := coinLike_sum_pos_of_pos pol d (fun j => 1/2+η j) hd0 ω i hpP
    have hpair := mixPredict_pair (hd i).1 (hd i).2 (hη i).1 (hη i).2 hA hB hAB
    have hkl := mixPredict_kl_bound (hd i).1 (hd i).2 (hη i).1 (hη i).2 hh (hdη i) hA hB hAB
    rw [Fintype.sum_option, Fintype.sum_bool,
      transcriptLaw_query_none pol d (fun j => 1/2+η j) ω i hi,
      transcriptLaw_query_none pol d (fun j => 1/2-η j) ω i hi,
      transcriptLaw_predict_true pol d (fun j => 1/2+η j) ω i hi hmP,
      transcriptLaw_predict_true pol d (fun j => 1/2-η j) ω i hi hmQ,
      transcriptLaw_predict_false pol d (fun j => 1/2+η j) ω i hi hmP,
      transcriptLaw_predict_false pol d (fun j => 1/2-η j) ω i hi hmQ]
    simp only [show klTerm 0 0 = 0 from by simp [klTerm], zero_add,
      Option.isSome_some, ↓reduceIte, mul_one]
    rw [binary_mass_chain hpP hqP hpair]
    nlinarith [mul_le_mul_of_nonneg_left hkl hpP.le]


theorem stopped_transcript_kl : ThresholdHC.Targets.stopped_transcript_kl := by
  intro m n pol d η h hh hd hη hdη
  induction n with
  | zero =>
    simp [klFT, transcriptLaw, pathProb, signPrior_total, workOf]
  | succ n ih =>
    calc
      _ = ∑ ω : Fin n → Option Bool, ∑ o : Option Bool,
          klTerm (transcriptLaw pol d (fun i => 1/2+η i) (Fin.snoc ω o))
            (transcriptLaw pol d (fun i => 1/2-η i) (Fin.snoc ω o)) := by
        unfold klFT
        rw [sum_snoc]
        rfl
      _ ≤ ∑ ω : Fin n → Option Bool,
          (klTerm (transcriptLaw pol d (fun i => 1/2+η i) ω)
            (transcriptLaw pol d (fun i => 1/2-η i) ω) +
            (128/225)*h^2 * transcriptLaw pol d (fun i => 1/2+η i) ω *
              (if (pol (fullHist ω)).isSome then 1 else 0)) :=
        Finset.sum_le_sum (fun ω _ => transcriptLaw_kl_step pol d η h hh hd hη hdη ω)
      _ = klFT (transcriptLaw (n:=n) pol d (fun i => 1/2+η i))
          (transcriptLaw (n:=n) pol d (fun i => 1/2-η i)) +
          (128/225)*h^2 * ∑ ω : Fin n → Option Bool,
            transcriptLaw pol d (fun i => 1/2+η i) ω *
              (if (pol (fullHist ω)).isSome then 1 else 0) := by
        rw [Finset.sum_add_distrib]
        simp only [mul_assoc, ← Finset.mul_sum, klFT, klTerm]
      _ ≤ (128/225)*h^2 * (∑ ω : Fin n → Option Bool,
          transcriptLaw pol d (fun i => 1/2+η i) ω * workOf ω) +
          (128/225)*h^2 * ∑ ω : Fin n → Option Bool,
            transcriptLaw pol d (fun i => 1/2+η i) ω *
              (if (pol (fullHist ω)).isSome then 1 else 0) := add_le_add ih le_rfl
      _ = _ := by
        rw [transcriptLaw_work_succ]
        ring


theorem stopped_transcript_testing : ThresholdHC.Targets.stopped_transcript_testing := by
  intro m n pol d η h δ A hh hd hη hdη hδ hδhalf hPA hQA
  have hd0 i : 0 ≤ d i ∧ d i ≤ 1/2 := ⟨(hd i).1.le, (hd i).2⟩
  have hq i : 0 < (1/2:ℝ)+η i ∧ (1/2:ℝ)+η i < 1 := by constructor <;> linarith [(hη i).1,(hη i).2]
  have hr i : 0 < (1/2:ℝ)-η i ∧ (1/2:ℝ)-η i < 1 := by constructor <;> linarith [(hη i).1,(hη i).2]
  have hP := transcript_law_total m n pol d (fun i => 1/2+η i) hd0 (fun i => ⟨(hq i).1.le,(hq i).2.le⟩)
  have hQ := transcript_law_total m n pol d (fun i => 1/2-η i) hd0 (fun i => ⟨(hr i).1.le,(hr i).2.le⟩)
  have hsupp (ω : Fin n → Option Bool) :
      transcriptLaw pol d (fun i => 1/2-η i) ω = 0 →
        transcriptLaw pol d (fun i => 1/2+η i) ω = 0 :=
    (transcriptLaw_support pol d _ _ hd0 hq hr ω).mpr
  have hpAnonneg : 0 ≤ ∑ ω ∈ A, transcriptLaw pol d (fun i => 1/2+η i) ω :=
    Finset.sum_nonneg (fun ω _ => hP.1 ω)
  have hpAle : (∑ ω ∈ A, transcriptLaw pol d (fun i => 1/2+η i) ω) ≤ 1 := by
    calc
      _ ≤ ∑ ω : Fin n → Option Bool, transcriptLaw pol d (fun i => 1/2+η i) ω :=
        Finset.sum_le_univ_sum_of_nonneg hP.1
      _ = 1 := hP.2
  have hqApos : 0 < ∑ ω ∈ A, transcriptLaw pol d (fun i => 1/2-η i) ω := by
    by_contra hn
    have heq : (∑ ω ∈ A, transcriptLaw pol d (fun i => 1/2-η i) ω) = 0 :=
      le_antisymm (not_lt.mp hn) (Finset.sum_nonneg (fun ω _ => hQ.1 ω))
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun ω _ => hQ.1 ω)).mp heq
    have hpzero : (∑ ω ∈ A, transcriptLaw pol d (fun i => 1/2+η i) ω) = 0 :=
      Finset.sum_eq_zero (fun ω hω => hsupp ω (hz ω hω))
    linarith
  have htest := Tier2Information.kl_test_separation δ _ _ hδ hδhalf hpAnonneg hpAle hqApos hQA hPA
  have hdata := kl_data_processing_finite (Fin n → Option Bool)
    (transcriptLaw pol d (fun i => 1/2+η i)) (transcriptLaw pol d (fun i => 1/2-η i))
    A hP.1 hQ.1 hsupp hP.2 hQ.2
  exact htest.trans (hdata.trans (stopped_transcript_kl m n pol d η h hh hd hη hdη))

end ThresholdHC.Proofs
