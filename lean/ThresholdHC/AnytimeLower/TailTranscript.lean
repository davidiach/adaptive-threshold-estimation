
import ThresholdHC.AnytimeLower.TailInformation
import ThresholdHC.Proofs.Tier2.Transcript
import ThresholdHC.Tier5.PriorRatio

noncomputable section
namespace ThresholdHC.AnytimeLower
open ThresholdHC.Proofs ThresholdHC.Proofs.Transcript

/-- Priors may agree at arbitrary gaps, including deterministic observations.
Where they differ, the gap and priors lie in the central small-gap region. -/
def TailContrast (d q r : ℝ) : Prop :=
  q = r ∨ (d ≤ 1/4 ∧ (1/4 ≤ q ∧ q ≤ 3/4) ∧ (1/4 ≤ r ∧ r ≤ 3/4))

theorem tailContrast_ratio {d q r : ℝ} (h : TailContrast d q r)
    (hq : 0 ≤ q ∧ q ≤ 1) (hr : 0 ≤ r ∧ r ≤ 1) :
    q ≤ 3*r ∧ 1-q ≤ 3*(1-r) := by
  rcases h with h | ⟨_,hp,hs⟩
  · subst r
    constructor <;> linarith
  · constructor <;> linarith

theorem mixPredict_eq_head (d q A B : ℝ) :
    mixPredict d q A B = predictiveHead q A B d := by
  unfold mixPredict pred mixMass predictiveHead posteriorMass
  ring

theorem tail_transcript_step {m n : ℕ} (pol : List Bool → Option (Fin m))
    (d q r : Fin m → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1/2)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (hr : ∀ i, 0 ≤ r i ∧ r i ≤ 1)
    (hcentral : ∀ i, TailContrast (d i) (q i) (r i))
    (hcontrast : ∀ i, d i*|q i-r i| ≤ ε/32)
    (ω : Fin n → Option Bool) :
    (∑ o : Option Bool, klTerm (transcriptLaw pol d q (Fin.snoc ω o))
      (transcriptLaw pol d r (Fin.snoc ω o))) ≤
    klTerm (transcriptLaw pol d q ω) (transcriptLaw pol d r ω) +
      ε^2 * transcriptLaw pol d q ω := by
  have hpNN := (transcript_law_total m n pol d q hd hq).1
  have hqNN := (transcript_law_total m n pol d r hd hr).1
  have hpChild := (transcript_law_total m (n+1) pol d q hd hq).1
  by_cases hpZ : transcriptLaw pol d q ω = 0
  · have hcZ : ∀ o : Option Bool, transcriptLaw pol d q (Fin.snoc ω o) = 0 := by
      have hs := transcriptLaw_sum_extensions pol d q ω
      rw [hpZ] at hs
      exact fun o => (Finset.sum_eq_zero_iff_of_nonneg
        (fun o _ => hpChild (Fin.snoc ω o))).mp hs o (Finset.mem_univ o)
    simp [hcZ,hpZ,klTerm]
  have hpP : 0 < transcriptLaw pol d q ω := lt_of_le_of_ne (hpNN ω) (Ne.symm hpZ)
  have hqP : 0 < transcriptLaw pol d r ω := by
    have hrat := Tier5.finite_transcript_le_of_prior_ratio_horizon pol d r q 3
      hd hr hq (by norm_num)
      (fun i => (tailContrast_ratio (hcentral i) (hq i) (hr i)).1)
      (fun i => (tailContrast_ratio (hcentral i) (hq i) (hr i)).2) ω
    by_contra hh
    have hz : transcriptLaw pol d r ω = 0 := le_antisymm (not_lt.mp hh) (hqNN ω)
    rw [hz,mul_zero] at hrat
    exact (not_le.mpr hpP) hrat
  cases hi : pol (fullHist ω) with
  | none =>
    simp only [transcriptLaw_stop pol d _ ω hi,Fintype.sum_option,Fintype.sum_bool]
    simpa [klTerm] using
      (le_add_of_nonneg_right (mul_nonneg (sq_nonneg ε) hpP.le) :
        klTerm (transcriptLaw pol d q ω) (transcriptLaw pol d r ω) ≤
          klTerm (transcriptLaw pol d q ω) (transcriptLaw pol d r ω) + ε^2*transcriptLaw pol d q ω)
  | some i =>
    have hmP := coinMix_ne_of_pos pol d q ω i hpP
    have hmQ := coinMix_ne_of_pos pol d r ω i hqP
    have hA := coinLike_nonneg pol ω i (p:=1/2+d i)
      (by linarith [(hd i).1]) (by linarith [(hd i).2])
    have hB := coinLike_nonneg pol ω i (p:=1/2-d i)
      (by linarith [(hd i).2]) (by linarith [(hd i).1])
    have hAB := coinLike_sum_pos_of_pos pol d q hd ω i hpP
    let A := coinLike pol ω i (1/2+d i)
    let B := coinLike pol ω i (1/2-d i)
    have hpair : ((0 < mixPredict (d i) (q i) A B ∧ mixPredict (d i) (q i) A B < 1) ∧
        (0 < mixPredict (d i) (r i) A B ∧ mixPredict (d i) (r i) A B < 1)) ∨
        mixPredict (d i) (q i) A B = mixPredict (d i) (r i) A B := by
      rcases hcentral i with he | ⟨hdi,hqi,hri⟩
      · exact Or.inr (by rw [he])
      · left
        rw [mixPredict_eq_head,mixPredict_eq_head]
        have hp := predictiveHead_bounds hqi hA hB hAB ⟨(hd i).1,hdi⟩
        have hs := predictiveHead_bounds hri hA hB hAB ⟨(hd i).1,hdi⟩
        exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩
    have hkl : klB (mixPredict (d i) (q i) A B) (mixPredict (d i) (r i) A B) ≤ ε^2 := by
      rcases hcentral i with he | ⟨hdi,hqi,hri⟩
      · rw [he,klB_self]
        exact sq_nonneg ε
      · rw [mixPredict_eq_head,mixPredict_eq_head]
        exact predictiveHead_kl hqi hri hA hB hAB ⟨(hd i).1,hdi⟩ hε (hcontrast i)
    rw [Fintype.sum_option,Fintype.sum_bool,
      transcriptLaw_query_none pol d q ω i hi,transcriptLaw_query_none pol d r ω i hi,
      transcriptLaw_predict_true pol d q ω i hi hmP,
      transcriptLaw_predict_true pol d r ω i hi hmQ,
      transcriptLaw_predict_false pol d q ω i hi hmP,
      transcriptLaw_predict_false pol d r ω i hi hmQ]
    simp only [show klTerm 0 0 = 0 from by simp [klTerm],zero_add]
    rw [binary_mass_chain hpP hqP hpair]
    nlinarith [mul_le_mul_of_nonneg_left hkl hpP.le]

/-- Adaptive finite transcripts, including revisits and early stopping, pay at
most epsilon squared per padded physical observation. -/
theorem tail_transcript_kl {m : ℕ} (n : ℕ) (pol : List Bool → Option (Fin m))
    (d q r : Fin m → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1/2)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (hr : ∀ i, 0 ≤ r i ∧ r i ≤ 1)
    (hcentral : ∀ i, TailContrast (d i) (q i) (r i))
    (hcontrast : ∀ i, d i*|q i-r i| ≤ ε/32) :
    klFT (transcriptLaw (n:=n) pol d q) (transcriptLaw pol d r) ≤ n*ε^2 := by
  induction n with
  | zero => simp [klFT,transcriptLaw,pathProb,signPrior_total]
  | succ n ih =>
    calc
      _ = ∑ ω : Fin n → Option Bool, ∑ o : Option Bool,
          klTerm (transcriptLaw pol d q (Fin.snoc ω o))
            (transcriptLaw pol d r (Fin.snoc ω o)) := by
        unfold klFT
        rw [sum_snoc]
        rfl
      _ ≤ ∑ ω : Fin n → Option Bool,
          (klTerm (transcriptLaw pol d q ω) (transcriptLaw pol d r ω) +
            ε^2*transcriptLaw pol d q ω) :=
        Finset.sum_le_sum (fun ω _ => tail_transcript_step pol d q r hε hd hq hr hcentral hcontrast ω)
      _ = klFT (transcriptLaw (n:=n) pol d q) (transcriptLaw pol d r) + ε^2 := by
        rw [Finset.sum_add_distrib,← Finset.mul_sum,(transcript_law_total m n pol d q hd hq).2,mul_one]
        rfl
      _ ≤ _ := by push_cast; nlinarith

end ThresholdHC.AnytimeLower
