import ThresholdHC.RareAboveTwo.PathBase

/-! Information in fixed-parameter adaptive paths, charged to individual labels. -/
noncomputable section
namespace ThresholdHC.RareAboveTwo
open ThresholdHC.Proofs ThresholdHC.Proofs.Transcript ThresholdHC.CriticalEntropy

def chargedWork {m n : ℕ} (pol : List Bool → Option (Fin m)) (C : Fin m → ℝ)
    (w : Fin n → Option Bool) : ℝ :=
  ∑ t, if (w t).isSome then (pol (histBefore w t)).elim 0 C else 0

theorem chargedWork_snoc {m n : ℕ} (pol : List Bool → Option (Fin m)) (C : Fin m → ℝ)
    (w : Fin n → Option Bool) (o : Option Bool) :
    chargedWork pol C (Fin.snoc w o) = chargedWork pol C w+
      (if o.isSome then (pol (fullHist w)).elim 0 C else 0) := by
  unfold chargedWork
  rw [Fin.sum_univ_castSucc]
  simp only [histBefore_snoc_castSucc,Fin.snoc_castSucc,histBefore_snoc_last,Fin.snoc_last]

theorem chargedWork_expectation_succ {m n : ℕ} (pol : List Bool → Option (Fin m))
    (p C : Fin m → ℝ) :
    (∑ w : Fin (n+1) → Option Bool, pathProb pol p w*chargedWork pol C w) =
      (∑ w : Fin n → Option Bool, pathProb pol p w*chargedWork pol C w)+
      ∑ w : Fin n → Option Bool, pathProb pol p w*(pol (fullHist w)).elim 0 C := by
  rw [sum_snoc,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w _
  simp_rw [pathProb_snoc,chargedWork_snoc]
  cases h : pol (fullHist w) <;> simp [Fintype.sum_option,Fintype.sum_bool,stepProb,h] <;> ring

theorem path_support_pair {m n : ℕ} (pol : List Bool → Option (Fin m)) (p q : Fin m → ℝ)
    (hpair : ∀ i, (0 < p i ∧ p i < 1) ∧ (0 < q i ∧ q i < 1) ∨ p i = q i)
    (w : Fin n → Option Bool) : pathProb pol p w = 0 ↔ pathProb pol q w = 0 := by
  have he (xs : List Bool) (o : Option Bool) : stepProb pol p xs o = 0 ↔ stepProb pol q xs o = 0 := by
    cases h : pol xs with
    | none => cases o <;> simp [stepProb,h]
    | some i =>
      rcases hpair i with hpair | he
      · cases o with
        | none => simp [stepProb,h]
        | some b => cases b <;> simp [stepProb,h,hpair.1.1.ne',hpair.2.1.ne',
            (sub_pos.mpr hpair.1.2).ne',(sub_pos.mpr hpair.2.2).ne']
      · cases o with
        | none => simp [stepProb,h]
        | some b => cases b <;> simp [stepProb,h,he]
  change (∏ t, stepProb pol p (histBefore w t) (w t)) = 0 ↔ (∏ t, stepProb pol q (histBefore w t) (w t)) = 0
  simp only [Finset.prod_eq_zero_iff]
  exact exists_congr (fun t => and_congr_right (fun _ => he _ _))

theorem charged_kl_step {m n : ℕ} (pol : List Bool → Option (Fin m)) (p q C : Fin m → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (hpair : ∀ i, (0 < p i ∧ p i < 1) ∧ (0 < q i ∧ q i < 1) ∨ p i = q i)
    (hC : ∀ i, klB (p i) (q i) ≤ C i) (w : Fin n → Option Bool) :
    (∑ o : Option Bool, klTerm (pathProb pol p (Fin.snoc w o)) (pathProb pol q (Fin.snoc w o))) ≤
      klTerm (pathProb pol p w) (pathProb pol q w)+
        pathProb pol p w*(pol (fullHist w)).elim 0 C := by
  by_cases hz : pathProb pol p w = 0
  · simp [pathProb_snoc,hz,klTerm]
  have hP : 0 < pathProb pol p w := lt_of_le_of_ne (pathProb_nonneg pol p hp w) (Ne.symm hz)
  have hQ : 0 < pathProb pol q w := lt_of_le_of_ne (pathProb_nonneg pol q hq w)
    (Ne.symm (fun h => hz ((path_support_pair pol p q hpair w).2 h)))
  cases h : pol (fullHist w) with
  | none => simp [pathProb_snoc,stepProb,h,Fintype.sum_option,klTerm]
  | some i =>
    simp only [pathProb_snoc,Fintype.sum_option,Fintype.sum_bool,stepProb,h,
      mul_zero,show klTerm 0 0 = 0 by simp [klTerm],zero_add,Option.elim_some]
    rw [binary_mass_chain hP hQ (hpair i)]
    exact add_le_add_right (mul_le_mul_of_nonneg_left (hC i) hP.le) _

theorem charged_kl_bound {m : ℕ} (pol : List Bool → Option (Fin m)) (p q C : Fin m → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (hpair : ∀ i, (0 < p i ∧ p i < 1) ∧ (0 < q i ∧ q i < 1) ∨ p i = q i)
    (hC : ∀ i, klB (p i) (q i) ≤ C i) (n : ℕ) :
    klFT (pathProb (n := n) pol p) (pathProb pol q) ≤
      ∑ w : Fin n → Option Bool, pathProb pol p w*chargedWork pol C w := by
  induction n with
  | zero => simp [klFT,pathProb,chargedWork]
  | succ n ih =>
    calc
      _ = ∑ w : Fin n → Option Bool, ∑ o : Option Bool,
          klTerm (pathProb pol p (Fin.snoc w o)) (pathProb pol q (Fin.snoc w o)) := by
        unfold klFT; rw [sum_snoc]; rfl
      _ ≤ ∑ w : Fin n → Option Bool, (klTerm (pathProb pol p w) (pathProb pol q w)+
          pathProb pol p w*(pol (fullHist w)).elim 0 C) :=
        Finset.sum_le_sum (fun w _ => charged_kl_step pol p q C hp hq hpair hC w)
      _ = klFT (pathProb (n := n) pol p) (pathProb pol q)+
          ∑ w : Fin n → Option Bool, pathProb pol p w*(pol (fullHist w)).elim 0 C := by
        rw [Finset.sum_add_distrib]; rfl
      _ ≤ _ := by rw [chargedWork_expectation_succ]; exact add_le_add ih le_rfl

end ThresholdHC.RareAboveTwo
