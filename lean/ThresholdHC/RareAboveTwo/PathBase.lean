import ThresholdHC.CriticalEntropy.BernoulliPrefix
import ThresholdHC.Proofs.Tier2.Transcript

/-! Finite stopped paths pay information only for flips actually performed.
This chain compares fixed Bernoulli signs and permits arbitrary stopping policies. -/
noncomputable section
namespace ThresholdHC.RareAboveTwo
open ThresholdHC.Proofs ThresholdHC.Proofs.Transcript ThresholdHC.CriticalEntropy

theorem stepProb_zero_iff {m : ℕ} (pol : List Bool → Option (Fin m))
    (p q : Fin m → ℝ) (hp : ∀ i, 0 < p i ∧ p i < 1) (hq : ∀ i, 0 < q i ∧ q i < 1)
    (xs : List Bool) (o : Option Bool) : stepProb pol p xs o = 0 ↔ stepProb pol q xs o = 0 := by
  cases h : pol xs with
  | none => cases o <;> simp [stepProb,h]
  | some i =>
    cases o with
    | none => simp [stepProb,h]
    | some b =>
      cases b <;> simp [stepProb,h,(hp i).1.ne',(hq i).1.ne',
        (sub_pos.mpr (hp i).2).ne',(sub_pos.mpr (hq i).2).ne']

theorem pathProb_zero_iff {m n : ℕ} (pol : List Bool → Option (Fin m))
    (p q : Fin m → ℝ) (hp : ∀ i, 0 < p i ∧ p i < 1) (hq : ∀ i, 0 < q i ∧ q i < 1)
    (w : Fin n → Option Bool) : pathProb pol p w = 0 ↔ pathProb pol q w = 0 := by
  change (∏ t, stepProb pol p (histBefore w t) (w t)) = 0 ↔ (∏ t, stepProb pol q (histBefore w t) (w t)) = 0
  simp only [Finset.prod_eq_zero_iff]
  exact exists_congr (fun t => and_congr_right (fun _ => stepProb_zero_iff pol p q hp hq _ _))

theorem path_kl_step {m n : ℕ} (pol : List Bool → Option (Fin m))
    (p q : Fin m → ℝ) (hp : ∀ i, 0 < p i ∧ p i < 1) (hq : ∀ i, 0 < q i ∧ q i < 1)
    (C : ℝ) (hC : ∀ i, klB (p i) (q i) ≤ C) (w : Fin n → Option Bool) :
    (∑ o : Option Bool, klTerm (pathProb pol p (Fin.snoc w o)) (pathProb pol q (Fin.snoc w o))) ≤
      klTerm (pathProb pol p w) (pathProb pol q w)+
        C*pathProb pol p w*(if (pol (fullHist w)).isSome then 1 else 0) := by
  have hp0 := pathProb_nonneg pol p (fun i => ⟨(hp i).1.le,(hp i).2.le⟩) w
  by_cases hz : pathProb pol p w = 0
  · simp [pathProb_snoc,hz,klTerm]
  have hP : 0 < pathProb pol p w := lt_of_le_of_ne hp0 (Ne.symm hz)
  have hQ : 0 < pathProb pol q w := lt_of_le_of_ne
    (pathProb_nonneg pol q (fun i => ⟨(hq i).1.le,(hq i).2.le⟩) w)
    (Ne.symm (fun h => hz ((pathProb_zero_iff pol p q hp hq w).2 h)))
  cases h : pol (fullHist w) with
  | none => simp [pathProb_snoc,stepProb,h,Fintype.sum_option,Fintype.sum_bool,klTerm]
  | some i =>
    simp only [pathProb_snoc,Fintype.sum_option,Fintype.sum_bool,stepProb,h,
      mul_zero,show klTerm 0 0 = 0 by simp [klTerm],zero_add,Option.isSome_some,ite_true,mul_one]
    rw [binary_mass_chain hP hQ (Or.inl ⟨hp i,hq i⟩)]
    nlinarith only [mul_le_mul_of_nonneg_left (hC i) hP.le]

theorem path_work_succ {m n : ℕ} (pol : List Bool → Option (Fin m)) (p : Fin m → ℝ) :
    (∑ w : Fin (n+1) → Option Bool, pathProb pol p w*workOf w) =
      (∑ w : Fin n → Option Bool, pathProb pol p w*workOf w)+
        ∑ w : Fin n → Option Bool, pathProb pol p w*(if (pol (fullHist w)).isSome then 1 else 0) := by
  rw [sum_snoc,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w _
  simp_rw [pathProb_snoc,workOf_snoc]
  cases h : pol (fullHist w) <;> simp [Fintype.sum_option,Fintype.sum_bool,stepProb,h] <;> ring


end ThresholdHC.RareAboveTwo
