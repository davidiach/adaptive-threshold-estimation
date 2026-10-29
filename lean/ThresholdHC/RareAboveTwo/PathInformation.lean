import ThresholdHC.RareAboveTwo.PathBase

noncomputable section
namespace ThresholdHC.RareAboveTwo
open ThresholdHC.Proofs ThresholdHC.Proofs.Transcript ThresholdHC.CriticalEntropy

theorem path_kl_bound {m : ℕ} (pol : List Bool → Option (Fin m))
    (p q : Fin m → ℝ) (hp : ∀ i, 0 < p i ∧ p i < 1) (hq : ∀ i, 0 < q i ∧ q i < 1)
    (C : ℝ) (hC : ∀ i, klB (p i) (q i) ≤ C) (n : ℕ) :
    klFT (pathProb (n := n) pol p) (pathProb pol q) ≤
      C*∑ w : Fin n → Option Bool, pathProb pol p w*workOf w := by
  induction n with
  | zero => simp [klFT,pathProb,workOf]
  | succ n ih =>
    calc
      _ = ∑ w : Fin n → Option Bool, ∑ o : Option Bool,
          klTerm (pathProb pol p (Fin.snoc w o)) (pathProb pol q (Fin.snoc w o)) := by
        unfold klFT
        rw [sum_snoc]
        rfl
      _ ≤ ∑ w : Fin n → Option Bool, (klTerm (pathProb pol p w) (pathProb pol q w)+
          C*pathProb pol p w*(if (pol (fullHist w)).isSome then 1 else 0)) :=
        Finset.sum_le_sum (fun w _ => path_kl_step pol p q hp hq C hC w)
      _ = klFT (pathProb (n := n) pol p) (pathProb pol q)+
          C*∑ w : Fin n → Option Bool, pathProb pol p w*(if (pol (fullHist w)).isSome then 1 else 0) := by
        rw [Finset.sum_add_distrib]
        simp only [mul_assoc,← Finset.mul_sum,klFT,klTerm]
      _ ≤ C*(∑ w : Fin n → Option Bool, pathProb pol p w*workOf w)+
          C*∑ w : Fin n → Option Bool, pathProb pol p w*(if (pol (fullHist w)).isSome then 1 else 0) :=
        add_le_add ih le_rfl
      _ = _ := by rw [path_work_succ]; ring

end ThresholdHC.RareAboveTwo
