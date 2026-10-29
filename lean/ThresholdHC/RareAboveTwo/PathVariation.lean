import ThresholdHC.RareAboveTwo.ChargedPath

/-! A variation bound that also covers deterministic Bernoulli endpoints. -/
noncomputable section
namespace ThresholdHC.RareAboveTwo
open ThresholdHC.Proofs ThresholdHC.Proofs.Transcript ThresholdHC.CriticalEntropy

theorem mass_l1_bound (P Q p q : ℝ) (hP : 0 ≤ P) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    |P*p-Q*q|+|P*(1-p)-Q*(1-q)| ≤ |P-Q|+2*P*|p-q| := by
  have h₁ := abs_add_le (P*(p-q)) ((P-Q)*q)
  have h₂ := abs_add_le (P*(q-p)) ((P-Q)*(1-q))
  have he₁ : P*(p-q)+(P-Q)*q = P*p-Q*q := by ring
  have he₂ : P*(q-p)+(P-Q)*(1-q) = P*(1-p)-Q*(1-q) := by ring
  rw [he₁,abs_mul,abs_mul,abs_of_nonneg hP,abs_of_nonneg hq] at h₁
  rw [he₂,abs_mul,abs_mul,abs_of_nonneg hP,abs_of_nonneg (sub_nonneg.mpr hq1),abs_sub_comm q p] at h₂
  linarith

theorem charged_variation_step {m n : ℕ} (pol : List Bool → Option (Fin m)) (p q C : Fin m → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (hC : ∀ i, 2*|p i-q i| ≤ C i) (w : Fin n → Option Bool) :
    (∑ o : Option Bool, |pathProb pol p (Fin.snoc w o)-pathProb pol q (Fin.snoc w o)|) ≤
      |pathProb pol p w-pathProb pol q w|+pathProb pol p w*(pol (fullHist w)).elim 0 C := by
  cases h : pol (fullHist w) with
  | none => simp [pathProb_snoc,stepProb,h,Fintype.sum_option]
  | some i =>
    simp only [pathProb_snoc,Fintype.sum_option,Fintype.sum_bool,stepProb,h,
      mul_zero,sub_self,abs_zero,zero_add,Option.elim_some]
    have hP := pathProb_nonneg pol p hp w
    have hb := mass_l1_bound (pathProb pol p w) (pathProb pol q w) (p i) (q i) hP (hq i).1 (hq i).2
    nlinarith only [hb,mul_le_mul_of_nonneg_left (hC i) hP]

theorem charged_variation_bound {m : ℕ} (pol : List Bool → Option (Fin m)) (p q C : Fin m → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (hC : ∀ i, 2*|p i-q i| ≤ C i) (n : ℕ) :
    (∑ w : Fin n → Option Bool, |pathProb pol p w-pathProb pol q w|) ≤
      ∑ w : Fin n → Option Bool, pathProb pol p w*chargedWork pol C w := by
  induction n with
  | zero => simp [pathProb,chargedWork]
  | succ n ih =>
    calc
      _ = ∑ w : Fin n → Option Bool, ∑ o : Option Bool,
          |pathProb pol p (Fin.snoc w o)-pathProb pol q (Fin.snoc w o)| := by rw [sum_snoc]
      _ ≤ ∑ w : Fin n → Option Bool, (|pathProb pol p w-pathProb pol q w|+
          pathProb pol p w*(pol (fullHist w)).elim 0 C) :=
        Finset.sum_le_sum (fun w _ => charged_variation_step pol p q C hp hq hC w)
      _ ≤ _ := by
        rw [Finset.sum_add_distrib,chargedWork_expectation_succ]
        exact add_le_add ih le_rfl

theorem sqrt_square_le_abs (P Q : ℝ) (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    (Real.sqrt P-Real.sqrt Q)^2 ≤ |P-Q| := by
  have hp := Real.sq_sqrt hP
  have hq := Real.sq_sqrt hQ
  by_cases h : P ≤ Q
  · rw [abs_of_nonpos (sub_nonpos.mpr h)]
    have hs := Real.sqrt_le_sqrt h
    nlinarith [mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg P)]
  · rw [abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge h))]
    have hs := Real.sqrt_le_sqrt (le_of_not_ge h)
    nlinarith [mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg Q)]

end ThresholdHC.RareAboveTwo
