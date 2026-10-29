import ThresholdHC.RareAboveTwo.PathVariation
import ThresholdHC.RareAboveTwo.FiniteMixture
import ThresholdHC.RareAboveTwo.SignInformation

noncomputable section
namespace ThresholdHC.RareAboveTwo
open ThresholdHC.Proofs ThresholdHC.Proofs.Transcript ThresholdHC.CriticalEntropy

def coinWork {m n : ℕ} (pol : List Bool → Option (Fin m)) (i : Fin m)
    (w : Fin n → Option Bool) : ℝ := chargedWork pol (fun j => if j=i then 1 else 0) w

theorem chargedWork_scale {m n : ℕ} (pol : List Bool → Option (Fin m)) (C : Fin m → ℝ)
    (c : ℝ) (w : Fin n → Option Bool) :
    chargedWork pol (fun i => c*C i) w = c*chargedWork pol C w := by
  unfold chargedWork
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  cases h : w t <;> cases hpol : pol (histBefore w t) <;> simp [h,hpol]

theorem coinWork_nonneg {m n : ℕ} (pol : List Bool → Option (Fin m)) (i : Fin m)
    (w : Fin n → Option Bool) : 0 ≤ coinWork pol i w := by
  unfold coinWork chargedWork
  apply Finset.sum_nonneg
  intro t _
  cases h : w t <;> cases hpol : pol (histBefore w t) <;> simp [h,hpol] <;> positivity

theorem sum_coinWork_le_work {m n : ℕ} (pol : List Bool → Option (Fin m))
    (w : Fin n → Option Bool) : (∑ i, coinWork pol i w) ≤ workOf w := by
  unfold coinWork chargedWork
  rw [Finset.sum_comm,workOf_eq_sum]
  apply Finset.sum_le_sum
  intro t _
  cases h : w t <;> cases hpol : pol (histBefore w t) <;> simp [h,hpol]

theorem path_sign_distance {m n : ℕ} (pol : List Bool → Option (Fin m)) (i : Fin m)
    (p : Fin m → ℝ) (hp : ∀ j, 0 ≤ p j ∧ p j ≤ 1)
    (d a : ℝ) (hd : 0 < d) (hda : d ≤ a) (ha : a ≤ 1/2) :
    let p₀ := Function.update p i (1/2-d)
    let p₁ := Function.update p i (1/2+d)
    (∑ w : Fin n → Option Bool, (Real.sqrt (pathProb pol p₀ w)-Real.sqrt (pathProb pol p₁ w))^2) ≤
      32*a^2*(∑ w : Fin n → Option Bool, pathProb pol p₀ w*coinWork pol i w) := by
  classical
  let p₀ := Function.update p i (1/2-d)
  let p₁ := Function.update p i (1/2+d)
  have hp₀ (j) : 0 ≤ p₀ j ∧ p₀ j ≤ 1 := by
    by_cases h : j=i
    · subst j; simp only [p₀,Function.update_self]; constructor <;> linarith
    · simpa [p₀,Function.update_of_ne h] using hp j
  have hp₁ (j) : 0 ≤ p₁ j ∧ p₁ j ≤ 1 := by
    by_cases h : j=i
    · subst j; simp only [p₁,Function.update_self]; constructor <;> linarith
    · simpa [p₁,Function.update_of_ne h] using hp j
  have hwork : 0 ≤ ∑ w : Fin n → Option Bool, pathProb pol p₀ w*coinWork pol i w :=
    Finset.sum_nonneg (fun w _ => mul_nonneg (pathProb_nonneg pol p₀ hp₀ w) (coinWork_nonneg pol i w))
  have he (c : ℝ) :
      (∑ w : Fin n → Option Bool, pathProb pol p₀ w*
        chargedWork pol (fun j => if j=i then c else 0) w) =
      c*(∑ w : Fin n → Option Bool, pathProb pol p₀ w*coinWork pol i w) := by
    have hfun : (fun j : Fin m => if j=i then c else 0) =
        fun j => c*(if j=i then 1 else 0) := by funext j; split_ifs <;> simp
    rw [hfun]
    simp_rw [chargedWork_scale]
    simp only [coinWork,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _; ring
  by_cases hsmall : a ≤ 1/4
  · have hpair (j) : (0 < p₀ j ∧ p₀ j < 1) ∧ (0 < p₁ j ∧ p₁ j < 1) ∨ p₀ j=p₁ j := by
      by_cases h : j=i
      · subst j; left; simp only [p₀,p₁,Function.update_self]; constructor <;> constructor <;> linarith
      · right; simp [p₀,p₁,Function.update_of_ne h]
    have hC (j) : klB (p₀ j) (p₁ j) ≤ (if j=i then 32*a^2 else 0) := by
      by_cases h : j=i
      · subst j; simpa [p₀,p₁] using sign_kl_bound d a hd hda hsmall
      · simp [p₀,p₁,Function.update_of_ne h,h,klB_self]
    have hkl := charged_kl_bound pol p₀ p₁ (fun j => if j=i then 32*a^2 else 0) hp₀ hp₁ hpair hC n
    rw [he] at hkl
    apply le_trans ?_ hkl
    have hi (w : Fin n → Option Bool) :
        (Real.sqrt (pathProb pol p₀ w)-Real.sqrt (pathProb pol p₁ w))^2 ≤
        klTerm (pathProb pol p₀ w) (pathProb pol p₁ w)+pathProb pol p₁ w-pathProb pol p₀ w := by
      by_cases hz : pathProb pol p₀ w=0
      · simp [hz,(path_support_pair pol p₀ p₁ hpair w).1 hz,klTerm]
      · exact sqrt_square_le_kl _ _
          (lt_of_le_of_ne (pathProb_nonneg pol p₀ hp₀ w) (Ne.symm hz))
          (lt_of_le_of_ne (pathProb_nonneg pol p₁ hp₁ w)
            (Ne.symm (fun h => hz ((path_support_pair pol p₀ p₁ hpair w).2 h))))
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun w _ => hi w)
    simpa only [Finset.sum_sub_distrib,Finset.sum_add_distrib,pathProb_total,add_sub_cancel_right,klFT,klTerm,p₀,p₁] using hh
  · have hC (j) : 2*|p₀ j-p₁ j| ≤ (if j=i then 2 else 0) := by
      by_cases h : j=i
      · subst j; simp only [p₀,p₁,Function.update_self,ite_true]
        have hab : |(1/2-d)-(1/2+d)| ≤ 1 := abs_le.mpr ⟨by linarith,by linarith⟩
        linarith
      · simp [p₀,p₁,Function.update_of_ne h,h]
    have hv := charged_variation_bound pol p₀ p₁ (fun j => if j=i then 2 else 0) hp₀ hp₁ hC n
    rw [he] at hv
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun (w : Fin n → Option Bool) _ => sqrt_square_le_abs
      (pathProb pol p₀ w) (pathProb pol p₁ w) (pathProb_nonneg pol p₀ hp₀ w) (pathProb_nonneg pol p₁ hp₁ w))
    exact hs.trans (hv.trans (mul_le_mul_of_nonneg_right (by nlinarith) hwork))

end ThresholdHC.RareAboveTwo
