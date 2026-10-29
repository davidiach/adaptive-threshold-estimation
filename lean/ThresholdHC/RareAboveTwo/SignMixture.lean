import ThresholdHC.RareAboveTwo.PathSign
import ThresholdHC.RareAboveTwo.KernelDistance
import ThresholdHC.CriticalEntropy.FinitePopulation

noncomputable section
namespace ThresholdHC.RareAboveTwo
open MeasureTheory ThresholdHC.Proofs ThresholdHC.Proofs.Transcript ThresholdHC.CriticalEntropy

def signWeight {m : ℕ} (q : Fin m → ℝ) (s : Fin m → Bool) : ℝ :=
  ∏ j, if s j then q j else 1-q j

def signParameter {m : ℕ} (d : Fin m → ℝ) (s : Fin m → Bool) (j : Fin m) : ℝ :=
  1/2+(if s j then d j else -d j)

theorem signWeight_nonneg {m : ℕ} (q : Fin m → ℝ) (hq : ∀ j, 0 ≤ q j ∧ q j ≤ 1)
    (s : Fin m → Bool) : 0 ≤ signWeight q s := by
  apply Finset.prod_nonneg
  intro j _; split_ifs <;> linarith [(hq j).1,(hq j).2]

theorem signParameter_bounds {m : ℕ} (d : Fin m → ℝ) (hd : ∀ j, 0 ≤ d j ∧ d j ≤ 1/2)
    (s : Fin m → Bool) (j : Fin m) : 0 ≤ signParameter d s j ∧ signParameter d s j ≤ 1 := by
  unfold signParameter
  split_ifs <;> constructor <;> linarith [(hd j).1,(hd j).2]

theorem sign_average_override {m n : ℕ} (pol : List Bool → Option (Fin m))
    (d q : Fin m → ℝ) (i : Fin m) (b : Bool) (w : Fin n → Option Bool) :
    (∑ s : Fin m → Bool, signWeight q s *
      pathProb pol (Function.update (signParameter d s) i (1/2+(if b then d i else -d i))) w) =
      transcriptLaw pol d (Function.update q i (if b then 1 else 0)) w := by
  classical
  simp_rw [pathProb_factor]
  calc
    _ = pathValidity pol w * ∑ s : Fin m → Bool,
        ∏ j, (if s j then q j else 1-q j)*
          coinLike pol w j (if j=i then 1/2+(if b then d i else -d i) else signParameter d s j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      simp only [signWeight,Finset.prod_mul_distrib,Function.update_apply]
      ring
    _ = pathValidity pol w * ∏ j, ∑ v : Bool, (if v then q j else 1-q j)*
          coinLike pol w j (if j=i then 1/2+(if b then d i else -d i) else 1/2+(if v then d j else -d j)) := by
      simp only [signParameter]
      congr 1
      exact (Fintype.prod_sum (fun j : Fin m => fun v : Bool => (if v then q j else 1-q j)*
        coinLike pol w j (if j=i then 1/2+(if b then d i else -d i) else 1/2+(if v then d j else -d j)))).symm
    _ = _ := by
      rw [transcriptLaw_factor]
      congr 1
      apply Finset.prod_congr rfl
      intro j _
      by_cases h : j=i
      · subst j
        cases b <;> simp [Function.update_self] <;> ring
      · simp [h,Function.update_of_ne h,sub_eq_add_neg]

theorem transcript_mix_update {m n : ℕ} (pol : List Bool → Option (Fin m))
    (d q : Fin m → ℝ) (i : Fin m) (u : ℝ) (w : Fin n → Option Bool) :
    transcriptLaw pol d (Function.update q i u) w =
      priorMix u (transcriptLaw pol d (Function.update q i 0) w)
        (transcriptLaw pol d (Function.update q i 1) w) := by
  classical
  have hf (v : ℝ) : transcriptLaw pol d (Function.update q i v) w =
      pathValidity pol w * (v*coinLike pol w i (1/2+d i)+(1-v)*coinLike pol w i (1/2-d i))*
        ∏ j ∈ Finset.univ.erase i, (q j*coinLike pol w j (1/2+d j)+(1-q j)*coinLike pol w j (1/2-d j)) := by
    rw [transcriptLaw_factor,← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),← mul_assoc]
    simp only [Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [hf,hf,hf]
  unfold priorMix
  ring

end ThresholdHC.RareAboveTwo
