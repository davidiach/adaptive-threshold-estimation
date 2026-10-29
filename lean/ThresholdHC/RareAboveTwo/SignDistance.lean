import ThresholdHC.RareAboveTwo.SignMixture

noncomputable section
namespace ThresholdHC.RareAboveTwo
open MeasureTheory ThresholdHC.Proofs ThresholdHC.Proofs.Transcript ThresholdHC.CriticalEntropy

theorem transcript_sign_distance {m n : ℕ} (pol : List Bool → Option (Fin m))
    (d q : Fin m → ℝ) (i : Fin m) (a : ℝ)
    (hd : ∀ j, 0 < d j ∧ d j ≤ 1/2) (hq : ∀ j, 0 ≤ q j ∧ q j ≤ 1)
    (hda : d i ≤ a) (ha : a ≤ 1/2) :
    2*(1-realFiniteAffinity
      (transcriptLaw (n := n) pol d (Function.update q i 0))
      (transcriptLaw pol d (Function.update q i 1))) ≤
      32*a^2*(∑ w : Fin n → Option Bool, transcriptLaw pol d (Function.update q i 0) w*coinWork pol i w) := by
  classical
  let P (b : Bool) (s : Fin m → Bool) (w : Fin n → Option Bool) :=
    pathProb pol (Function.update (signParameter d s) i (1/2+(if b then d i else -d i))) w
  have hp (b : Bool) (s : Fin m → Bool) (j : Fin m) : 0 ≤ (Function.update (signParameter d s) i (1/2+(if b then d i else -d i))) j ∧
      (Function.update (signParameter d s) i (1/2+(if b then d i else -d i))) j ≤ 1 := by
    by_cases h : j=i
    · subst j; simp only [Function.update_self]; cases b <;> constructor <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> linarith [(hd i).1,(hd i).2]
    · rw [Function.update_of_ne h]; exact signParameter_bounds d (fun j => ⟨(hd j).1.le,(hd j).2⟩) s j
  have hP (b s w) : 0 ≤ P b s w := pathProb_nonneg pol _ (hp b s) w
  have hPs (b s) : (∑ w, P b s w)=1 := pathProb_total pol _ n
  have he (b : Bool) (w : Fin n → Option Bool) :
      (∑ s, signWeight q s*P b s w) = transcriptLaw pol d (Function.update q i (if b then 1 else 0)) w :=
    sign_average_override pol d q i b w
  have hJ := finite_distance_sum_le (signWeight q) (signWeight_nonneg q hq) (signPrior_total q)
    (P false) (P true) (hP false) (hP true) (hPs false) (hPs true)
  simp only [he,Bool.false_eq_true,ite_false,ite_true] at hJ
  have hb (s : Fin m → Bool) : 2*(1-realFiniteAffinity (P false s) (P true s)) ≤
      32*a^2*(∑ w, P false s w*coinWork pol i w) := by
    rw [← sum_sqrt_distance _ _ (hP false s) (hP true s) (hPs false s) (hPs true s)]
    simpa only [P,Bool.false_eq_true,ite_false,ite_true,sub_eq_add_neg] using
      path_sign_distance (n := n) pol i (signParameter d s)
        (signParameter_bounds d (fun j => ⟨(hd j).1.le,(hd j).2⟩) s) (d i) a (hd i).1 hda ha
  calc
    _ ≤ 2*(∑ s, signWeight q s*(1-realFiniteAffinity (P false s) (P true s))) := by linarith
    _ = ∑ s, signWeight q s*(2*(1-realFiniteAffinity (P false s) (P true s))) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro s _; ring
    _ ≤ ∑ s, signWeight q s*(32*a^2*(∑ w, P false s w*coinWork pol i w)) :=
      Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (hb s) (signWeight_nonneg q hq s))
    _ = _ := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro w _
      have hew := he false w
      simp only [Bool.false_eq_true,ite_false] at hew
      rw [← hew]
      simp only [Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s _; ring

end ThresholdHC.RareAboveTwo
