import SharpPrefixCost
import SharpEntropy

/-! Three-bias lower risk from the finite-prefix work account. -/
noncomputable section
namespace ThresholdHC.SharpRMS
open Proofs Tier3 Tier5 Real

/-- Expected value on a homogeneous finite transcript at sign mean t. -/
def prefixExpect {n : ℕ} (pol : List Bool → Option ℕ) (s t : ℝ) (f : Prefix n → ℝ) :=
  ∑ w, creationLaw pol (fun _ => s/2) (fun _ => (1+t)/2) w * f w

private theorem gibbs_atom (p q g : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hac : p ≠ 0 → q ≠ 0) (hg : 0 < g) :
    p*log g ≤ p*log (p/q)+q*g-p := by
  by_cases hz : p=0
  · simp [hz,mul_nonneg hq hg.le]
  have hp' := lt_of_le_of_ne hp (Ne.symm hz)
  have hq' := lt_of_le_of_ne hq (Ne.symm (hac hz))
  have hh := Real.log_le_sub_one_of_pos (div_pos (mul_pos hq' hg) hp')
  rw [Real.log_div (mul_pos hq' hg).ne' hz, Real.log_mul hq'.ne' hg.ne'] at hh
  rw [Real.log_div hz hq'.ne']
  have hb := mul_le_mul_of_nonneg_right hh hp
  field_simp [hz] at hb
  linarith

/-- A linear inequality in the three risks and fair-law work. Its linear
form permits averaging over an arbitrary independent seed before applying
the work budget. -/
theorem prefix_risk_work {n : ℕ} (pol : List Bool → Option ℕ) (s : ℝ)
    (hs : 0 < s) (hs' : s < 1) (X : Prefix n → ℝ) :
    (40/9:ℝ) ≤ 5 * prefixExpect pol s 0 (fun w => (X w)^2) +
      8 * prefixExpect pol s (7/10) (fun w => (X w-7/10)^2) +
      8 * prefixExpect pol s (-(7/10)) (fun w => (X w+7/10)^2) +
      (7/10:ℝ)^2*artanh s*s*prefixExpect (n := n) pol s 0 workOf := by
  let Q := fun (t : ℝ) => creationLaw (n := n) pol (fun _ => s/2) (fun _ => (1+t)/2)
  let P := Q 0
  let L := fun (t : ℝ) (w : Prefix n) => 1+8*((X w-t)^2-1/9)
  have valid (t : ℝ) (ht : |t| < 1) : (∀ w, 0 ≤ Q t w) ∧ ∑ w, Q t w=1 :=
    creationLaw_total n _ _ _ (fun _ => ⟨by linarith,by linarith⟩)
      (fun _ => ⟨by linarith [(abs_lt.mp ht).1],by linarith [(abs_lt.mp ht).2]⟩)
  have support (t : ℝ) (ht : |t| < 1) (w : Prefix n) : P w ≠ 0 → Q t w ≠ 0 := by
    intro hp hq
    have hh (u : ℝ) (hu : |u| < 1) := transcriptLaw_zero_iff (capPolicy (coinCap n pol) pol)
      (fun _ => s/2) (fun _ => (1+u)/2) (fun _ => ⟨by linarith,by linarith⟩)
      (fun _ => ⟨by linarith [(abs_lt.mp hu).1],by linarith [(abs_lt.mp hu).2]⟩) w
    exact hp ((hh 0 (by norm_num)).2 ((hh t ht).1 hq))
  have cost := transcript_cost (n := n) (capPolicy (coinCap n pol) pol) s hs hs'
  have fair : P = creationLaw (n := n) pol (fun _ => s/2) (fun _ => 1/2) := by
    dsimp [P,Q]
    norm_num
  change pairedCost (creationLaw pol (fun _ => s/2) (fun _ => 1/2))
      (Q (7/10)) (Q (-(7/10))) ≤ (7/10:ℝ)^2*artanh s*s*∑ w : Prefix n,
        creationLaw pol (fun _ => s/2) (fun _ => 1/2) w*workOf w at cost
  rw [← fair] at cost
  have test (t : ℝ) (ht : |t| < 1) (w : Prefix n) :=
    gibbs_atom (P w) (Q t w) (L t w) ((valid 0 (by norm_num)).1 w) ((valid t ht).1 w)
      (support t ht w) (by dsimp [L]; nlinarith [sq_nonneg (X w-t)])
  have per (w : Prefix n) : P w*(40/9) ≤
      5*(P w*(X w)^2) + 8*(Q (7/10) w*(X w-7/10)^2) +
      8*(Q (-(7/10)) w*(X w+7/10)^2) +
      P w*(log (P w/Q (7/10) w)+log (P w/Q (-(7/10)) w)) +
      (Q (7/10) w+Q (-(7/10)) w-2*P w)/9 := by
    have h₀ := mul_le_mul_of_nonneg_left (entropy_minorant (X w)) ((valid 0 (by norm_num)).1 w)
    have hp := test (7/10) (by norm_num) w
    have hn := test (-(7/10)) (by norm_num) w
    dsimp only [L] at hp hn
    rw [sub_neg_eq_add] at hn
    linarith only [h₀,hp,hn]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun w _ => per w)
  simp only [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul, (valid _ (by norm_num : |(7/10:ℝ)| < 1)).2,
    (valid _ (by norm_num : |(-(7/10):ℝ)| < 1)).2] at hsum
  have hP : ∑ w, P w = 1 := (valid 0 (by norm_num)).2
  rw [hP] at hsum
  change (∑ w, P w * _) ≤ (7/10:ℝ)^2*artanh s*s*∑ w, P w*workOf w at cost
  unfold prefixExpect
  change _ ≤ 5*(∑ w, P w*(X w)^2) + 8*(∑ w, Q _ w*(X w-7/10)^2) +
    8*(∑ w, Q _ w*(X w+7/10)^2) + _*(∑ w, P w*workOf w)
  linarith only [hsum,cost]

end ThresholdHC.SharpRMS
