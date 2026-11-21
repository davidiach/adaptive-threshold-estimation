import ThresholdHC.SharpRMS.WeakRisk
import ThresholdHC.UnbiasedConverse.TwoPoint

/-! A finite-prefix testing bound for the two deterministic sign laws at one
gap. Under sign mean one every coin is positive and under sign mean minus one
every coin is negative, so a paid flip shows one with probability one half
plus or minus half the flip bias, including revisits. The two transcript laws
differ by the factor exp (2 artanh s N), where N is the net observed sign. The
triangular discrimination is then bounded through the Wald identity by
s artanh s times the summed expected work. No relative entropy enters. -/
noncomputable section
namespace ThresholdHC.OracleSharpness
open Proofs Tier3 Tier5 Real

/-- Net observed sign of a padded transcript. -/
private def netBits {n : ℕ} (w : Prefix n) : ℝ := ∑ k, SharpRMS.bitValue (w k)

private theorem netBits_snoc {n : ℕ} (w : Prefix n) (o : Option Bool) :
    netBits (Fin.snoc w o : Prefix (n+1)) = netBits w + SharpRMS.bitValue o := by
  simp only [netBits, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]

/-- Wald identity at a common coin probability. -/
private theorem wald_zero {m : ℕ} (pol : List Bool → Option (Fin m)) (p : ℝ) (n : ℕ) :
    ∑ w : Prefix n, pathProb pol (fun _ => p) w * (netBits w - (2*p-1)*workOf w) = 0 := by
  induction n with
  | zero => simp [netBits, workOf]
  | succ n ih =>
    rw [sum_snoc, ← ih]
    apply Finset.sum_congr rfl
    intro w _
    simp_rw [pathProb_snoc, netBits_snoc, workOf_snoc, mul_assoc, ← Finset.mul_sum]
    congr 1
    cases h : pol (fullHist w) with
    | none => simp [Fintype.sum_option, stepProb, h, SharpRMS.bitValue]
    | some i => simp [Fintype.sum_option, stepProb, h, SharpRMS.bitValue]; ring

private theorem wald_const {m : ℕ} (pol : List Bool → Option (Fin m)) (p : ℝ) (n : ℕ) :
    ∑ w : Prefix n, pathProb pol (fun _ => p) w * netBits w =
      (2*p-1) * ∑ w : Prefix n, pathProb pol (fun _ => p) w * workOf w := by
  have h := wald_zero pol p n
  simp only [mul_sub, Finset.sum_sub_distrib] at h
  rw [sub_eq_zero] at h
  rw [h, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  ring

private theorem exp_two_artanh (s : ℝ) (hs : 0 < s) (hs' : s < 1) :
    exp (2*artanh s) = (1/2+s/2)/(1/2-s/2) := by
  have hq : 0 < 1 - s := by linarith
  rw [show 2*artanh s = artanh s + artanh s by ring, Real.exp_add,
    exp_artanh ⟨by linarith, hs'⟩, Real.mul_self_sqrt (div_nonneg (by linarith) hq.le)]
  field_simp

private theorem step_ratio {m : ℕ} (pol : List Bool → Option (Fin m)) (s : ℝ)
    (hs : 0 < s) (hs' : s < 1) (h : List Bool) (o : Option Bool) :
    stepProb pol (fun _ => 1/2+s/2) h o =
      stepProb pol (fun _ => 1/2-s/2) h o * exp (2*artanh s*SharpRMS.bitValue o) := by
  have e := exp_two_artanh s hs hs'
  have hq : (1/2-s/2) ≠ 0 := by linarith
  have hp : (1/2+s/2) ≠ 0 := by linarith
  cases hpol : pol h with
  | none => cases o <;> simp [stepProb, hpol, SharpRMS.bitValue]
  | some i =>
    cases o with
    | none => simp [stepProb, hpol]
    | some b =>
      cases b
      · simp only [stepProb, hpol, SharpRMS.bitValue]
        rw [show 2*artanh s*(-1) = -(2*artanh s) by ring, Real.exp_neg, e]
        field_simp
        ring
      · simp only [stepProb, hpol, SharpRMS.bitValue, mul_one, e]
        field_simp

private theorem path_ratio {m n : ℕ} (pol : List Bool → Option (Fin m)) (s : ℝ)
    (hs : 0 < s) (hs' : s < 1) (w : Prefix n) :
    pathProb pol (fun _ => 1/2+s/2) w =
      pathProb pol (fun _ => 1/2-s/2) w * exp (2*artanh s*netBits w) := by
  change (∏ t, stepProb pol (fun _ => 1/2+s/2) (histBefore w t) (w t)) =
    (∏ t, stepProb pol (fun _ => 1/2-s/2) (histBefore w t) (w t)) * _
  rw [netBits, Finset.mul_sum, Real.exp_sum, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun t _ => step_ratio pol s hs hs' _ _)

/-- The squared-loss two-point bound for one word, with the triangular
discrimination replaced by half the symmetric log-likelihood term. -/
private theorem word_bound (P Q L X : ℝ) (hQ : 0 ≤ Q) (hP : P = Q * exp L) :
    P + Q ≤ P*(X-1)^2 + Q*(X+1)^2 + (P-Q)*L/2 := by
  subst hP
  rcases hQ.eq_or_lt with h | h
  · subst h
    simp
  set u := exp L with hu_def
  have hu : 0 < u := exp_pos L
  have hu1 : 0 < u+1 := by linarith
  have tri := UnbiasedConverse.triangle_le_symmetric_log (p := u/(u+1)) (q := 1/(u+1))
    (div_pos hu hu1) (div_pos one_pos hu1) (by field_simp)
  rw [show u/(u+1)/(1/(u+1)) = u by field_simp, hu_def, log_exp, ← hu_def,
    show u/(u+1)-1/(u+1) = (u-1)/(u+1) by field_simp, div_pow] at tri
  have tri' : 2*(u-1)^2 ≤ (u-1)*L*(u+1) := by
    have h2 := mul_le_mul_of_nonneg_left tri (sq_nonneg (u+1))
    have e1 : (u+1)^2*(2*((u-1)^2/(u+1)^2)) = 2*(u-1)^2 := by field_simp
    have e2 : (u+1)^2*((u-1)/(u+1)*L) = (u-1)*L*(u+1) := by field_simp
    linarith
  have key : (u+1)*(1+u) ≤ (u+1)*(u*(X-1)^2+(X+1)^2+(u-1)*L/2) := by
    nlinarith [sq_nonneg (u*(X-1)+(X+1))]
  have k2 := le_of_mul_le_mul_left key hu1
  nlinarith [mul_le_mul_of_nonneg_left k2 h.le]

/-- The deterministic-sign testing bound on padded transcripts of a finite
coin family. -/
theorem sign_path_bound {m n : ℕ} (pol : List Bool → Option (Fin m)) (s : ℝ)
    (hs : 0 < s) (hs' : s < 1) (X : Prefix n → ℝ) :
    (2:ℝ) ≤ ∑ w : Prefix n, pathProb pol (fun _ => 1/2+s/2) w*(X w-1)^2 +
      ∑ w : Prefix n, pathProb pol (fun _ => 1/2-s/2) w*(X w+1)^2 +
      s*artanh s*(∑ w : Prefix n, pathProb pol (fun _ => 1/2+s/2) w*workOf w +
        ∑ w : Prefix n, pathProb pol (fun _ => 1/2-s/2) w*workOf w) := by
  let P := pathProb (n := n) pol (fun _ => 1/2+s/2)
  let Q := pathProb (n := n) pol (fun _ => 1/2-s/2)
  let L := fun w : Prefix n => 2*artanh s*netBits w
  have hQ (w : Prefix n) : 0 ≤ Q w :=
    pathProb_nonneg pol _ (fun _ => ⟨by linarith, by linarith⟩) w
  have per (w : Prefix n) := word_bound (P w) (Q w) (L w) (X w) (hQ w) (path_ratio pol s hs hs' w)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun w _ => per w)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  have tP : ∑ w, P w = 1 := pathProb_total pol _ n
  have tQ : ∑ w, Q w = 1 := pathProb_total pol _ n
  have hL : ∑ w, (P w - Q w) * L w / 2 =
      artanh s * ∑ w, P w * netBits w - artanh s * ∑ w, Q w * netBits w := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro w _
    ring
  have wP := wald_const pol (1/2+s/2) n
  have wQ := wald_const pol (1/2-s/2) n
  change ∑ w, P w * netBits w = _ * ∑ w, P w * workOf w at wP
  change ∑ w, Q w * netBits w = _ * ∑ w, Q w * workOf w at wQ
  rw [tP, tQ, hL, wP, wQ] at hsum
  change (2:ℝ) ≤ ∑ w, P w*(X w-1)^2 + ∑ w, Q w*(X w+1)^2 +
    s*artanh s*(∑ w, P w*workOf w + ∑ w, Q w*workOf w)
  linarith

private theorem creation_pos {n : ℕ} (pol : List Bool → Option ℕ) (s : ℝ) (w : Prefix n) :
    creationLaw pol (fun _ => s/2) (fun _ => (1+1)/2) w =
      pathProb (capPolicy (coinCap n pol) pol) (fun _ => 1/2+s/2) w := by
  unfold creationLaw
  rw [transcriptLaw_factor, pathProb_factor]
  norm_num

private theorem creation_neg {n : ℕ} (pol : List Bool → Option ℕ) (s : ℝ) (w : Prefix n) :
    creationLaw pol (fun _ => s/2) (fun _ => (1+ -1)/2) w =
      pathProb (capPolicy (coinCap n pol) pol) (fun _ => 1/2-s/2) w := by
  unfold creationLaw
  rw [transcriptLaw_factor, pathProb_factor]
  norm_num

/-- The deterministic-sign testing bound for a countable-label policy at a
bounded horizon, at sign means one and minus one. -/
theorem prefix_sign_bound {n : ℕ} (pol : List Bool → Option ℕ) (s : ℝ)
    (hs : 0 < s) (hs' : s < 1) (X : Prefix n → ℝ) :
    (2:ℝ) ≤ SharpRMS.prefixExpect pol s 1 (fun w => (X w-1)^2) +
      SharpRMS.prefixExpect pol s (-1) (fun w => (X w+1)^2) +
      s*artanh s*(SharpRMS.prefixExpect pol s 1 (@workOf n) +
        SharpRMS.prefixExpect pol s (-1) (@workOf n)) := by
  have h := sign_path_bound (capPolicy (coinCap n pol) pol) s hs hs' X
  simp only [SharpRMS.prefixExpect, creation_pos, creation_neg]
  exact h

end ThresholdHC.OracleSharpness
