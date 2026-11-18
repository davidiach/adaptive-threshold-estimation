import ThresholdHC.Tier5.CreationBase

/-! Likelihood and work identities for arbitrary adaptive finite prefixes. -/
noncomputable section
namespace ThresholdHC.SharpRMS
open Proofs Tier3 Tier5

/-- The fair-prior posterior mean of the sign. The zero-denominator convention
also defines the statistic on impossible words. -/
def posterior {m n : ℕ} (pol : List Bool → Option (Fin m)) (w : Prefix n)
    (d : Fin m → ℝ) (i : Fin m) : ℝ :=
  let A := coinLike pol w i (1/2+d i)
  let B := coinLike pol w i (1/2-d i)
  (A-B)/(A+B)

private theorem fair_tilt (a b t : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ((1+t)/2)*a+(1-(1+t)/2)*b =
    ((1/2)*a+(1-1/2)*b)*(1+t*((a-b)/(a+b))) := by
  by_cases hz : a+b=0
  · have := show a=0 by linarith
    have := show b=0 by linarith
    simp_all
  · field_simp
    ring

theorem transcript_tilt {m n : ℕ} (pol : List Bool → Option (Fin m)) (w : Prefix n)
    (d t : Fin m → ℝ) (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1/2) :
    transcriptLaw pol d (fun i => (1+t i)/2) w =
    transcriptLaw pol d (fun _ => 1/2) w * ∏ i, (1+t i*posterior pol w d i) := by
  rw [transcriptLaw_factor, transcriptLaw_factor, mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  apply fair_tilt
  · apply coinLike_nonneg <;> linarith [(hd i).1,(hd i).2]
  · apply coinLike_nonneg <;> linarith [(hd i).1,(hd i).2]

theorem creation_tilt {n : ℕ} (pol : List Bool → Option ℕ) (w : Prefix n)
    (d t : ℕ → ℝ) (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1/2) :
    creationLaw pol d (fun i => (1+t i)/2) w =
    creationLaw pol d (fun _ => 1/2) w *
      ∏ i : Fin (coinCap n pol), (1+t i.val*
        posterior (capPolicy (coinCap n pol) pol) w (fun j => d j.val) i) :=
  transcript_tilt _ _ _ _ (fun i => hd i.val)

/-- A paid observation contributes its sign, and padding contributes zero. -/
def bitValue : Option Bool → ℝ
  | some true => 1
  | some false => -1
  | none => 0

def netCount {m n : ℕ} (pol : List Bool → Option (Fin m)) (w : Prefix n) (i : Fin m) : ℝ :=
  ∑ k, if pol (histBefore w k) = some i then bitValue (w k) else 0

private def signValue (b : Bool) : ℝ := if b then 1 else -1

private def agreement {m n : ℕ} (pol : List Bool → Option (Fin m)) (w : Prefix n)
    (σ : Fin m → Bool) : ℝ := ∑ i, signValue (σ i) * netCount pol w i

private theorem net_snoc {m n : ℕ} (pol : List Bool → Option (Fin m)) (w : Prefix n)
    (o : Option Bool) (i : Fin m) :
    netCount pol (Fin.snoc w o) i = netCount pol w i +
      (if pol (fullHist w) = some i then bitValue o else 0) := by
  simp only [netCount, Fin.sum_univ_castSucc, histBefore_snoc_castSucc,
    histBefore_snoc_last, Fin.snoc_castSucc, Fin.snoc_last]

private theorem agreement_snoc {m n : ℕ} (pol : List Bool → Option (Fin m)) (w : Prefix n)
    (o : Option Bool) (σ : Fin m → Bool) :
    agreement pol (Fin.snoc w o) σ = agreement pol w σ +
      (match pol (fullHist w) with | none => 0 | some i => signValue (σ i) * bitValue o) := by
  simp only [agreement, net_snoc, mul_add, Finset.sum_add_distrib]
  congr 1
  cases h : pol (fullHist w) with
  | none => simp
  | some i => simp [mul_ite]

private def coinP {m : ℕ} (s : ℝ) (σ : Fin m → Bool) (i : Fin m) : ℝ :=
  1/2 + if σ i then s/2 else -(s/2)

private theorem wald_fixed {m : ℕ} (pol : List Bool → Option (Fin m)) (s : ℝ)
    (σ : Fin m → Bool) (n : ℕ) :
    ∑ w : Prefix n, pathProb pol (coinP s σ) w * (agreement pol w σ - s*workOf w) = 0 := by
  induction n with
  | zero => simp [agreement, netCount, workOf]
  | succ n ih =>
    rw [sum_snoc, ← ih]
    apply Finset.sum_congr rfl
    intro w _
    simp_rw [pathProb_snoc, agreement_snoc, workOf_snoc, mul_assoc, ← Finset.mul_sum]
    congr 1
    cases h : pol (fullHist w) with
    | none => simp [Fintype.sum_option, stepProb, h]
    | some i =>
      cases hs : σ i <;> simp [Fintype.sum_option, stepProb, h, coinP, hs, signValue, bitValue] <;> ring

private def fairWeight {m n : ℕ} (pol : List Bool → Option (Fin m)) (s : ℝ)
    (σ : Fin m → Bool) (w : Prefix n) := (1/2:ℝ)^m * pathProb pol (coinP s σ) w

private theorem sum_fair {m n : ℕ} (pol : List Bool → Option (Fin m)) (s : ℝ) (w : Prefix n) :
    ∑ σ, fairWeight pol s σ w = transcriptLaw pol (fun _ => s/2) (fun _ => 1/2) w := by
  unfold transcriptLaw fairWeight coinP
  norm_num [div_pow]

private theorem posterior_mass {m n : ℕ} (pol : List Bool → Option (Fin m)) (s : ℝ)
    (hs : 0 ≤ s) (hs' : s ≤ 1) (w : Prefix n) (i : Fin m) :
    ∑ σ, fairWeight pol s σ w * signValue (σ i) =
      transcriptLaw pol (fun _ => s/2) (fun _ => 1/2) w *
        posterior pol w (fun _ => s/2) i := by
  let f := fun (j : Fin m) (b : Bool) =>
    (1/2:ℝ) * coinLike pol w j (1/2 + if b then s/2 else -(s/2))
  have hp (σ : Fin m → Bool) : fairWeight pol s σ w =
      pathValidity pol w * ∏ j, f j (σ j) := by
    rw [fairWeight, pathProb_factor]
    simp only [f, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, coinP]
    ring
  simp_rw [hp, mul_assoc, ← Finset.mul_sum]
  rw [sum_prod_coordinate, transcriptLaw_split pol _ _ w i]
  let a := coinLike pol w i (1/2+s/2)
  let b := coinLike pol w i (1/2-s/2)
  have ha : 0 ≤ a := coinLike_nonneg _ _ _ (by linarith) (by linarith)
  have hb : 0 ≤ b := coinLike_nonneg _ _ _ (by linarith) (by linarith)
  have ratio : (a/2+b/2)*((a-b)/(a+b)) = a/2-b/2 := by
    by_cases hz : a+b=0
    · have := show a=0 by linarith
      have := show b=0 by linarith
      simp_all
    · field_simp
  simp only [f, signValue, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte,
    ← sub_eq_add_neg, mul_one, mul_neg_one, otherMass, coinMix, posterior]
  norm_num1
  dsimp only [a,b] at ratio
  linear_combination (pathValidity pol w *
    ∏ j ∈ Finset.univ.erase i, ((1/2:ℝ)*coinLike pol w j (1/2+s/2) +
      (1/2:ℝ)*coinLike pol w j (1/2-s/2))) * -ratio

/-- Expected posterior sign times observed net count is exactly flip bias
times expected paid work, including policies that can switch coins at any step. -/
theorem transcript_wald {m n : ℕ} (pol : List Bool → Option (Fin m)) (s : ℝ)
    (hs : 0 ≤ s) (hs' : s ≤ 1) :
    (∑ w : Prefix n, transcriptLaw pol (fun _ => s/2) (fun _ => 1/2) w *
      ∑ i, posterior pol w (fun _ => s/2) i * netCount pol w i) =
    s * ∑ w : Prefix n, transcriptLaw pol (fun _ => s/2) (fun _ => 1/2) w * workOf w := by
  have path (w : Prefix n) :
      transcriptLaw pol (fun _ => s/2) (fun _ => 1/2) w *
        (∑ i, posterior pol w (fun _ => s/2) i * netCount pol w i) =
      ∑ σ, fairWeight pol s σ w * agreement pol w σ := by
    simp only [agreement, Finset.mul_sum]
    rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ) (f := fun σ i =>
      fairWeight pol s σ w * (signValue (σ i) * netCount pol w i))]
    apply Finset.sum_congr rfl
    intro i _
    simp only [← mul_assoc, ← Finset.sum_mul, posterior_mass pol s hs hs']
  apply sub_eq_zero.mp
  simp_rw [path, ← sum_fair pol s, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib,
    show ∀ (a b : ℝ), s*(a*b) = a*(s*b) from fun _ _ => by ring, ← mul_sub]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro σ _
  simp only [fairWeight, mul_assoc, ← Finset.mul_sum, wald_fixed, mul_zero]

theorem creation_wald {n : ℕ} (pol : List Bool → Option ℕ) (s : ℝ)
    (hs : 0 ≤ s) (hs' : s ≤ 1) :
    (∑ w : Prefix n, creationLaw pol (fun _ => s/2) (fun _ => 1/2) w *
      ∑ i : Fin (coinCap n pol), posterior (capPolicy (coinCap n pol) pol) w (fun _ => s/2) i *
        netCount (capPolicy (coinCap n pol) pol) w i) =
    s * ∑ w : Prefix n, creationLaw pol (fun _ => s/2) (fun _ => 1/2) w * workOf w :=
  transcript_wald _ s hs hs'

private theorem tilted_posterior_ratio (a b t : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ht : |t| < 1) :
    let q := (1+t)/2
    let z := (a-b)/(a+b)
    (q*a+(1-q)*b)*((z+t)/(1+t*z)) = q*a-(1-q)*b := by
  dsimp
  by_cases hz : a+b=0
  · have := show a=0 by linarith
    have := show b=0 by linarith
    simp_all
  have hp := lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm hz)
  have hz' : |(a-b)/(a+b)| ≤ 1 := by
    rw [abs_div,abs_of_pos hp,div_le_one hp,abs_le]
    constructor <;> linarith
  have hm : |t*((a-b)/(a+b))| < 1 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hz' (abs_nonneg t)).trans_lt (by simpa using ht)
  rw [← mul_div_assoc,div_eq_iff (show 1+t*((a-b)/(a+b)) ≠ 0 by linarith [(abs_lt.mp hm).1])]
  field_simp
  ring

/-- The Wald identity away from the reference prior. This gives the
observable posterior mean for every interleaved label at nonzero bias. -/
theorem biased_wald {m n : ℕ} (pol : List Bool → Option (Fin m)) (s t : ℝ)
    (hs : 0 ≤ s) (hs' : s ≤ 1) (ht : |t| < 1) :
    let Q := transcriptLaw (n := n) pol (fun _ => s/2) (fun _ => (1+t)/2)
    let z := fun (w : Prefix n) => posterior pol w (fun _ => s/2)
    (∑ w, Q w * ∑ i, ((z w i+t)/(1+t*z w i))*netCount pol w i) =
    s*∑ w, Q w*workOf w := by
  let q := (1+t)/2
  let Q := transcriptLaw (n := n) pol (fun _ => s/2) (fun _ => q)
  let z := fun (w : Prefix n) => posterior pol w (fun _ => s/2)
  let prior := fun (σ : Fin m → Bool) => ∏ i, if σ i then q else 1-q
  let joint := fun (σ : Fin m → Bool) (w : Prefix n) => prior σ * pathProb pol (coinP s σ) w
  have mass (w : Prefix n) : Q w = ∑ σ, joint σ w := rfl
  have coord (w : Prefix n) (i : Fin m) :
      ∑ σ, joint σ w * signValue (σ i) = Q w*((z w i+t)/(1+t*z w i)) := by
    let f := fun (j : Fin m) (b : Bool) =>
      (if b then q else 1-q) * coinLike pol w j (1/2 + if b then s/2 else -(s/2))
    have factor (σ : Fin m → Bool) : joint σ w = pathValidity pol w * ∏ j, f j (σ j) := by
      dsimp [joint,prior,f,coinP]
      rw [pathProb_factor,Finset.prod_mul_distrib]
      unfold coinP
      ring
    simp_rw [factor,mul_assoc,← Finset.mul_sum]
    rw [sum_prod_coordinate]
    dsimp only [Q]
    rw [transcriptLaw_split pol _ _ w i]
    let a := coinLike pol w i (1/2+s/2)
    let b := coinLike pol w i (1/2-s/2)
    have ha : 0 ≤ a := coinLike_nonneg _ _ _ (by linarith) (by linarith)
    have hb : 0 ≤ b := coinLike_nonneg _ _ _ (by linarith) (by linarith)
    have ratio := tilted_posterior_ratio a b t ha hb ht
    change (q*a+(1-q)*b)*((z w i+t)/(1+t*z w i))=q*a-(1-q)*b at ratio
    simp only [f,signValue,Fintype.sum_bool,Bool.false_eq_true,↓reduceIte,
      ← sub_eq_add_neg,mul_one,mul_neg_one,otherMass,coinMix]
    rw [mul_assoc (pathValidity pol w * _) _ _,ratio]
    ring
  have word (w : Prefix n) :
      Q w*(∑ i, ((z w i+t)/(1+t*z w i))*netCount pol w i) =
      ∑ σ, joint σ w*agreement pol w σ := by
    simp only [agreement, Finset.mul_sum]
    rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ) (f := fun σ i =>
      joint σ w * (signValue (σ i)*netCount pol w i))]
    apply Finset.sum_congr rfl
    intro i _
    simp only [← mul_assoc,← Finset.sum_mul,coord]
  change (∑ w, Q w*(∑ i, ((z w i+t)/(1+t*z w i))*netCount pol w i)) = s*∑ w, Q w*workOf w
  apply sub_eq_zero.mp
  simp_rw [word,mass,Finset.sum_mul,Finset.mul_sum,← Finset.sum_sub_distrib,
    show ∀ (a b : ℝ), s*(a*b) = a*(s*b) from fun _ _ => by ring, ← mul_sub]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro σ _
  simp only [joint,mul_assoc,← Finset.mul_sum,wald_fixed,mul_zero]

end ThresholdHC.SharpRMS
