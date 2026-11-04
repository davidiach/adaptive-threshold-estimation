import ThresholdHC.StoppingProgram.PrefixCoefficients
import ThresholdHC.StoppingProgram.Bellman

/-! Posterior energy on an actual stopped likelihood tree. If the positive
and negative latent signs contribute masses a and b at a node, the node
probability times the squared posterior sign mean is (a-b)^2/(a+b).
This representation also assigns zero energy to impossible prefixes. -/

noncomputable section
open Real

namespace ThresholdHC.FiniteQuantile
open ThresholdHC.Tier6 ThresholdHC.StoppingProgram

def posteriorEnergy (a b : ℝ) : ℝ := (a - b)^2 / (a + b)

theorem posteriorEnergy_step {a b z : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    let p := (1 + z) / 2
    let q := (1 - z) / 2
    posteriorEnergy (a*p) (b*q) + posteriorEnergy (a*q) (b*p) ≤
      posteriorEnergy a b + z^2 * (a + b) := by
  dsimp only
  rcases ha.eq_or_lt with h | ha'
  · subst a
    simp [posteriorEnergy, sq, mul_self_div_self]
    nlinarith only [mul_nonneg (sq_nonneg z) hb]
  rcases hb.eq_or_lt with h | hb'
  · subst b
    simp [posteriorEnergy, sq, mul_self_div_self]
    nlinarith only [mul_nonneg (sq_nonneg z) ha]
  let p := (1 + z) / 2
  let q := (1 - z) / 2
  have hp : 0 < p := by dsimp [p]; positivity
  have hq : 0 ≤ q := by dsimp [q]; linarith
  have h1 : 0 < a*p + b*q := add_pos_of_pos_of_nonneg (mul_pos ha' hp) (mul_nonneg hb hq)
  have h2 : 0 < a*q + b*p := add_pos_of_nonneg_of_pos (mul_nonneg ha hq) (mul_pos hb' hp)
  have hsum : 0 < a + b := add_pos ha' hb'
  let den := (a+b) * (a*p+b*q) * (a*q+b*p)
  have hden : 0 < den := by dsimp [den]; positivity
  have hid : (posteriorEnergy a b + z^2*(a+b) -
      (posteriorEnergy (a*p) (b*q) + posteriorEnergy (a*q) (b*p))) * den =
      z^2 * (a-b)^2 * ((1-z^2)*(a+b)^2 + 4*a*b) / 4 := by
    unfold posteriorEnergy den
    field_simp [hsum.ne', h1.ne', h2.ne']
    dsimp [p,q]
    ring
  have hzsq : 0 ≤ 1-z^2 := by nlinarith only [mul_nonneg (sub_nonneg.mpr hz1) (show 0 ≤ 1+z by linarith)]
  have hslack : 0 ≤ (posteriorEnergy a b + z^2*(a+b) -
      (posteriorEnergy (a*p) (b*q) + posteriorEnergy (a*q) (b*p))) * den := by
    rw [hid]
    positivity
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_left hslack hden)

def midpointMass (g : Gap) (n k : ℕ) : ℝ :=
  (prefixLikelihood true n k g + prefixLikelihood false n k g) / 2

def prefixEnergy (g : Gap) (n k : ℕ) : ℝ :=
  posteriorEnergy (prefixLikelihood true n k g / 2) (prefixLikelihood false n k g / 2)

theorem prefixEnergy_step (g : Gap) {n k : ℕ} (hk : k ≤ n) :
    prefixEnergy g (n+1) k + prefixEnergy g (n+1) (k+1) ≤
      prefixEnergy g n k + 4*(g:ℝ)^2 * midpointMass g n k := by
  have h := posteriorEnergy_step
    (a := prefixLikelihood true n k g / 2) (b := prefixLikelihood false n k g / 2)
    (z := 2*(g:ℝ)) (by positivity [prefixLikelihood_nonneg true n k g])
    (by positivity [prefixLikelihood_nonneg false n k g]) (by positivity [g.property.1])
    (by linarith [g.property.2])
  dsimp only at h
  have he : n+1-k = n-k+1 := by omega
  unfold prefixEnergy midpointMass
  simp only [prefixLikelihood, ite_true, Bool.false_eq_true, ite_false, he,
    Nat.add_sub_add_right, pow_succ] at h ⊢
  convert h using 1 <;> unfold posteriorEnergy <;> ring

/-- The stopped equal-prior posterior energy is at most four times the
squared gap times actual expected work, even at gap one half. -/
theorem stopped_posterior_energy (g : Gap) (cap : ℕ) (tree : StopTree cap) :
    treeInformation (prefixEnergy g) cap 0 0 tree ≤
      4*(g:ℝ)^2 * treeWork (midpointMass g) cap 0 0 tree := by
  have h (d n k : ℕ) (hk : k ≤ n) (a : StopTree d) :
      treeInformation (prefixEnergy g) d n k a ≤ prefixEnergy g n k +
        4*(g:ℝ)^2 * treeWork (midpointMass g) d n k a := by
    induction d generalizing n k with
    | zero => simp [treeInformation, treeWork]
    | succ d ih =>
      cases a with
      | none => simp [treeInformation, treeWork]
      | some branches =>
        simp only [treeInformation, treeWork]
        linarith only [ih (n+1) k (by omega) branches.1,
          ih (n+1) (k+1) (by omega) branches.2, prefixEnergy_step g hk]
  simpa [prefixEnergy, posteriorEnergy, prefixLikelihood] using h cap 0 0 le_rfl tree

end ThresholdHC.FiniteQuantile
