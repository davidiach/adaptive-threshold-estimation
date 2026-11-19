import ThresholdHC.UpperCost.LevelSum
import ThresholdHC.UpperMoment.Disagreement

/-! The early-stopping part of the disagreement, summed over levels.

The cap-`2^l` classifier errs by stopping early at the check with `cap k` flips
with probability at most `exp(-2*cap k*(d + t)^2)`, where `t` is the threshold
of that check (`Tier2.Model.errorUnionBound`). With `j = l - k` and
`v_j = 1 + j*log 2`, the exponent is `2*(sqrt (cap k*d^2) + sqrt v_j)^2`, which
is at least `2*v_j + 4*sqrt v_j*sqrt (cap k*d^2)`. Along a grid of ratio
`sqrt 2`, `∑ u*exp(-c*u) ≤ (2 + sqrt 2)/c` (`grid_exp_le`, a telescoping sum).
Summed over `j` with the weights `1/p_l`, the early-stopping parts of both
consecutive classifiers add at most `41/100` divided by `d`
(`stopError_levelSum_le`). -/
noncomputable section
namespace ThresholdHC.UpperDisagreement
open Real Finset ThresholdHC.Uniform713 ThresholdHC.UpperWork

/-- The early-stopping part of the error union bound of the cap-`2^l` classifier. -/
def stopError (l : ℕ) (d : ℝ) : ℝ :=
  ∑ k ∈ range l, Real.exp (-2 * cap k * (d + Tier2.Model.threshold1 (cap k) (cap l)) ^ 2)

theorem stopError_nonneg (l : ℕ) (d : ℝ) : 0 ≤ stopError l d :=
  sum_nonneg (fun _ _ => (Real.exp_pos _).le)

theorem errorUnionBound_eq (l : ℕ) (d : ℝ) :
    Tier2.Model.errorUnionBound l d = Real.exp (-2 * cap l * d ^ 2) + stopError l d := rfl

/-- `∑ u_k*exp(-c*u_k) ≤ (2 + sqrt 2)/c` along the grid `u_k = sqrt 2^k*d`. -/
theorem grid_exp_le {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (K : ℕ) :
    ∑ k ∈ range K, (Real.sqrt 2 ^ k * d) * Real.exp (-c * (Real.sqrt 2 ^ k * d)) ≤
      (2 + Real.sqrt 2) / c := by
  have hσ0 : 0 < Real.sqrt 2 := by positivity
  have hσ : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  set g : ℕ → ℝ := fun k => Real.exp (-(c * (Real.sqrt 2 ^ k * d)) / Real.sqrt 2) with hg
  have hstep : ∀ k, (1 - 1 / Real.sqrt 2) * (c * (Real.sqrt 2 ^ k * d)) *
      Real.exp (-c * (Real.sqrt 2 ^ k * d)) ≤ g k - g (k + 1) := by
    intro k
    set z := c * (Real.sqrt 2 ^ k * d) with hz
    have hz0 : 0 ≤ z := by positivity
    have hnext : g (k + 1) = Real.exp (-c * (Real.sqrt 2 ^ k * d)) := by
      simp only [hg]
      congr 1
      rw [pow_succ]
      field_simp
    have hcur : g k = Real.exp (-c * (Real.sqrt 2 ^ k * d)) *
        Real.exp ((1 - 1 / Real.sqrt 2) * z) := by
      simp only [hg]
      rw [← Real.exp_add]
      congr 1
      rw [hz]
      field_simp
      ring
    rw [hnext, hcur]
    have hδ : 0 ≤ (1 - 1 / Real.sqrt 2) * z := by
      have : 1 / Real.sqrt 2 ≤ 1 := by
        rw [div_le_one hσ0]
        exact Real.one_le_sqrt.2 (by norm_num)
      exact mul_nonneg (by linarith) hz0
    have he := Real.add_one_le_exp ((1 - 1 / Real.sqrt 2) * z)
    have hE := Real.exp_pos (-c * (Real.sqrt 2 ^ k * d))
    nlinarith
  have hsum : ∑ k ∈ range K, (1 - 1 / Real.sqrt 2) * (c * (Real.sqrt 2 ^ k * d)) *
      Real.exp (-c * (Real.sqrt 2 ^ k * d)) ≤ 1 := by
    refine (sum_le_sum (fun k _ => hstep k)).trans ?_
    rw [sum_range_sub']
    have h0 : g 0 ≤ 1 := by
      simp only [hg]
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.2
      have : 0 ≤ c * (Real.sqrt 2 ^ 0 * d) / Real.sqrt 2 := by positivity
      rw [neg_div]
      linarith
    have hK : 0 ≤ g K := (Real.exp_pos _).le
    linarith
  have hr : (1 - 1 / Real.sqrt 2) * (2 + Real.sqrt 2) = 1 := by
    field_simp
    linear_combination hσ
  have hcoef : 0 < 1 - 1 / Real.sqrt 2 := by
    have : 1 / Real.sqrt 2 < 1 := by
      rw [div_lt_one hσ0]
      exact Real.lt_sqrt_of_sq_lt (by norm_num)
    linarith
  rw [le_div_iff₀ hc, sum_mul]
  have h2 : ∑ k ∈ range K, (Real.sqrt 2 ^ k * d) * Real.exp (-c * (Real.sqrt 2 ^ k * d)) * c =
      (2 + Real.sqrt 2) * ∑ k ∈ range K, (1 - 1 / Real.sqrt 2) * (c * (Real.sqrt 2 ^ k * d)) *
        Real.exp (-c * (Real.sqrt 2 ^ k * d)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro k _
    linear_combination (-(Real.sqrt 2 ^ k * d) * Real.exp (-c * (Real.sqrt 2 ^ k * d)) * c) * hr
  rw [h2]
  have h2p : 0 ≤ 2 + Real.sqrt 2 := by positivity
  nlinarith

/-- One early-stopping term, in grid form. -/
theorem stop_term_le (k J : ℕ) {d : ℝ} (hd : 0 < d) :
    Real.exp (-2 * cap k * (d + Tier2.Model.threshold1 (cap k) (cap (k + J))) ^ 2) ≤
      Real.exp (-2 * (1 + J * Real.log 2)) *
        Real.exp (-(4 * Real.sqrt (1 + J * Real.log 2)) * (Real.sqrt 2 ^ k * d)) := by
  have hc := cap_pos k
  have hratio : cap (k + J) / cap k = 2 ^ J := by
    simp only [cap, pow_add]
    field_simp
  set v := 1 + (J : ℝ) * Real.log 2 with hv
  have hv0 : 0 ≤ v := by have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2); positivity
  have ht : Tier2.Model.threshold1 (cap k) (cap (k + J)) = Real.sqrt (v / cap k) := by
    unfold Tier2.Model.threshold1
    rw [hratio, Real.log_pow]
  have hu : Real.sqrt 2 ^ k * d = Real.sqrt (cap k) * d := by rw [UpperWork.sqrt_cap]
  have hs : Real.sqrt v = Real.sqrt (cap k) * Real.sqrt (v / cap k) := by
    rw [← Real.sqrt_mul hc.le, mul_div_cancel₀ _ hc.ne']
  have hc' : Real.sqrt (cap k) ^ 2 = cap k := Real.sq_sqrt hc.le
  have hv' : Real.sqrt v ^ 2 = v := Real.sq_sqrt hv0
  rw [← Real.exp_add, ht, hu]
  apply Real.exp_le_exp.2
  have hexp : cap k * (d + Real.sqrt (v / cap k)) ^ 2 =
      (Real.sqrt (cap k) * d + Real.sqrt v) ^ 2 := by
    rw [hs, show (Real.sqrt (cap k) * d + Real.sqrt (cap k) * Real.sqrt (v / cap k)) ^ 2 =
      Real.sqrt (cap k) ^ 2 * (d + Real.sqrt (v / cap k)) ^ 2 by ring, hc']
  rw [mul_assoc, hexp]
  have hq : 0 ≤ Real.sqrt (cap k) * d := by positivity
  nlinarith [sq_nonneg (Real.sqrt (cap k) * d)]

/-- The early-stopping parts, summed with the weights `1/p_l`. -/
theorem stopError_sum_le (L : ℕ) {d : ℝ} (hd : 0 < d) :
    d * ∑ l ∈ range (L + 1), stopError l d / pLevel l ≤
      (2 + Real.sqrt 2) ^ 2 / (4 * (13 / 10)) * Real.exp (-2) *
        (Real.sqrt 2 / (4 - Real.sqrt 2)) := by
  have hr0 := rLevel_pos
  have hr1 := rLevel_lt_one
  have hσ0 : 0 < Real.sqrt 2 := by positivity
  have hσ : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hrσ : rLevel * Real.sqrt 2 = 1 := UpperWork.rLevel_mul_sqrt_two
  have h1r : (1 - rLevel) * (2 + Real.sqrt 2) = 1 := by
    linear_combination (-(1 + Real.sqrt 2)) * hrσ + rLevel * hσ
  have hinvp : ∀ l, 1 / pLevel l = (2 + Real.sqrt 2) * Real.sqrt 2 ^ l := by
    intro l
    have hp : 0 < pLevel l := mul_pos (by linarith) (pow_pos hr0 l)
    have hprod : pLevel l * ((2 + Real.sqrt 2) * Real.sqrt 2 ^ l) = 1 := by
      unfold pLevel
      calc
        (1 - rLevel) * rLevel ^ l * ((2 + Real.sqrt 2) * Real.sqrt 2 ^ l) =
            ((1 - rLevel) * (2 + Real.sqrt 2)) * (rLevel * Real.sqrt 2) ^ l := by ring
        _ = 1 := by rw [h1r, hrσ, one_pow, one_mul]
    rw [div_eq_iff hp.ne']
    linarith
  -- reorder by the level difference
  have htri := UpperCost.sum_triangle L (fun l k =>
    Real.exp (-2 * cap k * (d + Tier2.Model.threshold1 (cap k) (cap l)) ^ 2) / pLevel l)
  have hexpand : ∑ l ∈ range (L + 1), stopError l d / pLevel l =
      ∑ l ∈ range (L + 1), ∑ k ∈ range l,
        Real.exp (-2 * cap k * (d + Tier2.Model.threshold1 (cap k) (cap l)) ^ 2) / pLevel l := by
    apply sum_congr rfl
    intro l _
    rw [stopError, sum_div]
  rw [hexpand, htri, mul_sum]
  set w : ℕ → ℝ := fun j => Real.sqrt 2 ^ (j + 1) *
    Real.exp (-2 * (1 + ((j + 1 : ℕ) : ℝ) * Real.log 2)) with hw
  have hlog := Real.log_two_gt_d9
  have hjterm : ∀ j ∈ range L, d * ∑ k ∈ range (L - j),
      Real.exp (-2 * cap k * (d + Tier2.Model.threshold1 (cap k) (cap (k + j + 1))) ^ 2) /
        pLevel (k + j + 1) ≤ (2 + Real.sqrt 2) * w j * ((2 + Real.sqrt 2) / (4 * (13 / 10))) := by
    intro j _
    set v := 1 + ((j + 1 : ℕ) : ℝ) * Real.log 2 with hv
    have hsv : 13 / 10 ≤ Real.sqrt v := by
      apply Real.le_sqrt_of_sq_le
      simp only [hv]
      push_cast
      nlinarith
    have hc : 0 < 4 * Real.sqrt v := by positivity
    have hk : ∀ k ∈ range (L - j), d *
        (Real.exp (-2 * cap k * (d + Tier2.Model.threshold1 (cap k) (cap (k + j + 1))) ^ 2) /
          pLevel (k + j + 1)) ≤
        (2 + Real.sqrt 2) * w j * ((Real.sqrt 2 ^ k * d) *
          Real.exp (-(4 * Real.sqrt v) * (Real.sqrt 2 ^ k * d))) := by
      intro k _
      have hb := stop_term_le k (j + 1) hd
      rw [show k + (j + 1) = k + j + 1 by ring] at hb
      have hp := hinvp (k + j + 1)
      rw [div_eq_mul_one_div, hp]
      simp only [hw]
      have hpow : Real.sqrt 2 ^ (k + j + 1) = Real.sqrt 2 ^ (j + 1) * Real.sqrt 2 ^ k := by
        rw [← pow_add]
        ring_nf
      rw [hpow]
      have hpos : 0 ≤ d * ((2 + Real.sqrt 2) * (Real.sqrt 2 ^ (j + 1) * Real.sqrt 2 ^ k)) := by
        positivity
      calc
        _ = d * ((2 + Real.sqrt 2) * (Real.sqrt 2 ^ (j + 1) * Real.sqrt 2 ^ k)) *
            Real.exp (-2 * cap k * (d + Tier2.Model.threshold1 (cap k) (cap (k + j + 1))) ^ 2) := by
          ring
        _ ≤ d * ((2 + Real.sqrt 2) * (Real.sqrt 2 ^ (j + 1) * Real.sqrt 2 ^ k)) *
            (Real.exp (-2 * (1 + ((j + 1 : ℕ) : ℝ) * Real.log 2)) *
              Real.exp (-(4 * Real.sqrt v) * (Real.sqrt 2 ^ k * d))) :=
          mul_le_mul_of_nonneg_left hb hpos
        _ = _ := by ring
    rw [mul_sum]
    refine (sum_le_sum hk).trans ?_
    rw [← mul_sum]
    have hg := grid_exp_le hc hd (L - j)
    have hw0 : 0 ≤ (2 + Real.sqrt 2) * w j := by simp only [hw]; positivity
    refine (mul_le_mul_of_nonneg_left hg hw0).trans ?_
    apply mul_le_mul_of_nonneg_left _ hw0
    apply div_le_div_of_nonneg_left (by positivity) (by norm_num)
    linarith
  refine (sum_le_sum hjterm).trans ?_
  rw [← sum_mul, ← mul_sum]
  -- the geometric sum over the level difference
  have hw' : ∀ j, w j = Real.exp (-2) * (Real.sqrt 2 / 4) ^ (j + 1) := by
    intro j
    simp only [hw]
    have h4 : Real.exp (-2 * (1 + ((j + 1 : ℕ) : ℝ) * Real.log 2)) =
        Real.exp (-2) * ((1 / 4 : ℝ) ^ (j + 1)) := by
      rw [show -2 * (1 + ((j + 1 : ℕ) : ℝ) * Real.log 2) =
        -2 + ((j + 1 : ℕ) : ℝ) * Real.log (1 / 4) by
          rw [show (1 / 4 : ℝ) = (2 ^ 2)⁻¹ by norm_num, Real.log_inv, Real.log_pow]
          push_cast
          ring]
      rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log (by norm_num)]
    rw [h4, show Real.sqrt 2 / 4 = Real.sqrt 2 * (1 / 4) by ring, mul_pow]
    ring
  have hq0 : 0 ≤ Real.sqrt 2 / 4 := by positivity
  have hq1 : Real.sqrt 2 / 4 < 1 := by nlinarith [Real.sqrt_lt_sqrt (by norm_num : (0:ℝ) ≤ 2) (by norm_num : (2:ℝ) < 16)]
  have hgeo : ∑ j ∈ range L, (Real.sqrt 2 / 4) ^ (j + 1) ≤ Real.sqrt 2 / (4 - Real.sqrt 2) := by
    have hs : HasSum (fun j : ℕ => (Real.sqrt 2 / 4) ^ (j + 1))
        (Real.sqrt 2 / 4 * (1 - Real.sqrt 2 / 4)⁻¹) := by
      convert (hasSum_geometric_of_lt_one hq0 hq1).mul_left (Real.sqrt 2 / 4) using 1
      funext j
      ring
    have h := sum_le_hasSum (range L) (fun j _ => pow_nonneg hq0 (j + 1)) hs
    refine h.trans (le_of_eq ?_)
    have hne : (4 : ℝ) - Real.sqrt 2 ≠ 0 := by nlinarith
    have hne' : 1 - Real.sqrt 2 / 4 ≠ 0 := by nlinarith
    field_simp
  rw [sum_congr rfl (fun j _ => hw' j), ← mul_sum]
  have he0 : 0 ≤ Real.exp (-2) := (Real.exp_pos _).le
  have hA : 0 ≤ (2 + Real.sqrt 2) * ((2 + Real.sqrt 2) / (4 * (13 / 10))) := by positivity
  calc
    (2 + Real.sqrt 2) * (Real.exp (-2) * ∑ j ∈ range L, (Real.sqrt 2 / 4) ^ (j + 1)) *
        ((2 + Real.sqrt 2) / (4 * (13 / 10))) ≤
      (2 + Real.sqrt 2) * (Real.exp (-2) * (Real.sqrt 2 / (4 - Real.sqrt 2))) *
        ((2 + Real.sqrt 2) / (4 * (13 / 10))) := by gcongr
    _ = _ := by ring

/-- Both consecutive classifiers: at most `41/100` divided by `d`. -/
theorem stopError_levelSum_le (L : ℕ) {d : ℝ} (hd : 0 < d) :
    d * ∑ l ∈ range (L + 1), (stopError l d + stopError (l - 1) d) / pLevel l ≤ 41 / 100 := by
  have hr0 := rLevel_pos
  have hr1 := rLevel_lt_one
  have hrσ : rLevel * Real.sqrt 2 = 1 := UpperWork.rLevel_mul_sqrt_two
  have hp : ∀ l, 0 < pLevel l := fun l => mul_pos (by linarith) (pow_pos hr0 l)
  have hT0 : ∀ L', 0 ≤ ∑ l ∈ range (L' + 1), stopError l d / pLevel l :=
    fun L' => sum_nonneg (fun l _ => div_nonneg (stopError_nonneg l d) (hp l).le)
  -- the level `l - 1` parts are `sqrt 2` times the level parts
  have hshift : ∑ l ∈ range (L + 1), stopError (l - 1) d / pLevel l ≤
      Real.sqrt 2 * ∑ l ∈ range (L + 1), stopError l d / pLevel l := by
    rw [sum_range_succ']
    simp only [Nat.zero_sub, Nat.add_sub_cancel]
    have h0 : stopError 0 d = 0 := by simp [stopError]
    rw [h0, zero_div, add_zero, mul_sum]
    have hle : ∑ i ∈ range L, stopError i d / pLevel (i + 1) ≤
        ∑ i ∈ range (L + 1), Real.sqrt 2 * (stopError i d / pLevel i) := by
      have hterm : ∀ i ∈ range L, stopError i d / pLevel (i + 1) =
          Real.sqrt 2 * (stopError i d / pLevel i) := by
        intro i _
        rw [show pLevel (i + 1) = pLevel i * rLevel by unfold pLevel; ring, ← div_div,
          div_eq_mul_inv (stopError i d / pLevel i), inv_eq_of_mul_eq_one_right hrσ]
        ring
      rw [sum_congr rfl hterm]
      exact sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) (fun i _ _ =>
        mul_nonneg (Real.sqrt_nonneg 2) (div_nonneg (stopError_nonneg i d) (hp i).le))
    exact hle
  have hmain := stopError_sum_le L hd
  have hsplit : ∑ l ∈ range (L + 1), (stopError l d + stopError (l - 1) d) / pLevel l =
      ∑ l ∈ range (L + 1), stopError l d / pLevel l +
        ∑ l ∈ range (L + 1), stopError (l - 1) d / pLevel l := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro l _
    rw [add_div]
  rw [hsplit]
  have hσu : Real.sqrt 2 ≤ 141422 / 100000 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
  have hσl : (141421 / 100000 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
  have he := UpperMoment.exp_neg_two_le
  have hconst : (1 + Real.sqrt 2) * ((2 + Real.sqrt 2) ^ 2 / (4 * (13 / 10)) * Real.exp (-2) *
      (Real.sqrt 2 / (4 - Real.sqrt 2))) ≤ 41 / 100 := by
    have hq : Real.sqrt 2 / (4 - Real.sqrt 2) ≤ 141422 / 258578 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      nlinarith
    have hq0 : 0 ≤ Real.sqrt 2 / (4 - Real.sqrt 2) := div_nonneg (by positivity) (by linarith)
    have hA : (1 + Real.sqrt 2) * ((2 + Real.sqrt 2) ^ 2 / (4 * (13 / 10))) ≤
        (1 + 141422 / 100000) * ((2 + 141422 / 100000) ^ 2 / (4 * (13 / 10))) := by
      gcongr
    have hA0 : 0 ≤ (1 + Real.sqrt 2) * ((2 + Real.sqrt 2) ^ 2 / (4 * (13 / 10))) := by positivity
    have he0 : 0 ≤ Real.exp (-2) := (Real.exp_pos _).le
    calc
      _ = ((1 + Real.sqrt 2) * ((2 + Real.sqrt 2) ^ 2 / (4 * (13 / 10)))) * Real.exp (-2) *
          (Real.sqrt 2 / (4 - Real.sqrt 2)) := by ring
      _ ≤ ((1 + 141422 / 100000) * ((2 + 141422 / 100000) ^ 2 / (4 * (13 / 10)))) *
          (339 / 2500) * (141422 / 258578) := by gcongr
      _ ≤ 41 / 100 := by norm_num
  have hd0 := hd.le
  nlinarith [mul_le_mul_of_nonneg_left hshift hd0, hT0 L]

end ThresholdHC.UpperDisagreement
