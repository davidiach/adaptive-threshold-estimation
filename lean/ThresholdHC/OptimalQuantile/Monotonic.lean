import ThresholdHC.OptimalQuantile.Infinite

noncomputable section
open Real
namespace ThresholdHC.OptimalQuantile

theorem dualPrice_strict_in_factor {k l u : ℝ}
    (hk : sqrt 2 ≤ k) (hkl : k < l) (hu : 1 ≤ u) :
    dualPrice k u < dualPrice l u := by
  have hk1 : 1 ≤ k := (one_le_sqrt.mpr (by norm_num : (1 : ℝ) ≤ 2)).trans hk
  have hi : 0 ≤ 1/u := by positivity
  have hA : 1 ≤ u+1/u := by linarith
  have hm := mul_le_mul_of_nonneg_left hA (show 0 ≤ l+k by linarith)
  have hc : 0 < 2*(l+k)*(u+1/u)-4 := by nlinarith only [hm,hk1,hkl]
  apply sub_pos.mp
  have he : dualPrice l u-dualPrice k u = (l-k)*(2*(l+k)*(u+1/u)-4) := by
    unfold dualPrice
    ring
  rw [he]
  exact mul_pos (sub_pos.mpr hkl) hc

theorem exponentialTail_antitone {p q : ℝ} (hp : 2 ≤ p) (hpq : p ≤ q) :
    exponentialTail q ≤ exponentialTail p := by
  apply Summable.tsum_le_tsum _ (exponentialTail_summable (hp.trans hpq)) (exponentialTail_summable hp)
  intro n
  apply exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_right hpq (show 0 ≤ (2 : ℝ)^n by positivity)
  linarith

theorem partitionSeries_strict_in_factor {k l u : ℝ}
    (hk : sqrt 2 ≤ k) (hkl : k < l) (hu : 1 ≤ u) :
    partitionSeries l u < partitionSeries k u := by
  have hp := dualPrice_strict_in_factor hk hkl hu
  have hfirst : exp (1-dualPrice l u/(2*u)) < exp (1-dualPrice k u/(2*u)) := by
    apply exp_lt_exp.mpr
    have h := div_lt_div_of_pos_right hp (show 0 < 2*u by linarith)
    linarith
  exact add_lt_add_of_lt_of_le hfirst (exponentialTail_antitone (dualPrice_ge_two hk hu) hp.le)

theorem tangent_sum_mono {u v : ℝ} (hu : 1 ≤ u) (huv : u ≤ v) :
    u+1/u ≤ v+1/v := by
  have hu0 : 0 < u := by linarith
  have hv0 : 0 < v := by linarith
  have hp : 0 ≤ (v-u)*(u*v-1) := by
    apply mul_nonneg (sub_nonneg.mpr huv)
    have h := mul_le_mul hu (hu.trans huv) (by norm_num : (0 : ℝ) ≤ 1) hu0.le
    nlinarith only [h]
  have heu : u+1/u = (u^2+1)/u := by
    field_simp [ne_of_gt hu0]
  have hev : v+1/v = (v^2+1)/v := by
    field_simp [ne_of_gt hv0]
  rw [heu,hev,div_le_div_iff₀ hu0 hv0]
  nlinarith only [hp]

theorem dualPrice_mono_in_tangent (k : ℝ) {u v : ℝ} (hu : 1 ≤ u) (huv : u ≤ v) :
    dualPrice k u ≤ dualPrice k v := by
  have h := mul_le_mul_of_nonneg_left (tangent_sum_mono hu huv) (show 0 ≤ 2*k^2 by positivity)
  unfold dualPrice
  linarith

theorem partitionSeries_mono_above_factor {k u v : ℝ}
    (hk : sqrt 2 ≤ k) (hku : k ≤ u) (huv : u ≤ v) :
    partitionSeries k v ≤ partitionSeries k u := by
  have hk1 : 1 ≤ k := (one_le_sqrt.mpr (by norm_num : (1 : ℝ) ≤ 2)).trans hk
  have hu1 : 1 ≤ u := hk1.trans hku
  have hu0 : 0 < u := by linarith
  have hv0 : 0 < v := by linarith
  have hdiv : k/v ≤ k/u := div_le_div_of_nonneg_left (by linarith) hu0 huv
  have hkdiv : k/u ≤ 1 := (div_le_one hu0).mpr hku
  have hp : 0 ≤ (k/u-k/v)*(2-k/u-k/v) :=
    mul_nonneg (sub_nonneg.mpr hdiv) (by linarith)
  have hfirst : exp (1-dualPrice k v/(2*v)) ≤ exp (1-dualPrice k u/(2*u)) := by
    rw [first_exponent_identity k hv0.ne',first_exponent_identity k hu0.ne']
    apply exp_le_exp.mpr
    nlinarith only [hp]
  exact add_le_add hfirst (exponentialTail_antitone (dualPrice_ge_two hk hu1)
    (dualPrice_mono_in_tangent k hu1 huv))

end ThresholdHC.OptimalQuantile
