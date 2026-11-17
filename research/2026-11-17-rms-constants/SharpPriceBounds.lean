import SharpBarrier
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Elementary bounds for every exit barrier, including arbitrarily large k. -/
noncomputable section
namespace ThresholdHC.SharpRMS
open Set MeasureTheory

def exitLength (s t : ℝ) (k : ℕ) := (k:ℝ)+1-t*((k:ℝ)/barrierPosterior s k-1/s)

theorem exit_length_mono (s t : ℝ) (hs : 0 < s) (hs' : s < 1)
    (ht : 0 ≤ t) (ht' : t ≤ 1) (j k : ℕ) (hj : 0 < j) (hjk : j ≤ k) :
    exitLength s t j ≤ exitLength s t k := by
  induction k, hjk using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    apply ih.trans
    let x := barrierPosterior s k
    have h := barrier_posterior_bounds s hs hs' k
    have hx : 0 < x := hs.trans_le (h.2.2.2 (hj.trans_le hk))
    have hx' : x < 1 := h.2.1
    have hxs : x ≤ k*s := h.2.2.1
    have den : 0 < 1+s*x := by positivity
    have pos : 0 < (x+s)/(1+s*x) := by positivity
    have slope : ((k:ℝ)+1)/((x+s)/(1+s*x)) - k/x ≤ 1 := by
      rw [sub_le_iff_le_add,div_le_iff₀ pos]
      field_simp
      have a : x*(1-s) ≤ (k*s)*(1+x) := by
        apply le_trans _ (mul_le_mul_of_nonneg_right hxs (show 0 ≤ 1+x by linarith))
        nlinarith [mul_nonneg hx.le (show 0 ≤ x+s by linarith)]
      nlinarith only [mul_nonneg (sub_nonneg.mpr a) (sub_nonneg.mpr hx'.le)]
    unfold exitLength
    change _ ≤ ((k+1:ℕ):ℝ)+1-t*(((k+1:ℕ):ℝ)/((x+s)/(1+s*x))-1/s)
    push_cast
    change (k:ℝ)+1-t*((k:ℝ)/x-1/s) ≤ _
    linarith only [mul_le_mul_of_nonneg_left slope ht,ht']

private theorem length_two (s t : ℝ) (hs : 0 < s) :
    exitLength s t 2 = 3-s*t := by
  simp [exitLength,barrierPosterior]
  field_simp
  ring

/-- A lower bound on the reciprocal Fisher price that uses the second-flip
cost for every barrier of height at least two. -/
theorem price_of_two_caps (s t P : ℝ) (hs : 0 < s) (hs' : s < 1)
    (ht : 0 ≤ t) (ht' : t < 1) (hP : 0 ≤ P)
    (h₁ : P ≤ 1-s^2*t^2) (h₂ : P ≤ s^2*(1-t^2)*(3-s*t)/2) :
    admissibleExitPrice s t P := by
  intro k hk
  by_cases one : k=1
  · subst k
    simp [barrierPosterior,hs.ne']
    nlinarith only [h₁]
  let x := barrierPosterior s k
  have hb := barrier_posterior_bounds s hs hs' k
  have hx : 0 < x := hs.trans_le (hb.2.2.2 hk)
  have hx' : x ≤ 1 := hb.2.1.le
  have hlen := exit_length_mono s t hs hs' ht ht'.le 2 k (by decide) (by omega)
  rw [length_two s t hs] at hlen
  change P*(1+x/s) ≤ (1-t*x)*(1+t*s)*exitLength s t k
  have hts : s*t ≤ 1 := (mul_le_mul_of_nonneg_right hs'.le ht).trans (by simpa using ht'.le)
  have htx : t*x ≤ 1 := (mul_le_mul_of_nonneg_left hx' ht).trans (by simpa using ht'.le)
  have common : s*(s+1)*(1+t) ≤ 2*(1+t*s) := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hs'.le) (show 0 ≤ 2+s+s*t by positivity)]
  calc
    _ ≤ P*(1+1/s) := mul_le_mul_of_nonneg_left (by linarith [div_le_div_of_nonneg_right hx' hs.le]) hP
    _ ≤ (s^2*(1-t^2)*(3-s*t)/2)*(1+1/s) := mul_le_mul_of_nonneg_right h₂ (by positivity)
    _ ≤ (1-t)*(1+t*s)*(3-s*t) := by
      field_simp
      nlinarith only [mul_nonneg (mul_nonneg (sub_nonneg.mpr common) (sub_nonneg.mpr ht'.le))
        (show 0 ≤ 3-s*t by linarith)]
    _ ≤ (1-t*x)*(1+t*s)*(3-s*t) := by
      apply mul_le_mul_of_nonneg_right _ (by linarith)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith [mul_le_mul_of_nonneg_left hx' ht]
    _ ≤ _ := mul_le_mul_of_nonneg_left hlen (mul_nonneg (by linarith) (by positivity))

def nearPerfectReciprocal (s t : ℝ) := if t ≤ 3/4 then 1-s^2*t^2 else s^2*(1-t^2)

theorem near_perfect_admissible (s t : ℝ) (hs : 39/40 ≤ s) (hs' : s < 1)
    (ht : 0 ≤ t) (ht' : t < 1) : admissibleExitPrice s t (nearPerfectReciprocal s t) := by
  have hs0 : 0 < s := by linarith
  have hsq : s^2 ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hs'.le) (show 0 ≤ 1+s by linarith)]
  have v : 0 ≤ 1-t^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr ht'.le) (show 0 ≤ 1+t by linarith)]
  have hst : s*t ≤ t := by simpa using mul_le_mul_of_nonneg_right hs'.le ht
  apply price_of_two_caps s t _ hs0 hs' ht ht'
  · unfold nearPerfectReciprocal
    split <;> nlinarith [mul_nonneg (sq_nonneg t) (sub_nonneg.mpr hsq), mul_nonneg (sq_nonneg s) v]
  · unfold nearPerfectReciprocal
    split <;> linarith
  · unfold nearPerfectReciprocal
    split_ifs with h
    · have a : (39/40:ℝ)^2 ≤ s^2 := by nlinarith [mul_nonneg (show 0 ≤ s-39/40 by linarith) (show 0 ≤ s+39/40 by linarith)]
      have b : 7/16 ≤ 1-t^2 := by nlinarith [mul_nonneg (show 0 ≤ 3/4-t by linarith) (show 0 ≤ 3/4+t by linarith)]
      have c : 1/4 ≤ 1-s*t := by linarith
      have bound := mul_le_mul_of_nonneg a b (by norm_num) v
      nlinarith only [mul_le_mul_of_nonneg bound c (by norm_num) (by linarith),a]
    · nlinarith only [mul_nonneg (mul_nonneg (sq_nonneg s) v) (show 0 ≤ 1-s*t by linarith)]

/-- A polynomial upper bound for the tapered information price below 3/4,
and the sign-revelation upper bound above 3/4. -/
def nearPerfectEnvelope (s t : ℝ) :=
  if t ≤ 3/4 then (1-t^2)-(1-s^2)*((1-t^2)*t^2) else (1-t^2)/s^2

theorem near_perfect_envelope (s t : ℝ) (hs : 39/40 ≤ s) (hs' : s < 1)
    (ht : 0 ≤ t) (ht' : t < 1) :
    0 < nearPerfectReciprocal s t ∧ nearPerfectReciprocal s t ≤ 1 ∧
      (1-t^2)^2 ≤ nearPerfectEnvelope s t * nearPerfectReciprocal s t := by
  have hs0 : 0 < s := by linarith
  have s2 : s^2 < 1 := by nlinarith [mul_pos (sub_pos.mpr hs') (show 0 < 1+s by linarith)]
  have v : 0 < 1-t^2 := by nlinarith [mul_pos (sub_pos.mpr ht') (show 0 < 1+t by linarith)]
  unfold nearPerfectEnvelope nearPerfectReciprocal
  split_ifs
  · refine ⟨by nlinarith [mul_nonneg (sub_nonneg.mpr s2.le) (sq_nonneg t)],by nlinarith [mul_nonneg (sq_nonneg s) (sq_nonneg t)],?_⟩
    nlinarith only [mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg v.le (sub_nonneg.mpr s2.le)) (sq_nonneg s))
      (sq_nonneg (t^2))) zero_le_one]
  · refine ⟨mul_pos (sq_pos_of_pos hs0) v,?_,?_⟩
    · nlinarith [mul_nonneg (sq_nonneg s) (sq_nonneg t)]
    · field_simp
      ring_nf
      norm_num

theorem near_perfect_integral (s : ℝ) (hs : 39/40 ≤ s) (hs' : s < 1) :
    IntervalIntegrable (nearPerfectEnvelope s) volume 0 1 ∧
    (∫ t in (0:ℝ)..1, nearPerfectEnvelope s t) ≤ 2/3 := by
  let a := (3/4:ℝ)
  let V := fun t : ℝ => 1-t^2
  let M := fun t : ℝ => (1-s^2)*(V t*t^2)
  let f := nearPerfectEnvelope s
  have hv : Continuous V := by dsimp [V]; fun_prop
  have hm : Continuous M := by dsimp [M]; fun_prop
  have left : Set.EqOn (fun t => V t-M t) f (Set.uIoo 0 a) := by
    rw [Set.uIoo_of_le (by dsimp [a]; norm_num)]
    intro t ht
    exact (ite_eq_left ht.2.le).symm
  have right : Set.EqOn (fun t => V t/s^2) f (Set.uIoo a 1) := by
    rw [Set.uIoo_of_le (by dsimp [a]; norm_num)]
    intro t ht
    exact (ite_eq_right (not_le_of_gt ht.1)).symm
  have hL : IntervalIntegrable f volume 0 a :=
    ((hv.sub hm).intervalIntegrable ..).congr_uIoo left
  have hR : IntervalIntegrable f volume a 1 :=
    ((hv.div_const _).intervalIntegrable ..).congr_uIoo right
  refine ⟨hL.trans hR,?_⟩
  change (∫ t in (0:ℝ)..1, f t) ≤ _
  rw [← intervalIntegral.integral_add_adjacent_intervals hL hR,
    ← intervalIntegral.integral_congr_uIoo left,← intervalIntegral.integral_congr_uIoo right,
    intervalIntegral.integral_sub (hv.intervalIntegrable ..) (hm.intervalIntegrable ..),
    intervalIntegral.integral_div]
  have iV (l r : ℝ) : (∫ t in l..r, V t) = (r-l)-(r^3-l^3)/3 := by
    dsimp [V]
    rw [intervalIntegral.integral_sub (intervalIntegrable_const) (Continuous.intervalIntegrable (by fun_prop) ..),
      intervalIntegral.integral_const,integral_pow]
    norm_num
  have iM : (∫ t in (0:ℝ)..a, M t) = (1-s^2)*(477/5120) := by
    dsimp [M,V,a]
    rw [intervalIntegral.integral_const_mul]
    have eqn (t : ℝ) : (1-t^2)*t^2 = t^2-t^4 := by ring
    simp_rw [eqn]
    rw [intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) ..)
      (Continuous.intervalIntegrable (by fun_prop) ..),integral_pow,integral_pow]
    norm_num
  rw [iV,iM,iV]
  dsimp [a]
  have hpos : 0 < s := by linarith
  have hs2 : (39/40:ℝ)^2 ≤ s^2 := by nlinarith [mul_nonneg (show 0 ≤ s-39/40 by linarith) (show 0 ≤ s+39/40 by linarith)]
  have hlt : 0 ≤ 1-s^2 := by nlinarith [mul_pos (sub_pos.mpr hs') (show 0 < 1+s by linarith)]
  field_simp
  nlinarith only [mul_nonneg hlt (show 0 ≤ (477/5120)*s^2-11/192 by linarith only [hs2])]

end ThresholdHC.SharpRMS
