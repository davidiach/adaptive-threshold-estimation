import ThresholdHC.OptimalQuantile.Root
import Mathlib.Analysis.Convex.Deriv

/-! Chord bound for the five-term partition sum.

For `√2 ≤ k ≤ 31/20`, the function `finitePartition 5 k u + 25 u^2/2` is convex on
`[1,31/20]`. Each exponent has the form `a+b u+c/u+d/u^2`, and the second
derivative of `exp` of it is at least `exp` of it times the exponent's second
derivative. The first term contributes at least `-6k^2`, the five tail terms at
least `-2k^2 (2/5)^j`, and `25` exceeds the sum of these. On a cell `[l,r]` the
partition sum is then at most its larger endpoint value plus `25(r-l)^2/8`. -/
noncomputable section
open Real
namespace ThresholdHC.QuantileFactorUpper
open ThresholdHC.OptimalQuantile

/-- The exponent `a+b u+c/u+d/u^2`. -/
def expo (a b c d u : ℝ) : ℝ := a+b*u+c*u⁻¹+d*u⁻¹^2

/-- The first derivative of `expo`. -/
def expoD (b c d u : ℝ) : ℝ := b-c*u⁻¹^2-2*d*u⁻¹^3

/-- The second derivative of `expo`. -/
def expoDD (c d u : ℝ) : ℝ := 2*c*u⁻¹^3+6*d*u⁻¹^4

theorem hasDerivAt_expo (a b c d : ℝ) {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (expo a b c d) (expoD b c d u) u := by
  have hi := hasDerivAt_inv hu
  have h := ((((hasDerivAt_id' u).const_mul b).const_add a).add (hi.const_mul c)).add
    ((hi.fun_pow 2).const_mul d)
  convert h using 1
  · rfl
  · rw [← inv_pow]
    unfold expoD
    norm_num
    ring

theorem hasDerivAt_expoD (b c d : ℝ) {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (expoD b c d) (expoDD c d u) u := by
  have hi := hasDerivAt_inv hu
  have h := (((hi.fun_pow 2).const_mul c).const_sub b).sub ((hi.fun_pow 3).const_mul (2*d))
  convert h using 1
  · rfl
  · rw [← inv_pow]
    unfold expoDD
    norm_num
    ring

theorem hasDerivAt_expTerm (a b c d : ℝ) {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (fun v => exp (expo a b c d v)) (exp (expo a b c d u)*expoD b c d u) u :=
  (hasDerivAt_expo a b c d hu).exp

theorem hasDerivAt_expTermD (a b c d : ℝ) {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (fun v => exp (expo a b c d v)*expoD b c d v)
      (exp (expo a b c d u)*expoD b c d u*expoD b c d u+exp (expo a b c d u)*expoDD c d u) u :=
  (hasDerivAt_expTerm a b c d hu).mul (hasDerivAt_expoD b c d hu)

/-- The first exponent `1-price/(2u)`. -/
def firstExpo (k u : ℝ) : ℝ := expo (1-k^2) 0 (2*k) (-k^2) u

/-- The exponent `1-price*2^j`. -/
def tailExpo (k : ℝ) (j : ℕ) (u : ℝ) : ℝ := expo (1+4*k*2^j) (-(2*k^2*2^j)) (-(2*k^2*2^j)) 0 u

theorem firstExpo_eq (k : ℝ) {u : ℝ} (hu : u ≠ 0) : firstExpo k u = 1-dualPrice k u/(2*u) := by
  unfold firstExpo expo dualPrice
  field_simp
  ring

theorem tailExpo_eq (k : ℝ) (j : ℕ) {u : ℝ} (hu : u ≠ 0) :
    tailExpo k j u = 1-dualPrice k u*2^j := by
  unfold tailExpo expo dualPrice
  field_simp
  ring

theorem finitePartition_eq_expo (k : ℝ) {u : ℝ} (hu : u ≠ 0) :
    finitePartition 5 k u = exp (firstExpo k u)+∑ j ∈ Finset.range 5, exp (tailExpo k j u) := by
  unfold finitePartition
  rw [Fin.sum_univ_eq_sum_range (fun j => exp (1-dualPrice k u*(2 : ℝ)^j)) 5, firstExpo_eq k hu]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [tailExpo_eq k j hu]

/-- The convexified five-term partition sum. -/
def convexPart (k u : ℝ) : ℝ :=
  exp (firstExpo k u)+∑ j ∈ Finset.range 5, exp (tailExpo k j u)+25/2*u^2

/-- The first derivative of `convexPart`. -/
def convexPartD (k u : ℝ) : ℝ :=
  exp (firstExpo k u)*expoD 0 (2*k) (-k^2) u+
    ∑ j ∈ Finset.range 5, exp (tailExpo k j u)*expoD (-(2*k^2*2^j)) (-(2*k^2*2^j)) 0 u+25*u

/-- The second derivative of `convexPart`. -/
def convexPartDD (k u : ℝ) : ℝ :=
  (exp (firstExpo k u)*expoD 0 (2*k) (-k^2) u*expoD 0 (2*k) (-k^2) u+
      exp (firstExpo k u)*expoDD (2*k) (-k^2) u)+
    ∑ j ∈ Finset.range 5, (exp (tailExpo k j u)*expoD (-(2*k^2*2^j)) (-(2*k^2*2^j)) 0 u*
        expoD (-(2*k^2*2^j)) (-(2*k^2*2^j)) 0 u+
      exp (tailExpo k j u)*expoDD (-(2*k^2*2^j)) 0 u)+25

theorem hasDerivAt_convexPart (k : ℝ) {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (convexPart k) (convexPartD k u) u := by
  have h0 := hasDerivAt_expTerm (1-k^2) 0 (2*k) (-k^2) hu
  have hs := HasDerivAt.fun_sum (u := Finset.range 5) (fun j _ =>
    hasDerivAt_expTerm (1+4*k*2^j) (-(2*k^2*2^j)) (-(2*k^2*2^j)) 0 hu)
  have hq : HasDerivAt (fun y : ℝ => 25/2*y^2) (25*u) u := by
    convert (hasDerivAt_pow 2 u).const_mul (25/2 : ℝ) using 1
    norm_num
    ring
  have h := (h0.add hs).add hq
  convert h using 1
  · rfl
  · rfl

theorem hasDerivAt_convexPartD (k : ℝ) {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (convexPartD k) (convexPartDD k u) u := by
  have h0 := hasDerivAt_expTermD (1-k^2) 0 (2*k) (-k^2) hu
  have hs := HasDerivAt.fun_sum (u := Finset.range 5) (fun j _ =>
    hasDerivAt_expTermD (1+4*k*2^j) (-(2*k^2*2^j)) (-(2*k^2*2^j)) 0 hu)
  have hq : HasDerivAt (fun y : ℝ => 25*y) 25 u := by
    simpa using (hasDerivAt_id' u).const_mul (25 : ℝ)
  have h := (h0.add hs).add hq
  convert h using 1
  · rfl
  · rfl

theorem exp_neg_one_le_half : exp (-1 : ℝ) ≤ 1/2 := by
  rw [exp_neg, ← one_div]
  apply one_div_le_one_div_of_le (by norm_num)
  have := add_one_le_exp (1 : ℝ)
  linarith

theorem exp_neg_two_le_fifth : exp (-2 : ℝ) ≤ 1/5 := by
  rw [exp_neg, ← one_div]
  exact one_div_le_one_div_of_le (by norm_num) exp_two_gt_five.le

theorem convexPartDD_nonneg {k u : ℝ} (hk : sqrt 2 ≤ k) (hk' : k ≤ 31/20) (hu : 1 ≤ u) :
    0 ≤ convexPartDD k u := by
  have hu0 : 0 < u := by linarith
  have hune : u ≠ 0 := hu0.ne'
  have hk0 : 0 ≤ k := (sqrt_nonneg 2).trans hk
  have hv0 : 0 < u⁻¹ := inv_pos.mpr hu0
  have hv1 : u⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hu
  have hv3 : u⁻¹^3 ≤ 1 := pow_le_one₀ hv0.le hv1
  have hv4 : u⁻¹^4 ≤ 1 := pow_le_one₀ hv0.le hv1
  have hk2 : k^2 ≤ (31/20)^2 := pow_le_pow_left₀ hk0 hk' 2
  -- the first term
  have hs2 : (sqrt (2 : ℝ))^2 = 2 := sq_sqrt (by norm_num)
  have hk2' : 2 ≤ k^2 := by
    have := pow_le_pow_left₀ (sqrt_nonneg 2) hk 2
    linarith
  have hE0 : firstExpo k u ≤ 0 := by
    rw [firstExpo_eq k hune, first_exponent_identity k hune]
    nlinarith only [hk2',sq_nonneg (k/u-1)]
  have he0 : exp (firstExpo k u) ≤ 1 := exp_le_one_iff.mpr hE0
  have hp0 : 0 < exp (firstExpo k u) := exp_pos _
  have hD0 : -(6*k^2) ≤ expoDD (2*k) (-k^2) u := by
    unfold expoDD
    have h3 : 0 ≤ 2*(2*k)*u⁻¹^3 := by positivity
    nlinarith only [h3,hv4,sq_nonneg k]
  have hfirst : -(6*k^2) ≤ exp (firstExpo k u)*expoD 0 (2*k) (-k^2) u*expoD 0 (2*k) (-k^2) u+
      exp (firstExpo k u)*expoDD (2*k) (-k^2) u := by
    have hsq : 0 ≤ exp (firstExpo k u)*expoD 0 (2*k) (-k^2) u*expoD 0 (2*k) (-k^2) u := by
      rw [mul_assoc]
      exact mul_nonneg hp0.le (mul_self_nonneg _)
    have hm := mul_le_mul_of_nonneg_left hD0 hp0.le
    nlinarith only [hsq,hm,he0,hp0,sq_nonneg k]
  -- the tail terms
  have htail (j : ℕ) : -(2*k^2*(2/5 : ℝ)^j) ≤
      exp (tailExpo k j u)*expoD (-(2*k^2*2^j)) (-(2*k^2*2^j)) 0 u*
        expoD (-(2*k^2*2^j)) (-(2*k^2*2^j)) 0 u+
      exp (tailExpo k j u)*expoDD (-(2*k^2*2^j)) 0 u := by
    have hpj : 0 < exp (tailExpo k j u) := exp_pos _
    have hej : exp (tailExpo k j u) ≤ 1/2*(1/5 : ℝ)^j := by
      rw [tailExpo_eq k j hune]
      calc
        _ ≤ exp (-1)*(exp (-2))^j := exponential_term_bound (dualPrice_ge_two hk hu) j
        _ ≤ _ := by
          apply mul_le_mul exp_neg_one_le_half
            (pow_le_pow_left₀ (exp_pos _).le exp_neg_two_le_fifth j) (by positivity) (by norm_num)
    have hDj : -(4*k^2*2^j) ≤ expoDD (-(2*k^2*2^j)) 0 u := by
      unfold expoDD
      have h2 : 0 ≤ k^2*(2 : ℝ)^j := by positivity
      nlinarith only [h2,hv3,hv0]
    have hsq : 0 ≤ exp (tailExpo k j u)*expoD (-(2*k^2*2^j)) (-(2*k^2*2^j)) 0 u*
        expoD (-(2*k^2*2^j)) (-(2*k^2*2^j)) 0 u := by
      rw [mul_assoc]
      exact mul_nonneg hpj.le (mul_self_nonneg _)
    have hm := mul_le_mul_of_nonneg_left hDj hpj.le
    have hc : 0 ≤ 4*k^2*(2 : ℝ)^j := by positivity
    have hm2 := mul_le_mul_of_nonneg_left hej hc
    have he : 4*k^2*(2 : ℝ)^j*(1/2*(1/5)^j) = 2*k^2*(2/5)^j := by
      rw [div_pow, div_pow, one_pow]
      field_simp
      ring
    nlinarith only [hsq,hm,hm2,he]
  have hsum := Finset.sum_le_sum (s := Finset.range 5) (fun j _ => htail j)
  have hgeo : ∑ j ∈ Finset.range 5, -(2*k^2*(2/5 : ℝ)^j) = -(2*k^2*(1031/625)) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    ring
  rw [hgeo] at hsum
  unfold convexPartDD
  nlinarith only [hfirst,hsum,hk2]

theorem convexPart_convexOn {k : ℝ} (hk : sqrt 2 ≤ k) (hk' : k ≤ 31/20) :
    ConvexOn ℝ (Set.Icc 1 (31/20)) (convexPart k) := by
  have hint : interior (Set.Icc (1 : ℝ) (31/20)) = Set.Ioo 1 (31/20) := interior_Icc
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 1 (31/20))
  · intro u hu
    exact (hasDerivAt_convexPart k (by linarith [hu.1] : u ≠ 0)).continuousAt.continuousWithinAt
  · intro u hu
    rw [hint] at hu
    exact (hasDerivAt_convexPart k (by linarith [hu.1] : u ≠ 0)).hasDerivWithinAt
  · intro u hu
    rw [hint] at hu
    exact (hasDerivAt_convexPartD k (by linarith [hu.1] : u ≠ 0)).hasDerivWithinAt
  · intro u hu
    rw [hint] at hu
    exact convexPartDD_nonneg hk hk' hu.1.le

theorem convexPart_eq (k : ℝ) {u : ℝ} (hu : u ≠ 0) :
    convexPart k u = finitePartition 5 k u+25/2*u^2 := by
  rw [finitePartition_eq_expo k hu]
  rfl

theorem chord_bound {k l r u : ℝ} (hk : sqrt 2 ≤ k) (hk' : k ≤ 31/20) (hl : 1 ≤ l)
    (hr : r ≤ 31/20) (hlu : l ≤ u) (hur : u ≤ r) :
    finitePartition 5 k u ≤
      max (finitePartition 5 k l) (finitePartition 5 k r)+25*(r-l)^2/8 := by
  rcases eq_or_lt_of_le (hlu.trans hur) with hlr | hlr
  · have hul : u = l := le_antisymm (hlr ▸ hur) hlu
    rw [hul, ← hlr]
    have := le_max_left (finitePartition 5 k l) (finitePartition 5 k l)
    nlinarith only [this]
  have hd : 0 < r-l := by linarith
  set a := (r-u)/(r-l) with ha
  set b := (u-l)/(r-l) with hb
  have ha0 : 0 ≤ a := div_nonneg (by linarith) hd.le
  have hb0 : 0 ≤ b := div_nonneg (by linarith) hd.le
  have hab : a+b = 1 := by
    rw [ha, hb, ← add_div]
    exact (div_eq_one_iff_eq hd.ne').mpr (by ring)
  have hu' : a*l+b*r = u := by
    rw [ha, hb]
    field_simp
    ring
  have hlm : l ∈ Set.Icc (1 : ℝ) (31/20) := ⟨hl, by linarith⟩
  have hrm : r ∈ Set.Icc (1 : ℝ) (31/20) := ⟨by linarith, hr⟩
  have hc := (convexPart_convexOn hk hk').2 hlm hrm ha0 hb0 hab
  simp only [smul_eq_mul] at hc
  rw [hu'] at hc
  rw [convexPart_eq k (by linarith : u ≠ 0), convexPart_eq k (by linarith : l ≠ 0),
    convexPart_eq k (by linarith : r ≠ 0)] at hc
  have hkey : a*l^2+b*r^2-u^2 = (u-l)*(r-u) := by
    rw [← hu', ha, hb]
    field_simp
    ring
  have hq : (u-l)*(r-u) ≤ (r-l)^2/4 := by nlinarith only [sq_nonneg (2*u-l-r)]
  have hm1 := mul_le_mul_of_nonneg_left (le_max_left (finitePartition 5 k l)
    (finitePartition 5 k r)) ha0
  have hm2 := mul_le_mul_of_nonneg_left (le_max_right (finitePartition 5 k l)
    (finitePartition 5 k r)) hb0
  have hM : a*max (finitePartition 5 k l) (finitePartition 5 k r)+
      b*max (finitePartition 5 k l) (finitePartition 5 k r) =
      max (finitePartition 5 k l) (finitePartition 5 k r) := by
    rw [← add_mul, hab, one_mul]
  linarith only [hc, hkey, hq, hm1, hm2, hM]

end ThresholdHC.QuantileFactorUpper
