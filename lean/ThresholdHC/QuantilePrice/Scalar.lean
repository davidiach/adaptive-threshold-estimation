import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

noncomputable section
open Real
namespace ThresholdHC.QuantilePrice

private theorem quadratic_nonneg {A B C : ℝ} (hA : 0 < A) (hd : B^2 ≤ 4*A*C) (w x : ℝ) :
    0 ≤ A*w^2+B*w*x+C*x^2 := by
  apply nonneg_of_mul_nonneg_right (a := 4*A) _ (by positivity)
  nlinarith only [sq_nonneg (2*A*w+B*x),mul_nonneg (sub_nonneg.mpr hd) (sq_nonneg x)]

/-- Positivity certificate after the homogeneous change of variables w = y - x/3. -/
theorem price_quartic (x y : ℝ) :
    0 ≤ 16*(31/20:ℝ)^4*(x^2+y^2)^2 -
      (4*(31/20)*(x^2+y^2)+(37/40*x+77/80*y)^2)^2 - 16*(31/20)^2*x^2*(x^2+y^2) := by
  let w := y-x/3
  have h₁ := quadratic_nonneg (A := 340512227/8192000) (B := 922920889/30720000)
    (C := 6) (by norm_num) (by norm_num) w x
  have h₂ := quadratic_nonneg (A := 551277971/12288000-6) (B := 255898057/276480000)
    (C := 177573199/3317760000) (by norm_num) (by norm_num) w x
  convert add_nonneg (mul_nonneg (sq_nonneg w) h₁) (mul_nonneg (sq_nonneg x) h₂) using 1
  dsimp [w]; ring

private theorem price_dual {x y : ℝ} (h : x^2+y^2=1) :
    (1+(37/40*x+77/80*y)^2/(4*(31/20)))^2+x^2 ≤ (31/20)^2 := by
  have hp := price_quartic x y
  rw [h] at hp
  ring_nf at hp ⊢
  linarith only [hp]

/-- Support-function form of the scalar price bound; all zero cases are included. -/
theorem scalar_price (T v c : ℝ) (hT : 0 ≤ T) (hv : 0 ≤ v) (hc : 0 ≤ c) :
    T+sqrt ((v+37/40*sqrt (T*c))^2+(77/80*sqrt (T*c))^2) ≤
      (31/20)*(sqrt (T^2+v^2)+c) := by
  let z := sqrt (T*c)
  let p := v+37/40*z
  let q := 77/80*z
  let s := sqrt (p^2+q^2)
  let r := sqrt (T^2+v^2)
  have hs : 0 ≤ s := sqrt_nonneg _
  have hs2 : s^2=p^2+q^2 := sq_sqrt (by positivity)
  have hr : 0 ≤ r := sqrt_nonneg _
  have hr2 : r^2=T^2+v^2 := sq_sqrt (by positivity)
  change T+s ≤ (31/20)*(r+c)
  by_cases he : s=0
  · have hTr : T ≤ r := (sq_le_sq₀ hT hr).mp (by linarith [sq_nonneg v])
    linarith
  let x := p/s
  let y := q/s
  have hunit : x^2+y^2=1 := by
    dsimp only [x,y]
    field_simp [he]
    linarith
  have hx : 0 ≤ x := by dsimp only [x,p,z]; positivity
  let d := 37/40*x+77/80*y
  let a := 1+d^2/(4*(31/20))
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hab : a^2+x^2 ≤ (31/20)^2 := price_dual hunit
  have hdot : a*T+x*v ≤ (31/20)*r := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    have h := mul_le_mul_of_nonneg_right hab (show 0 ≤ r^2 by positivity)
    rw [hr2] at h
    nlinarith only [h,sq_nonneg (a*v-x*T),hr2]
  have hyoung : d*z ≤ d^2*T/(4*(31/20))+(31/20)*c := by
    change d*sqrt (T*c) ≤ _
    rw [sqrt_mul hT]
    have h := sq_nonneg (2*(31/20)*sqrt c-d*sqrt T)
    ring_nf at h ⊢
    rw [sq_sqrt hc,sq_sqrt hT] at h
    linarith only [h]
  have hsrep : s=x*p+y*q := by
    dsimp only [x,y]
    field_simp [he]
    nlinarith only [hs2]
  have hex : s=x*v+d*z := by rw [hsrep]; dsimp only [p,q,d]; ring
  dsimp only [a] at hdot
  ring_nf at hdot hyoung hex ⊢
  linarith only [hdot,hyoung,hex]

end ThresholdHC.QuantilePrice
