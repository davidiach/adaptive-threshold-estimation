import Mathlib.Tactic

/-! Integer polynomial arithmetic and a positivity certificate on a rational interval. -/
namespace ThresholdHC.SharpRMS.Revisit.IntPoly
abbrev Coeffs := List ℤ

def value : Coeffs → ℝ → ℝ
  | [], _ => 0
  | a::as, x => (a:ℝ)+x*value as x

def add : Coeffs → Coeffs → Coeffs
  | [], b => b
  | a, [] => a
  | a::as, b::bs => (a+b)::add as bs

def scale (a : ℤ) (l : Coeffs) := l.map (a*·)

def mul : Coeffs → Coeffs → Coeffs
  | [], _ => []
  | a::as, b => add (scale a b) (0::mul as b)

def power (l : Coeffs) : ℕ → Coeffs
  | 0 => [1]
  | n+1 => mul l (power l n)

def sumTo (f : ℕ → Coeffs) : ℕ → Coeffs
  | 0 => []
  | n+1 => add (sumTo f n) (f n)

@[simp] theorem value_add (a b : Coeffs) (x : ℝ) : value (add a b) x=value a x+value b x := by
  induction a generalizing b with
  | nil => simp [add,value]
  | cons a l ih =>
    cases b with
    | nil => simp [add,value]
    | cons b m => simp [add,value,ih]; ring

@[simp] theorem value_scale (a : ℤ) (l : Coeffs) (x : ℝ) : value (scale a l) x=a*value l x := by
  induction l with
  | nil => simp [scale,value]
  | cons b l ih => change (↑(a*b):ℝ)+x*value (scale a l) x=_; rw [Int.cast_mul,ih]; simp [value]; ring

@[simp] theorem value_mul (a b : Coeffs) (x : ℝ) : value (mul a b) x=value a x*value b x := by
  induction a with
  | nil => simp [mul,value]
  | cons a as ih => simp [mul,value,ih]; ring

@[simp] theorem value_power (a : Coeffs) (n : ℕ) (x : ℝ) : value (power a n) x=(value a x)^n := by
  induction n with
  | zero => simp [power,value]
  | succ n ih => simp [power,ih,pow_succ,mul_comm]

@[simp] theorem value_sumTo (f : ℕ → Coeffs) (n : ℕ) (x : ℝ) :
    value (sumTo f n) x=∑ i ∈ Finset.range n, value (f i) x := by
  induction n with
  | zero => simp [sumTo,value]
  | succ n ih => simp [sumTo,ih,Finset.sum_range_succ]

/-- Clear the denominator after substituting the ratio of two linear polynomials. -/
def homogeneous (u v : Coeffs) : Coeffs → Coeffs
  | [] => []
  | a::as => add (scale a (power v (as.length+1))) (mul u (homogeneous u v as))

theorem value_homogeneous (a u v : Coeffs) (x : ℝ) (hv : value v x≠0) :
    value (homogeneous u v a) x=(value v x)^a.length*value a (value u x/value v x) := by
  induction a with
  | nil => simp [homogeneous,value]
  | cons a as ih =>
    simp only [homogeneous,value_add,value_scale,value_power,value_mul,ih,List.length_cons,value,pow_succ]
    field_simp

private theorem value_nonneg (a : Coeffs) (x : ℝ) (hx : 0≤x) (h : ∀ c∈a, 0≤c) : 0≤value a x := by
  induction a with
  | nil => exact le_rfl
  | cons c cs ih =>
    exact add_nonneg (by exact_mod_cast h c (by simp)) (mul_nonneg hx (ih (fun d hd => h d (by simp [hd]))))

def intervalCheck (a : Coeffs) (i m : ℕ) :=
  (homogeneous [(i:ℤ),i+1] [(m:ℤ),m] a).all (fun z => decide (0≤z))

theorem interval_sound (a : Coeffs) (i m : ℕ) (hm : 0<m) (cert : intervalCheck a i m=true)
    (p : ℝ) (hl : (i:ℝ)≤m*p) (hr : m*p < i+1) : 0≤value a p := by
  let y := (m*p-i)/(i+1-m*p)
  have den : 0<(i:ℝ)+1-m*p := by linarith
  have hy : 0≤y := div_nonneg (sub_nonneg.mpr hl) den.le
  let u : Coeffs := [i,i+1]
  let v : Coeffs := [m,m]
  have mp : (0:ℝ) < m := by exact_mod_cast hm
  have vp : 0<value v y := by simp [v,value]; positivity
  have repr : value u y/value v y=p := by
    apply (div_eq_iff vp.ne').2
    simp [u,v,value,y]; field_simp [den.ne']; ring
  have good : ∀ z∈homogeneous u v a, (0:ℤ)≤z := by
    simpa [intervalCheck,u,v,List.all_eq_true] using cert
  have pos := value_nonneg _ y hy good
  rw [value_homogeneous _ _ _ _ vp.ne',repr] at pos
  exact nonneg_of_mul_nonneg_right pos (pow_pos vp _)

end ThresholdHC.SharpRMS.Revisit.IntPoly
