import Mathlib.Tactic
import Mathlib.Algebra.Order.Floor.Div

/-! Algebraic form of the executable integer rectangle heights. -/
namespace ThresholdHC.SharpRMS.Window

def bins : Nat := 2048
def scale : Nat := 2^32
def biasDenominator : Nat := 40960

def posteriorParts (u w : ℕ) : ℕ → ℕ × ℕ
  | 0 => (0,1)
  | k+1 =>
    let (p,q) := posteriorParts u w k
    (p*w+q*u,q*w+p*u)

def roundUp (a b : ℕ) := (a+b-1)/b
def weight (j : ℕ) := bins^2-(j-1)^2
def signHeight (j u w : ℕ) := roundUp (scale*weight j*w^2) (bins^2*u^2)

structure Barrier where
  top : Nat
  numerator : Nat
  denominator : Nat
  slopeNumerator : Nat
  slopeDenominator : Nat
  height : Nat

def makeBarrier (u w k : ℕ) : Barrier :=
  let (p,q) := posteriorParts u w k
  let c := k*q*u-p*w
  let d := p*u
  let (a,b) := if k=20 then (1,1) else (p,q)
  ⟨scale*(b*u+a*w)*w*d,a,b,c,d,k⟩

def barrierList (u w : ℕ) := (List.range 20).reverse.map (fun i => makeBarrier u w (i+1))

def roundedExit (j u w : ℕ) (b : Barrier) :=
  let den := bins*u*(bins*b.denominator-j*b.numerator)*(bins*w+j*u)*
    (bins*b.slopeDenominator*(b.height+1)-j*b.slopeNumerator)
  if den=0 then signHeight j u w else roundUp (b.top*(weight j)^2) den

def exitHeight (j u w k : ℕ) := roundedExit j u w (makeBarrier u w k)

def maximumFor (j u w : ℕ) (prices : List Barrier) :=
  prices.foldl (fun best b => max best (roundedExit j u w b)) 0

def largestHeight (j u w : ℕ) := maximumFor j u w (barrierList u w)

def rectangleHeight (j u w : ℕ) := min (largestHeight j u w) (signHeight j u w)

def upperSum (u : ℕ) :=
  let prices := barrierList u biasDenominator
  (List.range bins).foldl (fun acc i =>
    acc+min (maximumFor (i+1) u biasDenominator prices) (signHeight (i+1) u biasDenominator)) 0

theorem roundUp_covers (a b : ℕ) (hb : 0 < b) : (a:ℝ)/(b:ℝ) ≤ (roundUp a b:ℝ) := by
  apply (div_le_iff₀ (by exact_mod_cast hb)).mpr
  exact_mod_cast (show a ≤ roundUp a b*b by simpa [roundUp,Nat.ceilDiv_eq_add_pred_div,mul_comm] using
    (le_smul_ceilDiv (α := ℕ) (b := a) hb))

theorem exit_le_largest (j u w k : ℕ) (hk : 0 < k) (hm : k ≤ 20) :
    exitHeight j u w k ≤ largestHeight j u w := by
  let f := fun i => exitHeight j u w (i+1)
  have bound (xs : List ℕ) (v : ℕ) :
      v ≤ xs.foldl (fun a i => max a (f i)) v ∧
      (∀ i ∈ xs, f i ≤ xs.foldl (fun a i => max a (f i)) v) := by
    induction xs generalizing v with
    | nil => simp
    | cons x xs ih =>
      obtain ⟨h,hs⟩ := ih (max v (f x))
      refine ⟨(le_max_left ..).trans h,?_⟩
      intro i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · exact (le_max_right ..).trans h
      · exact hs i hi
  have h := (bound (List.range 20).reverse 0).2 (k-1) (by simp; omega)
  simpa only [largestHeight,maximumFor,barrierList,List.foldl_map,Function.comp_def,exitHeight,f,
    Nat.sub_add_cancel hk] using h

end ThresholdHC.SharpRMS.Window
