import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic

/-! Rational certificates are checked by rational comparisons. Their soundness
is a theorem about real arithmetic; neither a Python evaluator nor a native
decision procedure is used in the proof. -/

namespace ThresholdHC.DeterministicCertificates

structure Interval where
  lower : ℚ
  upper : ℚ
  deriving DecidableEq, Repr

def Contains (i : Interval) (x : ℝ) : Prop := (i.lower : ℝ) ≤ x ∧ x ≤ (i.upper : ℝ)

def point (q : ℚ) : Interval := ⟨q,q⟩
def add (a b : Interval) : Interval := ⟨a.lower+b.lower,a.upper+b.upper⟩
def scale (q : ℚ) (a : Interval) : Interval :=
  if 0 ≤ q then ⟨q*a.lower,q*a.upper⟩ else ⟨q*a.upper,q*a.lower⟩
def imin (a b : Interval) : Interval := ⟨min a.lower b.lower,min a.upper b.upper⟩
def imax (a b : Interval) : Interval := ⟨max a.lower b.lower,max a.upper b.upper⟩
def encloses (outer inner : Interval) : Bool :=
  decide (outer.lower ≤ inner.lower ∧ inner.upper ≤ outer.upper)

theorem point_sound (q : ℚ) : Contains (point q) (q : ℝ) := ⟨le_rfl,le_rfl⟩

theorem add_sound {a b : Interval} {x y : ℝ} (ha : Contains a x) (hb : Contains b y) :
    Contains (add a b) (x+y) := by
  simpa [Contains,add] using And.intro (add_le_add ha.1 hb.1) (add_le_add ha.2 hb.2)

theorem scale_sound (q : ℚ) {a : Interval} {x : ℝ} (ha : Contains a x) :
    Contains (scale q a) ((q:ℝ)*x) := by
  unfold scale
  split_ifs with h
  · have hq : (0:ℝ) ≤ q := by exact_mod_cast h
    exact ⟨by simpa using mul_le_mul_of_nonneg_left ha.1 hq,
      by simpa using mul_le_mul_of_nonneg_left ha.2 hq⟩
  · have hq : (q:ℝ) ≤ 0 := by exact_mod_cast (le_of_not_ge h)
    exact ⟨by simpa using mul_le_mul_of_nonpos_left ha.2 hq,
      by simpa using mul_le_mul_of_nonpos_left ha.1 hq⟩

theorem min_sound {a b : Interval} {x y : ℝ} (ha : Contains a x) (hb : Contains b y) :
    Contains (imin a b) (min x y) := by
  simpa [Contains,imin] using And.intro (min_le_min ha.1 hb.1) (min_le_min ha.2 hb.2)

theorem max_sound {a b : Interval} {x y : ℝ} (ha : Contains a x) (hb : Contains b y) :
    Contains (imax a b) (max x y) := by
  simpa [Contains,imax] using And.intro (max_le_max ha.1 hb.1) (max_le_max ha.2 hb.2)

theorem encloses_sound {outer inner : Interval} {x : ℝ}
    (h : encloses outer inner = true) (hi : Contains inner x) : Contains outer x := by
  have h' : outer.lower ≤ inner.lower ∧ inner.upper ≤ outer.upper := by simpa [encloses] using h
  exact ⟨(show (outer.lower:ℝ) ≤ inner.lower by exact_mod_cast h'.1).trans hi.1,
    hi.2.trans (by exact_mod_cast h'.2)⟩

def sqrtCheck (input output : Interval) : Bool :=
  decide (0 ≤ input.lower ∧ 0 ≤ output.lower ∧ 0 ≤ output.upper ∧
    output.lower^2 ≤ input.lower ∧ input.upper ≤ output.upper^2)

theorem sqrtCheck_sound {input output : Interval} {x : ℝ}
    (h : sqrtCheck input output = true) (hi : Contains input x) : Contains output (Real.sqrt x) := by
  have hq : 0 ≤ input.lower ∧ 0 ≤ output.lower ∧ 0 ≤ output.upper ∧
      output.lower^2 ≤ input.lower ∧ input.upper ≤ output.upper^2 := by simpa [sqrtCheck] using h
  have hr : (0:ℝ) ≤ input.lower ∧ 0 ≤ (output.lower:ℝ) ∧ 0 ≤ (output.upper:ℝ) ∧
      (output.lower:ℝ)^2 ≤ input.lower ∧ (input.upper:ℝ) ≤ (output.upper:ℝ)^2 := by exact_mod_cast hq
  have hx : 0 ≤ x := hr.1.trans hi.1
  have hs := Real.sq_sqrt hx
  have hn := Real.sqrt_nonneg x
  constructor <;> nlinarith [hi.1,hi.2,hr.2.1,hr.2.2.1,hr.2.2.2.1,hr.2.2.2.2]

/-- A checked absolute and relative width contract for a square-root enclosure. -/
def sqrtPrecisionCheck (x tolerance : ℚ) (output : Interval) : Bool :=
  decide (0 ≤ tolerance ∧ 0 ≤ output.upper-output.lower ∧
    output.upper-output.lower ≤ tolerance ∧
    (output.upper-output.lower)^2 ≤ tolerance^2*x)

theorem sqrtPrecisionCheck_sound {x tolerance : ℚ} {output : Interval}
    (h : sqrtPrecisionCheck x tolerance output = true) (hx : 0 ≤ x) :
    (output.upper-output.lower:ℝ) ≤ (tolerance:ℝ)*min 1 (Real.sqrt (x:ℝ)) := by
  have hq : 0 ≤ tolerance ∧ 0 ≤ output.upper-output.lower ∧
      output.upper-output.lower ≤ tolerance ∧
      (output.upper-output.lower)^2 ≤ tolerance^2*x := by simpa [sqrtPrecisionCheck] using h
  have hr : (0:ℝ) ≤ tolerance ∧ 0 ≤ (output.upper-output.lower:ℝ) ∧
      (output.upper-output.lower:ℝ) ≤ tolerance ∧
      (output.upper-output.lower:ℝ)^2 ≤ (tolerance:ℝ)^2*(x:ℝ) := by exact_mod_cast hq
  rw [mul_min_of_nonneg _ _ hr.1,mul_one]
  refine le_min hr.2.2.1 ?_
  have hs : ((tolerance:ℝ)*Real.sqrt (x:ℝ))^2 = (tolerance:ℝ)^2*(x:ℝ) := by
    rw [mul_pow,Real.sq_sqrt (show (0:ℝ) ≤ x by exact_mod_cast hx)]
  have hn := mul_nonneg hr.1 (Real.sqrt_nonneg (x:ℝ))
  nlinarith [hr.2.1,hr.2.2.2]

end ThresholdHC.DeterministicCertificates
