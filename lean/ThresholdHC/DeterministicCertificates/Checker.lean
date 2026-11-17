import ThresholdHC.DeterministicCertificates.Logarithm

namespace ThresholdHC.DeterministicCertificates

/-- A public exact input expression, separate from its proposed numerical bounds. -/
inductive Expr where
  | rational (q : ℚ)
  | add (a b : Expr)
  | scale (q : ℚ) (a : Expr)
  | minimum (a b : Expr)
  | maximum (a b : Expr)
  | sqrt (a : Expr)
  | log (a : Expr)
  deriving DecidableEq, Repr

noncomputable def Expr.eval : Expr → ℝ
  | .rational q => q
  | .add a b => a.eval+b.eval
  | .scale q a => (q:ℝ)*a.eval
  | .minimum a b => min a.eval b.eval
  | .maximum a b => max a.eval b.eval
  | .sqrt a => Real.sqrt a.eval
  | .log a => Real.log a.eval

/-- Untrusted proposed intervals. The checker also checks every intermediate
interval; it never infers validity from the producer's identity or a digest. -/
inductive Evidence where
  | leaf (output : Interval)
  | unary (output : Interval) (child : Evidence)
  | binary (output : Interval) (left right : Evidence)
  | logarithm (output : Interval) (lower upper : LogWitness) (child : Evidence)
  deriving DecidableEq, Repr

def Evidence.bounds : Evidence → Interval
  | .leaf o => o
  | .unary o _ => o
  | .binary o _ _ => o
  | .logarithm o _ _ _ => o

/-- A terminating rational checker. Unsupported tree shapes and uncertified
transcendental domains are rejected, rather than assigned a default bound. -/
def check : Expr → Evidence → Bool
  | .rational q, .leaf o => encloses o (point q)
  | .add a b, .binary o ca cb =>
      check a ca && check b cb && encloses o (add ca.bounds cb.bounds)
  | .scale q a, .unary o ca => check a ca && encloses o (scale q ca.bounds)
  | .minimum a b, .binary o ca cb =>
      check a ca && check b cb && encloses o (imin ca.bounds cb.bounds)
  | .maximum a b, .binary o ca cb =>
      check a ca && check b cb && encloses o (imax ca.bounds cb.bounds)
  | .sqrt a, .unary o ca => check a ca && sqrtCheck ca.bounds o
  | .log a, .logarithm o lower upper ca => check a ca && logCheck ca.bounds o lower upper
  | _, _ => false

/-- Universal soundness of the executable checker, for every expression and
every proposed certificate, not just the regression examples. -/
theorem check_sound (e : Expr) (c : Evidence) (h : check e c = true) :
    Contains c.bounds e.eval := by
  induction e generalizing c with
  | rational q =>
    cases c <;> simp only [check,Bool.false_eq_true] at h
    exact encloses_sound h (point_sound q)
  | add a b ia ib =>
    cases c <;> simp only [check,Bool.false_eq_true,Bool.and_eq_true] at h
    exact encloses_sound h.2 (add_sound (ia _ h.1.1) (ib _ h.1.2))
  | scale q a ia =>
    cases c <;> simp only [check,Bool.false_eq_true,Bool.and_eq_true] at h
    exact encloses_sound h.2 (scale_sound q (ia _ h.1))
  | minimum a b ia ib =>
    cases c <;> simp only [check,Bool.false_eq_true,Bool.and_eq_true] at h
    exact encloses_sound h.2 (min_sound (ia _ h.1.1) (ib _ h.1.2))
  | maximum a b ia ib =>
    cases c <;> simp only [check,Bool.false_eq_true,Bool.and_eq_true] at h
    exact encloses_sound h.2 (max_sound (ia _ h.1.1) (ib _ h.1.2))
  | sqrt a ia =>
    cases c <;> simp only [check,Bool.false_eq_true,Bool.and_eq_true] at h
    exact sqrtCheck_sound h.2 (ia _ h.1)
  | log a ia =>
    cases c <;> simp only [check,Bool.false_eq_true,Bool.and_eq_true] at h
    exact logCheck_sound h.2 (ia _ h.1)

def accepted (e : Expr) (claimed : Interval) (c : Evidence) : Bool :=
  decide (c.bounds = claimed) && check e c

/-- The external claimed result must equal the checked root interval. -/
theorem accepted_sound {e : Expr} {claimed : Interval} {c : Evidence}
    (h : accepted e claimed c = true) : Contains claimed e.eval := by
  simp only [accepted,Bool.and_eq_true,decide_eq_true_eq] at h
  rw [← h.1]
  exact check_sound e c h.2

end ThresholdHC.DeterministicCertificates
