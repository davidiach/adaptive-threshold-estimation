import Mathlib.Data.Nat.Factorial.Basic

/-! Executable natural-number checker for the upper end of the quantile bracket.

All quantities are natural numbers. A value `v` stands for the real number
`v / scale` with `scale = 2^100`. For a rational `x = num/den ≥ 0`, the value
`expNegUp num den s` bounds `exp (-x)` from above: the Taylor sum of `exp`
at `x/2^s` with terms rounded down bounds `exp (x/2^s)` from below, its
reciprocal is rounded up, and `s` upward-rounded squarings follow.

The grid point `a` stands for `u = a/gridDen`, with `gridDen = 20*2^24`, so
`u = 1` at `a = gridDen` and `u = 31/20` at `a = gridTop = 31*2^24`. The factor is
`k = factorNum/factorDen = 1462554551280/10^12`. The value `crit a` bounds the
five-term partition sum at `u` plus the tail allowance `2^-62`, and `certify`
bisects a cell until the larger endpoint value plus `25 w^2/8` lies below one
for the cell width `w`. -/
namespace ThresholdHC.QuantileFactorUpper

/-- The fixed-point scale `2^100`. -/
def scale : ℕ := 2^100

/-- The number of Taylor terms. -/
def terms : ℕ := 22

/-- Division rounded up. -/
def ceilDiv (a b : ℕ) : ℕ := (a+b-1)/b

/-- The first `n` Taylor terms of `exp (num/den)`, each scaled and rounded down. -/
def taylorLow (num den : ℕ) : ℕ → ℕ
  | 0 => 0
  | i+1 => taylorLow num den i + scale*num^i/(den^i*i.factorial)

/-- Upper value for `exp (-(num/den))`: the rounded-up reciprocal of `taylorLow`. -/
def expBase (num den : ℕ) : ℕ := ceilDiv (scale*scale) (taylorLow num den terms)

/-- Squaring, rounded up. -/
def squareUp (v : ℕ) : ℕ := ceilDiv (v*v) scale

/-- Iterated upward squaring. -/
def squareIter : ℕ → ℕ → ℕ
  | 0, v => v
  | t+1, v => squareUp (squareIter t v)

/-- Upper value for `exp (-(num/den))` through the argument `num/(den*2^s)`. -/
def expNegUp (num den s : ℕ) : ℕ := squareIter s (expBase num (den*2^s))

/-- Numerator of the factor `1462554551280/10^12`. -/
def factorNum : ℕ := 18281931891

/-- Denominator of the factor `1462554551280/10^12`. -/
def factorDen : ℕ := 12500000000

/-- Grid denominator: `u = a/gridDen`. -/
def gridDen : ℕ := 20*2^24

/-- Grid point of `u = 31/20`. -/
def gridTop : ℕ := 31*2^24

/-- Numerator of the dual price `2k^2(u+1/u)-4k` at `u = a/gridDen`. -/
def priceNum (a : ℕ) : ℕ :=
  2*factorNum^2*(a^2+gridDen^2)-4*factorNum*factorDen*a*gridDen

/-- Denominator of the dual price at `u = a/gridDen`. -/
def priceDen (a : ℕ) : ℕ := factorDen^2*a*gridDen

/-- Numerator of `price/(2u)-1` at `u = a/gridDen`. -/
def firstNum (a : ℕ) : ℕ :=
  factorNum^2*(a^2+gridDen^2)-2*factorNum*factorDen*a*gridDen-factorDen^2*a^2

/-- Denominator of `price/(2u)-1` at `u = a/gridDen`. -/
def firstDen (a : ℕ) : ℕ := factorDen^2*a^2

/-- Upper value for `exp (1-price*2^j)`. -/
def tailTerm (a j : ℕ) : ℕ := expNegUp (2^j*priceNum a-priceDen a) (priceDen a) (j+2)

/-- Upper value for the five-term partition sum at `u = a/gridDen`, plus `2^-62`. -/
def crit (a : ℕ) : ℕ :=
  expNegUp (firstNum a) (firstDen a) 0+
    (tailTerm a 0+tailTerm a 1+tailTerm a 2+tailTerm a 3+tailTerm a 4)+scale/2^62

/-- The cell test: larger endpoint value plus `25 w^2/8` below one. -/
def cellOK (l r : ℕ) : Bool :=
  decide (8*gridDen^2*max (crit l) (crit r)+25*(r-l)^2*scale < 8*gridDen^2*scale)

/-- Bisection with fuel `d`. -/
def certify : ℕ → ℕ → ℕ → Bool
  | 0, l, r => cellOK l r
  | d+1, l, r => cellOK l r || (certify d l ((l+r)/2) && certify d ((l+r)/2) r)

end ThresholdHC.QuantileFactorUpper
