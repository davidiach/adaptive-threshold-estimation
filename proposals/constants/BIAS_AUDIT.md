# Bias audit of the constant search

Evidence labels below distinguish mathematical arguments from finite-grid
floating-point results. The frozen evaluator and acceptance rule are unchanged.

## A smaller threshold that preserves the v4 bias theorem

**Status: proved on paper**, using Hoeffding's inequality. Not Lean-checked.

Let the dyadic-cap classifier use threshold
`t(n,N) = sqrt((k1 + k2 log(N/n))/n)`, with `k1 >= 0`, `k2 >= 1`.
For either sign, its error probability obeys the original v4 bound

`e_N <= min(1, (N d^2)^(-2))`.

Indeed, an incorrect early stop at a dyadic prefix `n<N` requires the
empirical mean to deviate from its true mean by at least `d+t(n,N)`.
Hoeffding and `(d+t)^2 >= d^2+t^2` give probability at most

`exp(-2 n d^2) exp(-2 k1) (n/N)^(2 k2)`.

Since `n/N<1` and `k2>=1`, this is at most
`exp(-2 k1) N^(-2) n^2 exp(-2 n d^2)`. A wrong cap decision has
probability at most `exp(-2 N d^2)`; the convention for ties only weakens
these bounds. A union bound over all potential early stops is valid even
though stopping is adaptive.

For every `b>0`, on each interval `[n/2,n]` with dyadic `n`,

`integral x exp(-b x) dx >= exp(-b n) * 3 n^2 / 8`.

The intervals are disjoint, so summing and extending the integral to
`(0,infinity)` gives `sum n^2 exp(-b n) <= 8/(3 b^2)`.
With `b=2d^2` and `x=Nd^2`, it follows that

`e_N <= exp(-2x) + (2/3) exp(-2 k1) x^(-2)`.

For `x>=1`, the derivative of `x^2 exp(-2x)` is nonpositive, hence
`x^2 e_N <= exp(-2)+(2/3)exp(-2k1) <= exp(-2)+2/3 < 1`.
For `x<1`, use `e_N<=1`. This proves the claim uniformly over caps and
magnitudes, rather than just on the frozen grid.

Thus `(k1,k2)=(1/4,1)` is a theory-compatible candidate. Lowering `k1`
also cannot increase either classifier's stopping time on the same data
stream. This argument does **not** prove that its finite-grid variance-work
proxy is a uniform variance-work constant; that remains to be analyzed.

## The finite-grid winner violates the uniform bias theorem

**Status: proved on paper**, with exact rational arithmetic checks in
`bias_audit.py`. Not Lean-checked.

For `(k1,k2)=(1/4,1/2)`, choose positive sign, `d=1/10`, cap `N=2^97`,
and consider the event that the first 128 potential flips are all tails.
The event has probability `(2/5)^128`. At every inspected prefix the
empirical mean is zero, so this trajectory can never stop positively.
At `n=128=2^7`, the threshold satisfies

`n t(n,N)^2 = 1/4 + (90/2) log 2 < 1/4+45(7/10) = 127/4 < 32 = n/4`.

Consequently it has stopped negatively by that time. The elementary bound
`log 2 < 7/10` follows from the first five terms of the positive Taylor
series for `exp(7/10)`, whose sum already exceeds 2.

Therefore `e_N >= (2/5)^128`, whereas the proposed v4 bound is
`(Nd^2)^(-2)=10000/2^194`. Exact integer comparison shows that their ratio
exceeds **2907**. This is a concrete counterexample, not a large-cap
floating-point extrapolation.

The cap is deliberately outside the frozen evaluator's range `N<=4096`.
The finite-grid winner can legitimately pass that scorer, but cannot inherit
the v4 uniform bias theorem. No claim of a uniform variance-work constant or
replacement theorem is justified by the grid score. It may have other useful
bias rates; those are not established here.
