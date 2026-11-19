# How far is the upper constant 12 from its estimator's risk?

**Status: numerical evidence only.** Floating-point computations over finite
grids, with no proof and no Lean check. Nothing here changes a claimed
result.

Lean checks the upper constant $12$ of the RMS law
([`minimax_upper_12`](../../lean/ThresholdHC/UpperScale/Full.lean),
[record](../../results/upper-scale-20261119/README.md)), and the v6 paper
proves it as Theorem AB.1. Its estimator runs one budget level
$L$, with $4\cdot2^L\le B<8\cdot2^L$, calibrated at the scale $B/4$. This
study asks two questions:

1. What is the actual worst ratio $\text{RMS}/\omega_\mu(B^{-1/2})$ of that
   estimator?
2. Could a proof by the same method reach $11$, perhaps after retuning the
   estimator's parameters?

The [earlier study](../2026-11-18-upper-constant/README.md) answered the
first question for the single-level estimator behind the constants $512$ to
$36$. This one copies its exact risk formula and extends it.

## Summary

| Quantity | Value |
|---|---:|
| Proven constant, `minimax_upper_12` | $12$ (the proof gives $\sqrt{716/5}\approx11.97$) |
| Worst point mass, exact formula, $N=2^{14}$ ($2^{16}\le B<2^{17}$) | 5.07 |
| Limit as $B\to\infty$, point masses and two-point laws | 5.37 |
| Limit of the earlier single-level estimator, for comparison | 7.57 |
| Lean's method with exact sums in place of its certificates, paper's thresholds | 11.20 |
| The same, with a bias bound near $1/2$ in place of $1$ | 10.85 to 10.93 |
| The same method, thresholds retuned to $a=2$, $b=1/2$ | 10.33 |
| The proof route with exact one-coin constants | 5.6 to 5.75 |

The constant $12$ is about $2.2$ times the actual worst ratio. With the
paper's thresholds, Lean's method cannot reach $11$ unless the bias bound is
also sharpened, and even then its certificates would have to be within
$1.4$ to $2.9\%$ of the exact sums; they are now $15\%$ above. Retuned
thresholds leave room for $11$, but the estimator would then differ from the
frozen Lean construction and need a new realization. The large gain is in
sharper one-coin bounds, not in retuning.

## The estimator and its exact risk

Write $N=2^L$ and $\lambda=B/(4N)\in[1,2)$. Each call draws a coin and a
level $J$ with $\Pr(J=l)=p_l=(1-r)r^l$, $r=2^{-1/2}$. It runs two
early-stopping majority classifiers with caps $2^l$ and $2^{l-1}$ on the same
flips and returns $V=(Z_l-Z_{l-1})/p_l$. A level above $L$ costs one flip and
returns $0$. The classifier with cap $M$ looks at the prefixes
$n=1,2,4,\dots$ and stops at the first one whose success fraction differs
from $1/2$ by more than
$$t_{n,M}=\sqrt{\frac{a+b\log(M/n)}{n}}.$$
The paper and Lean use $a=b=1$; this study also varies $a$ and $b$. By the
calibration lemma (v6 Lemma 5.1) at scale $\lambda N=B/4$, the raw output has

$$\text{MSE}=(\mathbb E Z_L-\theta)^2+\bigl(\mathbb E V^2-(\mathbb E Z_L)^2\bigr)\frac{c}{\lambda N},$$

where $c$ is the mean padded cost of one call and $\theta$ the fraction of
positive coins. [blind12.py](blind12.py) computes every term exactly, up to
rounding, by the dynamic program of the earlier study, which that study
cross-checked against simulation of the toolkit implementation. Its values
at $a=b=1$ agree with the earlier study's.

Fix a gap law with finitely many atoms and let $B$ grow. For $b>1/4$ the
bias falls faster than $\omega_\mu(B^{-1/2})$, and the ratio tends to
$$\frac{2\sqrt{\operatorname{Var}V\cdot c}}{\mathbb E[1/D]},$$
with $\operatorname{Var}V$ and $c$ summed over all levels. For a point
mass this is $2d\sqrt{\operatorname{Var}V\cdot c}$. The factor $2=\sqrt4$
comes from the calibration at $B/4$. The earlier estimator had $\sqrt8$
here, because its budget could run to nearly twice what it used.

## The actual worst ratio

**Point masses** ([scan_scaled.py](scan_scaled.py),
[scan_scaled.json](scan_scaled.json)). The scan covers 70 gaps per level, 41
sign fractions and 9 values of $\lambda$ in $[1,2)$. The level $L$ covers
the budgets $4\cdot2^L\le B<8\cdot2^L$.

| $L$ | 0 | 2 | 4 | 6 | 8 | 10 | 12 | 13 | 14 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Worst RMS$/\omega(B^{-1/2})$ | 1.55 | 2.03 | 2.90 | 3.71 | 4.24 | 4.63 | 4.89 | 4.99 | 5.07 |
| Worst gap $d$ | 0.50 | 0.47 | 0.41 | 0.32 | 0.28 | 0.24 | 0.21 | 0.20 | 0.20 |

Every coin is on the positive side in the worst case. At every level the
worst ratio is the same for every $\lambda$ to four decimals: it comes from
the variance term, which does not depend on $\lambda$ once $d\ge B^{-1/2}$.

**The limit** ([limit12.py](limit12.py), [limit12.json](limit12.json)). For
36 gaps from $0.005$ to $0.5$, the per-gap sums run to
$\lceil\log_2(1/d^2)\rceil+36$ levels. The limit ratio peaks at $5.365$ near
$d=0.12$, with all signs positive. The earlier study's $G(0.12)=2.677$
summed to 26 levels; all levels give $2.683$.

**Two-point laws.** In the limit, the scan pairs any two of the 36 gaps,
with 199 weights and five sign fractions per atom. No two-point law exceeds
the worst point mass. At finite budgets
([scan_finite.py](scan_finite.py), [scan_finite.json](scan_finite.json)),
with 16 gaps, 19 weights, three sign fractions per atom and three values of
$\lambda$, the worst two-point law exceeds the worst point mass of the same
grid only at $L=4$, by $0.4\%$ ($2.828$ against $2.817$). Both stay below
the finer point-mass scan ($2.90$). At $L=6$ to $12$ point masses are worst.

So the actual worst ratio rises with the budget toward about $5.37$; $12$ is
$2.24$ times that limit.

## Where the proof's 12 goes

The Lean proof bounds three things separately:

- the bias, by $\beta\,\omega_\mu(N^{-1/2})$ with $\beta=1$;
- the second moment, $\mathbb E V^2\le\sigma A$ with $\sigma=13/2$, and the
  padded call cost, $c\le\kappa A$ with $\kappa=26/5$, where
  $A=\mathbb E_\mu\min(\sqrt N,1/D)$. Regime terms adjust both bounds when
  $Nd^2\le1$; their product is still at most $\tfrac{169}{5}A^2$;
- the modulus, by $\omega_\mu(N^{-1/2})^2\le4\lambda\,\omega_\mu(B^{-1/2})^2$.

So $\text{MSE}\le(4\lambda\beta^2+4\sigma\kappa)\,\omega_\mu(B^{-1/2})^2$,
and with $\lambda<2$ the constant is $C=\sqrt{8\beta^2+4\sigma\kappa}$. Lean
has $8+135.2=143.2$, so $C\approx11.97$. For $11$ the sum must be at most
$121$.

**The method's limit** ([hoeffding.py](hoeffding.py),
[params12.py](params12.py), [params12.json](params12.json)). The Lean
constants are rational certificates for Hoeffding bounds, union bounds and
the exact vote-change probability $a(1-a)\le1/4$. Evaluating those same
bounds with exact sums and the best split at every level gives
$\kappa_H=4.895$ and $\sigma_H=5.996$ at the paper's thresholds. Lean's
$26/5$ is $6.2\%$ above $\kappa_H$ and $13/2$ is $8.4\%$ above $\sigma_H$,
so the product $33.8$ is $15.2\%$ above $\sigma_H\kappa_H=29.35$.
$\sigma_H$ is reached as the gap tends to $0$, $\kappa_H$ at the worst
position of the gap relative to the dyadic grid.

| Bias term | Needed for 11 | Paper's thresholds: method's best $C$ | Certificate room left |
|---|---|---:|---:|
| Lean's, $8\beta^2$ with $\beta=1$ | $\sigma\kappa\le28.25$ | 11.20 | none ($-3.7\%$) |
| Same form, $\beta=1/2$ | $\sigma\kappa\le29.75$ | 10.93 | $1.4\%$ |
| Bias bounded against $\omega_\mu(B^{-1/2})$ directly, constant $1/2$ | $\sigma\kappa\le30.19$ | 10.85 | $2.9\%$ |

The bias constants $1/2$ are the sharp values
([scan_finite.py](scan_finite.py)). The largest wrong-label probability of
the level-$L$ classifier divided by $\min(1,h/d)$ is $0.549$, $0.512$ and
$0.502$ at $N=2^6$, $2^{10}$ and $2^{14}$, for $h=N^{-1/2}$ and for
$h=B^{-1/2}$ alike, and for both threshold choices tested. The supremum
is at the smallest gaps, where the classifier is nearly a fair coin and a
tie counts as label $0$. A bias bound against $\omega_\mu(B^{-1/2})$
directly gives $C=\sqrt{\beta_B^2+4\sigma\kappa}$. It would need its own
proof; Lean does not have it.

**With exact one-coin quantities** ([limit12.py](limit12.py)), the same
route has $\sigma^*=\sup_d d\,\mathbb E V^2=2.240$, at $d\approx0.23$, and
$\kappa^*=\sup_d d\,c\ge3.601$. The latter is reached at the smallest gap
computed, and the values still rise slowly toward about $3.61$. A bound on
the product over every gap law can do no better than
$P^*=\sup\mathbb E V^2\cdot c/\mathbb E[1/D]^2=7.757$, reached by a point
mass. With $\beta=1/2$ these give $C\approx5.75$ in Lean's form and $5.59$
with the direct bias bound, against the actual $5.37$. The losses of Lean's
method are in the Hoeffding bounds, not in the route: the exact second
moment is $2.24$ against $\sigma_H=6.0$, and the exact cost $3.6$ against
$\kappa_H=4.9$. These limits do not cover the regime $Nd^2<1$; in Lean its
product is far smaller ($\tfrac{583}{50}$ in place of $\tfrac{169}{5}$).

## Retuning the estimator

**The level ratio $r$ is forced.** Levels with $2^ld^2\lesssim1$ change
their vote with probability of order one, and levels beyond change it rarely.
So $\mathbb E V^2$ grows like $r^{-l^*}=d^{-2\log_2(1/r)}$ with
$2^{l^*}=d^{-2}$, and the mean cost like $(2r)^{l^*}=d^{-2\log_2(2r)}$. The
two exponents add to $2$ for every $r\in(1/2,1)$, so a single gap cannot
tell them apart. A two-point law can: if one exponent exceeds $1$, a small
weight on a small gap makes that moment large while barely changing
$\mathbb E[1/D]$, and the ratio is unbounded. Both moments must therefore
grow like $1/d$, which needs $\log_2(1/r)=1/2$. This is a scaling argument,
not a proof.

**The thresholds are free, with $b>1/4$.** In the method's bounds, the
wrong-label probability of the cap-$M$ classifier falls like
$e^{-2a}(Md^2)^{-2b}$. It must fall faster than
$p_l\propto M^{-1/2}$ for the second moment to stay bounded, and at least
as fast as $\omega(M^{-1/2})\propto M^{-1/2}$ for the bias. With $b\le1/4$
the method's error sums diverge.

| $(a,b)$ | $\kappa_H$ | $\sigma_H$ | Method's $C$, Lean's bias | Room for 11 | Actual ratio, $N=2^{14}$ | Actual limit |
|---|---:|---:|---:|---:|---:|---:|
| $(1,1)$, paper | 4.895 | 5.996 | 11.20 | $-3.7\%$ | 5.07 | 5.365 |
| $(1.5,1)$ | 5.187 | 5.037 | 10.61 | $8.1\%$ | | 5.590 |
| $(2,1/2)$ | 4.885 | 5.056 | 10.33 | $14.4\%$ | 5.12 | 5.354 |
| $(2,3/4)$ | 5.182 | 4.722 | 10.29 | $15.5\%$ | | 5.574 |
| $(2.5,1/2)$ | 5.165 | 4.524 | 10.07 | $20.9\%$ | 5.36 | 5.576 |
| $(3,1/2)$ | 5.430 | 4.338 | 10.11 | $19.9\%$ | 5.51 | 5.762 |

"Room for 11" is how far the certificates' product may exceed
$\sigma_H\kappa_H$ with Lean's bias term; Lean's certificates now exceed it
by $15.2\%$. The full grid of 55 pairs, $0.5\le a\le5$ and
$1/2\le b\le2$, is in [params12.log](params12.log); its best method constant
is at $(2.5,1/2)$.

Larger thresholds make early stops rarer. That lowers the method's bound on
the second moment but costs flips: the exact second moment hardly changes
($d\,\mathbb E V^2$ moves by less than $4\cdot10^{-4}$ across the table),
while the exact cost rises. So
retuning helps the proof and mostly hurts the estimator. The pair $(2,1/2)$
is the exception found here: the method's constant drops to $10.33$ and the
actual limit is unchanged ($5.354$ against $5.365$), though the ratio at
$N=2^{14}$ rises from $5.07$ to $5.12$.

A proof for retuned thresholds would need a new Lean estimator. The frozen
batch machine of `BlindUpper` uses the classifier `threshold1`, which has
$a=b=1$, and every certificate from `UpperCost` to `UpperCallCost` is for
those thresholds.

## Conclusions

1. The family behind $12$ has actual worst ratio $5.07$ at $N=2^{14}$, rising
   toward about $5.37$. Point masses with every coin positive are the worst
   laws found.
2. With the paper's thresholds, Lean's method cannot give $11$ while the bias
   bound is $\omega_\mu(N^{-1/2})$. A sharp bias bound near $1/2$ makes $11$
   possible in principle, but only if the second-moment and cost
   certificates come within $1.4$ to $2.9\%$ of the exact Hoeffding sums.
3. Retuned thresholds such as $(2,1/2)$ give the method $10.33$ with Lean's
   bias bound, and leave about as much certificate room as the current proof
   uses. They need a new Lean realization of the estimator.
4. The calibration at $B/4$ costs a factor $2$ in the actual ratio as well
   as in the proof. Removing it would change the batch design.
5. Bounds on the exact one-coin quantities would bring the route to about
   $5.6$ to $5.75$, close to the actual $5.37$. The earlier study's
   recommendation of interval arithmetic for those quantities still applies.

## Reproduce

From this directory, with the repository's Python requirements:

```sh
python scan_scaled.py
python params12.py
python limit12.py
python scan_finite.py
```

All four are deterministic. The logs [scan_scaled.log](scan_scaled.log),
[params12.log](params12.log), [limit12.log](limit12.log) and
[scan_finite.log](scan_finite.log) are their output. Together they took about
an hour on four cores; `params12.py` and `limit12.py` use four processes.
The runs used Python 3.13, numpy 2.5.3 and scipy 1.18.1, not the versions
pinned in `requirements.txt`.
