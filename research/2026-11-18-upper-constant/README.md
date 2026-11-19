# How loose is the upper constant 512?

**Status: numerical evidence only.** Floating-point computations over finite
grids, with no proof and no Lean check. Nothing here changes a claimed
result.

*Since this study,* Lean checks the constant $119$ for the same estimator
([`UpperConstant`](../../lean/ThresholdHC/UpperConstant/Full.lean),
[record](../../results/upper-constant-20261118/README.md)). It keeps the
library's sharper level sums, $23$ and $527/7$, in place of $85$ and $149$,
and compares the budget by $17/6$ in place of $4$. A second stage checks
$45$ ([`UpperWork`](../../lean/ThresholdHC/UpperWork/Full.lean),
[record](../../results/upper-work-20261118/README.md)). It replaces the
expected-flips bound of $17$ times the work envelope by
$\tfrac{49}{10}\,d^{-2}(1+\log(Nd^2))$, which brings the cost constant
$\kappa$ from $527/7$ to $248/25$. A third stage checks $36$
([`UpperMoment`](../../lean/ThresholdHC/UpperMoment/Full.lean),
[record](../../results/upper-moment-20261118/README.md)). It keeps the
disagreement factor $\tfrac{25}{3}e^{-2}\le\tfrac{113}{100}$ in place of $3$,
which brings $\sigma$ from $23$ to $72/5$. The per-level bounds themselves,
discussed below, are otherwise those of the original proof. A fourth stage
checks $27$ ([`UpperMixture`](../../lean/ThresholdHC/UpperMixture/Full.lean),
[record](../../results/upper-mixture-20261118/README.md)) for a variant that
runs level $L+1$ with probability $B/(4\cdot2^L)-1$ and level $L$ otherwise,
so that it uses the whole budget. This study does not compute that variant;
its ratios are for the single-level estimator. A fifth stage checks $19$ for
the same variant ([`UpperCost`](../../lean/ThresholdHC/UpperCost/Full.lean),
[record](../../results/upper-cost-20261118/README.md)). It sums the survival
bounds of the early-stopping classifiers by the difference of level and
check, which brings the padded call cost from $273/25$ to $11/2$. A sixth stage
checks $17$ for the same variant
([`UpperDisagreement`](../../lean/ThresholdHC/UpperDisagreement/Full.lean),
[record](../../results/upper-disagreement-20261119/README.md)). It bounds the
disagreement of consecutive classifiers by their error union bounds, which
brings the call second moment from $72/5$ to $57/5$. A seventh stage checks
$15$ ([`UpperSign`](../../lean/ThresholdHC/UpperSign/Full.lean),
[record](../../results/upper-sign-20261119/README.md)). Below the cap scale it
bounds that disagreement by the sign-change probability of the majority votes,
at most one half, plus an early-stop term, which brings the call second moment
to $89/10$.

The RMS law states
$\tfrac16\,\omega_\mu(B^{-1/2})\le R_\mu(B)\le512\,\omega_\mu(B^{-1/2})$
for every gap law and every $B\ge1$. Lean checks both constants, and $1/6$
is the best possible. This study asks how much of the factor $3072$
between them is slack in the upper constant, and where that slack comes
from.

## Summary

| Quantity | Value |
|---|---:|
| Proven constant, `minimax_upper_bound` in [BlindUpper/Full.lean](../../lean/ThresholdHC/BlindUpper/Full.lean) | 512 |
| Same algorithm, raw output, worst point mass, budgets $4\le B<2^{17}$ (exact formula) | 7.17 |
| Same algorithm, raw output, limit as $B\to\infty$ (worst gap $d\approx0.12$) | 7.57 |
| Same algorithm, output clipped to $[0,1]$, worst simulated case at $N=2^8$ and $N=2^{10}$ | about 3.8 and 4.9 |
| Constant reachable along the paper's own proof route, with sharp per-gap constants ($N=2^{14}$) | 8.7, rising to about 9.3 |
| Any algorithm that may use $\mu$, point masses only (proof below) | at most 1/2 |
| Sharp lower constant | 1/6 |

The proven $512$ is about 68 times the risk the algorithm actually has on
the hardest laws found here. Almost all of the loss is in two per-call
constants of the paper's analysis. A proof with sharp versions of those
constants, along the same route, would give a constant near 9.

## The algorithm and its exact risk

The upper bound uses one algorithm that knows only the budget. Lean checks
it as `budgetEstimator`, and the toolkit runs it as
[`estimate_fraction`](../../toolkit/threshold_toolkit/estimator.py). For
$B\ge4$ it takes the largest $N=2^L$ with $4N\le B$. Each call draws a
fresh coin and a random level $J$ with $\Pr(J=l)=p_l=(1-r)r^l$,
$r=2^{-1/2}$. It then runs two early-stopping majority classifiers on
the same flips, with caps $2^l$ and $2^{l-1}$, and returns
$V=(Z_l-Z_{l-1})/p_l$; a level above $L$ costs one flip and returns $0$.
Two pilot streams, each marking a call with probability cost$/N$, fix
how many fresh production calls to average. The classifiers are the ones in
the Lean construction: the cap-$2^l$ classifier looks at the success
fraction after $1,2,4,\dots$ flips and stops at the first prefix $n$ where
it differs from $1/2$ by more than $\sqrt{(1+\log(2^l/n))/n}$, or at $n=2^l$,
and reports $1$ only if the fraction exceeds $1/2$ (`threshold1`,
`firstStop` and `firstDecision` in the Lean sources).

The paper's calibration lemma (v6 §5) makes the risk of the raw output
exact:

$$\text{MSE}=(\mathbb E Z_L-\theta)^2+\bigl(\mathbb E V^2-(\mathbb E Z_L)^2\bigr)\,\frac cN,$$

$$\mathbb E V^2=\sum_{l\le L}\frac{\Pr(Z_l\ne Z_{l-1})}{p_l},\qquad
c=\sum_{l\le L}p_l\,\mathbb E[\text{flips at level }l]+r^{L+1},$$

where $\theta$ is the fraction of positive coins. Every term is an average
over the gap law and the sign law of one-coin quantities. Those depend only
on the coin's success probability and the level, not on $N$. They are
computed exactly, up to floating-point rounding, by a dynamic program over
the number of successes at the prefix lengths $1,2,4,\dots$ at which both
classifiers look ([blind.py](blind.py)).

**Validation.** [crosscheck.py](crosscheck.py) compares the formula with
40,000 simulated runs of the toolkit implementation at five settings. The
raw RMS agrees within the simulation's sampling error (for example
$0.7690$ exact against $0.7743$ simulated at $N=2^6$, $d=0.3$, all
positive), and the mean number of flips is $4N-c$, as the lemma says.

## Results

The ratio is RMS error divided by $\omega_\mu(B^{-1/2})$. For a fixed $N$,
the worst budget is $B\to8N$, so the tables report both
RMS$/\omega_\mu(N^{-1/2})$ and RMS$/\omega_\mu((8N)^{-1/2})$.

**Point masses** ([scan_point.py](scan_point.py), [scan_point.json](scan_point.json)).
The scan covers 70 gaps per budget level and 41 sign probabilities. The
worst case puts every coin on the positive side, at a moderately easy gap
$d\approx0.2$ to $0.3$.

| $N$ | $2^0$ | $2^2$ | $2^4$ | $2^6$ | $2^8$ | $2^{10}$ | $2^{12}$ | $2^{14}$ |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| RMS$/\omega(N^{-1/2})$ | 1.55 | 1.47 | 1.54 | 1.85 | 2.12 | 2.32 | 2.45 | 2.53 |
| RMS$/\omega((8N)^{-1/2})$ | 2.20 | 2.87 | 4.10 | 5.25 | 6.00 | 6.55 | 6.92 | 7.17 |

**The limit $N\to\infty$** ([limit.py](limit.py), [limit.json](limit.json)).
For a fixed gap $d$ and large $N$, the ratio to $\omega(N^{-1/2})$ tends to
$G(d)=d\sqrt{\operatorname{Var}V\cdot c}$, with level sums taken to $26$.
$G$ peaks at $2.677$ near $d=0.12$ and stays above $2.65$ for
$0.04\le d\le0.2$. With the budget rounding the limit is
$\sqrt8\cdot2.677\approx7.57$. Every finite-$N$ value computed lies below
it.

**Two-point laws** ([scan_two.py](scan_two.py), [scan_two.json](scan_two.json)).
The scan covers pairs of 23 gaps, 20 weights and 25 sign patterns at
$N=2^4,\dots,2^{12}$. At $N=2^4$ the worst two-point law exceeds the worst
point mass on the same coarse grid by $0.5\%$ ($4.023$ against $4.002$),
and stays below the finer point-mass scan ($4.10$). From $N=2^6$ on, the two
agree to three decimals.

**Clipping** ([clipped.py](clipped.py), [clipped.json](clipped.json)).
Clipping the output to $[0,1]$ can only help, and the Lean theorem does
not use it. Simulation over 7 gaps and 3 sign fractions gives a worst
clipped RMS$/\omega((8N)^{-1/2})$ of about $3.76$ at $N=2^8$ (12,000 runs
per setting) and $4.95$ at $N=2^{10}$ (4,000 runs). Clipping helps less as
$N$ grows. For a fixed gap and a sign fraction strictly between $0$ and
$1$, the output's spread shrinks with $N$, so it rarely leaves $[0,1]$.
The raw ratio for such sign fractions approaches nearly the same limit:
the exact formula gives $7.16$ at $d=0.12$, sign fraction $0.8$ and
$N=2^{18}$, against $7.42$ with all signs positive. Clipping therefore
lowers the constant mainly at small budgets.

## Where the factor 512 goes

The proof bounds the mean cost and the variance of one call separately:
$c\le149\,A_\mu(h)$ and $\operatorname{Var}V\le85\,A_\mu(h)$, with
$A_\mu(h)=\mathbb E_\mu\min\{h^{-1},D^{-1}\}$ and $h=N^{-1/2}$. Their
product gives $\text{MSE}\le(1+85\cdot149)\,\omega(h)^2=12666\,\omega(h)^2$,
or $12751$ with Lean's padding. [route.py](route.py) computes the best
constants this route allows, as suprema over the gap of the one-coin
ratios: bias $\le\beta\,\omega$, $\mathbb E V^2\le\sigma A$,
$c\le\kappa A$.

| | $\beta$ | $\sigma$ | $\kappa$ | $\sqrt{\beta^2+\sigma\kappa}$ | times $\sqrt8$ |
|---|---:|---:|---:|---:|---:|
| Paper and Lean | 1 | 85 | 149 | 112.5 | 318 (Lean: $4\cdot128=512$) |
| Sharp, $N=2^{10}$ | 0.51 | 2.83 | 2.84 | 2.88 | 8.15 |
| Sharp, $N=2^{14}$ | 0.50 | 2.89 | 3.18 | 3.07 | 8.69 |

$\kappa$ is still rising at $N=2^{14}$. The limit table gives
$c\cdot d\approx3.53$ at $d=0.04$, so the route's constant tends to
about $\sqrt8\cdot\sqrt{0.25+2.9\cdot3.6}\approx9.3$. In factors, from
$512$ down to the true $7.6$:

- **34:** sharp per-gap constants in place of $85$ and $149$.
- **1.13:** rounding $\sqrt{12751}=112.9$ up to $128$.
- **1.41:** comparing moduli with the factor $4$ where $\sqrt8$ suffices,
  because $\omega_\mu(ch)\le c\,\omega_\mu(h)$ for $c\ge1$.
- **1.2:** bounding a product of two averages over the gap law by a
  product of suprema. Point masses are the worst case found, so the
  route loses little here.

Two further factors are changes to the algorithm or the statement, not to
its analysis:

- **Clipping** the output to $[0,1]$ gains a factor of $1.3$ to $1.6$ at
  the budgets simulated, but little for large budgets (see above).
- **$\sqrt2$:** the expected cost $4N-c$ uses at most half of a budget
  just below $8N$. Setting the marking cap to $B/4$ in place of $N$ would
  spend the whole budget.

## With the law known: point masses

For $\mu=\delta_d$ the minimax constant is at most $1/2$. If
$d\sqrt B\ge1$, flip $B$ fresh coins once each. With $\bar Y$ the mean of
the $\pm1$ flips, $\hat\theta=\tfrac12+\bar Y/(4d)$ is unbiased with
variance at most $1/(16d^2B)$, so its RMS error is at most
$\tfrac14\cdot\frac1{d\sqrt B}=\tfrac14\,\omega_{\delta_d}(B^{-1/2})$.
If $d\sqrt B<1$, then $\omega_{\delta_d}(B^{-1/2})=1$, and the constant
estimate $1/2$ has RMS error at most $1/2$. The universal constant for
general laws with $\mu$ known is not addressed here.

## Recommendation

1. **A sharper proof for the same algorithm.** Bound the one-coin
   functions behind $\beta$, $\sigma$ and $\kappa$ directly. Each is a
   function of one gap and one level. Use interval arithmetic on a finite
   range of gaps and levels, and analytic tails outside it. The existing
   Lean realization of the algorithm (`BlindUpper`) would stay. What would
   change are the one-coin bounds in `CutoffBounds.lean` (the constants 85
   and 149), the bias bound in `CutoffBiasWork.lean`, and the arithmetic
   that combines them in `PopulationBounds.lean`, `CutoffBatch.lean` and
   `Full.lean`. The target is a constant near $10$ in place
   of $512$, about 50 times smaller.
2. **Then the algorithm.** Spending the whole budget would gain $\sqrt2$,
   bringing the limit from about $7.57$ to about $5.35$. Clipping helps mainly
   at small budgets. Further gains would have to come from the algorithm's
   design: the level law $r$, the classifier thresholds and the pilot
   scheme. These change the algorithm and need a new Lean realization.

## Reproduce

From this directory, with the repository's Python requirements:

```sh
python scan_point.py
python limit.py
python route.py
python scan_two.py
python crosscheck.py
python clipped.py
```

The first four are deterministic and take a few minutes in total;
[run-deterministic.log](run-deterministic.log) is their output. The last
two simulate with fixed seeds and take longer. The runs recorded here used
Python 3.13, numpy 2.5.3 and scipy 1.18.1, not the versions pinned in
`requirements.txt`. Simulated figures can differ in the last digits on
other versions.
