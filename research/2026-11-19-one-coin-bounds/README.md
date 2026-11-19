# Which one-coin bounds would bring the upper constant to 8?

**Status: numerical evidence only.** Floating-point computations over finite
grids, with no proof and no Lean check. Nothing here changes a claimed
result.

The [previous study](../2026-11-19-upper-constant-12/README.md) found that
the estimator behind the Lean constant $12$ has actual worst ratio
$\text{RMS}/\omega_\mu(B^{-1/2})$ tending to about $5.37$. Lean's proof
method, evaluated with exact sums, cannot go below about $11.2$. With
exact one-coin quantities, the same proof route would give about $5.6$ to
$5.75$. This study scopes the gap between those numbers. It asks which
sharper bound would carry a proof with Lean's structure to $8$, and whether
that needs interval arithmetic on the exact one-coin quantities.

## Answer

- **The loss is in the tail estimate, not in the proof's structure.** The
  proof keeps every union bound but replaces Hoeffding's inequality by
  Bahadur's elementary tail bound for binomial counts. The method then gives
  a call second moment $\sigma\approx2.93$ and a call cost
  $\kappa\approx4.44$, in place of $6.0$ and $4.9$. The constant becomes
  about $7.75$ with Lean's bias bound, or $7.35$ with a sharp bias bound
  near $1/2$.
- **A median bound adds a little more.** It bounds the probabilities near
  the centre of the distribution, where one-sided tail bounds give only $1$.
  That lowers $\kappa$ to $3.89$ and the constant to $7.3$, or $6.9$.
- **Exact one-coin values are not needed.** Using exact values above a gap
  $d_0$ and the analytic bound below it changes the constant by at most
  $0.04$. The cost bound peaks at the smallest gaps, which only an analytic
  bound can reach, and the second-moment bound is nearly flat for gaps up
  to $0.3$.
- **The estimator stays the same.** All of this is for the paper's
  thresholds ($a=b=1$), so the frozen `BlindUpper` machine is reused. The
  retuned thresholds of the previous study would need a new estimator.

Room for each whole-number target: the factor by which the certificates of
a Lean proof may exceed the exact sums of the method.

| Target | Bahadur, Lean's bias | Bahadur, sharp bias | Bahadur and median, Lean's bias | Bahadur and median, sharp bias |
|---|---:|---:|---:|---:|
| 9 | $40\%$ | $52\%$ | $60\%$ | $73\%$ |
| 8 | $8\%$ | $19\%$ | $23\%$ | $36\%$ |
| 7 | none | none | none | $3\%$ |

Lean's current certificates exceed the exact Hoeffding sums by $15\%$
([previous study](../2026-11-19-upper-constant-12/README.md#where-the-proofs-12-goes)).
So $9$ is a safe target for Bahadur's bound alone. $8$ needs one of the two
additions, the median bound or a sharp bias bound, with certificates about
as tight as now. $7$ is out of reach for this proof structure.

## The proof's constant

As in the previous study, the proof of Theorem AB.1 gives
$$C=\sqrt{8\beta^2+4\sigma\kappa}.$$
Here $\beta$ is the bias constant (Lean: $1$), $\sigma$ bounds
$d\,\mathbb E V^2$ and $\kappa$ bounds $d$ times the mean padded call cost,
both over all gaps $d$ (Lean: $13/2$ and $26/5$). Lean bounds the cost by
summing, over the checks of the classifiers, a bound on the probability
that the classifier is still running there. It bounds the second moment
level by level, by the smaller of two quantities: the error union bound of
the two classifiers, or the vote-change probability $1/4$ plus their early
stops. Each of these events is a deviation of the success count of $n=2^k$
flips past a cut. Lean bounds each one by Hoeffding's inequality, through
the interface `HasMeanTails` of
[`Uniform713/Common.lean`](../../lean/ThresholdHC/Uniform713/Common.lean).

## The ladder

Every row keeps that structure and changes only the bound for each event.
All rows use the paper's thresholds and the positive sign, which is the
worse sign under the tie rule.

| Bound for each event | $\sigma$ | $\kappa$ | $\sigma\kappa$ | $C$, Lean's bias | $C$, bias $1/2$ |
|---|---:|---:|---:|---:|---:|
| Lean's certificates | 6.500 | 5.200 | 33.80 | 11.97 | 11.71 |
| Hoeffding, exact sums | 5.977 | 4.895 | 29.26 | 11.18 | 10.91 |
| Bahadur or Hoeffding, at the lattice cut | 2.930 | 4.438 | 13.00 | 7.75 | 7.35 |
| The same, and the median bound | 2.930 | 3.892 | 11.40 | 7.32 | 6.90 |
| Gaussian probabilities, large-$n$ limit | 2.770 | 3.616 | 10.02 | 6.93 | 6.49 |
| Exact one-coin quantities, no union bounds | 2.240 | 3.601 | 8.07 | 6.35 | 5.85 |

The actual worst ratio of the estimator tends to about $5.37$. The rows:

- **Hoeffding, exact sums.** This is the method's limit computed in the
  previous study. Here [tails.py](tails.py) evaluates it in the large-$n$
  limit.
- **Bahadur or Hoeffding** ([rigorous.py](rigorous.py)). Each event is the
  exact lattice event at its check: integer success counts, with the
  classifier's strict comparisons. Its probability is bounded by the smaller
  of Hoeffding's bound and Bahadur's bound, $\Pr(X\ge k)\le\Pr(X=k)/(1-\rho)$
  with $\rho=(n-k)p/((k+1)q)<1$. Bahadur's bound is the geometric series of
  the ratios of consecutive binomial terms. Values are computed at 49 gaps
  from $0.002$ to $0.5$. $\kappa$ peaks at the smallest gap computed. Its
  large-$n$ form, the Mills-ratio bound $\varphi(w)/w$, gives $4.467$, so
  the limit lies between $4.44$ and $4.47$. With $4.467$ the constants are
  $7.78$ and $7.38$, and the room for $8$ is $7\%$ and $18\%$.
- **The median bound.** A binomial median lies between $\lfloor np\rfloor$
  and $\lceil np\rceil$ (Kaas and Buhrman, 1980). So
  $\Pr(X\le m)\le\tfrac12+(m-\lfloor np\rfloor+1)P_{\max}$ for
  $m\ge\lfloor np\rfloor$, where $P_{\max}$ is the largest binomial term,
  and symmetrically for upper tails. This bounds the survival probabilities
  near the threshold by about $1/2$ in place of $1$. It lowers only
  $\kappa$.
- **Gaussian probabilities.** The large-$n$ limit of each event's own
  probability, with the union bounds kept. It is not a bound for every $n$.
- **Exact one-coin quantities.** Taken from
  [limit12.json](../2026-11-19-upper-constant-12/limit12.json) of the
  previous study.

**Check.** With Bahadur's bound switched off, [rigorous.py](rigorous.py)
must reproduce the Hoeffding limits of [tails.py](tails.py) as the gap
shrinks. It gives $\kappa=4.828$, $4.882$ and $4.892$ at $d=0.05$, $0.01$
and $0.002$, against the limit $4.895$. $\sigma$ approaches $5.98$ from
below ($5.66$ and $5.78$ at $d=0.01$ and $0.002$), because the lattice cuts
are slightly stricter than the continuous ones.

## Where Hoeffding loses

The table splits the second-moment bound by the levels' $x=2^ld^2$, at
$d=0.01$. It is $(2+\sqrt2)\sum_l\sqrt{x_l}\,w_l$, with $w_l$ the bound for
the probability that the votes of levels $l$ and $l-1$ differ.

| Bound | $x<\tfrac14$ | $[\tfrac14,1)$ | $[1,4)$ | $[4,16)$ | Total |
|---|---:|---:|---:|---:|---:|
| Hoeffding, limit form | 1.902 | 2.672 | 1.264 | 0.013 | 5.851 |
| Bahadur or Hoeffding | 1.404 | 1.189 | 0.255 | 0.001 | 2.848 |
| Gaussian probabilities | 1.405 | 1.033 | 0.210 | 0.001 | 2.650 |
| Exact | 1.179 | 0.620 | 0.185 | 0.001 | 1.985 |

Most of Hoeffding's excess lies at $\tfrac14\le x<4$. There the bound is
the error union bound of the two classifiers at their caps, and Hoeffding's
$e^{-2x}+e^{-x}$ misses the factor $1/(w\sqrt{2\pi})$ of the Gaussian tail.
At $x=1$, Hoeffding gives $e^{-1}=0.37$ for the smaller classifier, against
a Gaussian probability of $0.08$. Bahadur's bound recovers almost all of
it. What remains against the exact values is the structure:
- below $x=\tfrac14$, the vote-change bound $\tfrac14$ plus early stops;
- from $\tfrac14$ to $1$, the union of the two error events in place of the
  probability that the votes differ.

At $d=0.2$ the picture is the same ([scope.log](scope.log)).

## Hybrids with exact values

| Gap $d_0$ | $0.01$ | $0.02$ | $0.05$ | $0.1$ | $0.2$ |
|---|---:|---:|---:|---:|---:|
| $C$, Bahadur below $d_0$, exact above, Lean's bias | 7.71 | 7.71 | 7.71 | 7.72 | 7.75 |
| The same with the median bound | 7.29 | 7.29 | 7.29 | 7.30 | 7.32 |

Exact one-coin values for every gap at least $d_0$ would need interval
arithmetic on dynamic programs over up to about $2^{l}$ success counts per
level, with $2^l\approx8/d_0^2$. They would gain at most $0.04$. The
bounds' suprema sit at small gaps:
- $\kappa$ rises toward its limit as $d\to0$;
- the Bahadur bound for $\sigma$ stays between $2.82$ and $2.93$ for every
  gap up to $0.3$, and falls only above that.

Below $d_0$ only an analytic bound can reach, because there are infinitely
many gaps. Exact values would pay off only with an analytic treatment of
the small-gap limit itself, a periodic function of $\log_2d^2$, and that
is a different project.

## What a Lean proof would need

1. **A sharper tail interface.** The cost and second-moment proofs use
   `HasMeanTails`, which provides only Hoeffding's bound for each cut.
   Bahadur's bound needs the binomial law of the success counts. So the
   interface would carry bounds at the lattice cuts, and the coin flips of
   the `BlindUpper` realization would have to be shown to satisfy it.
2. **Bahadur's bound.** It is elementary: the ratio of consecutive binomial
   terms, then a geometric series.
3. **The binomial term, uniformly in $n$.** Mathlib's Stirling lemmas
   (`Stirling.le_factorial_stirling`, `Stirling.sqrt_pi_le_stirlingSeq`, and
   Robbins' step bound `Stirling.log_stirlingSeq_sdiff_le`) give
   $\binom nk\le e^{1/(12n)}\sqrt{n/(2\pi k(n-k))}\,n^n/(k^k(n-k)^{n-k})$
   for $0<k<n$. With $\mathrm{KL}(k/n\,\|\,p)\ge2(k/n-p)^2$, this turns
   Bahadur's bound into Hoeffding's exponential times an explicit factor of
   Mills-ratio size. The small-gap regime then needs these factors bounded
   uniformly. Small $n$ can be checked case by case.
4. **New certificates.** Every grid certificate for the cost (the
   counterparts of `UpperWork`, `UpperCost` and `UpperCallCost`) and for the
   second moment (`UpperDisagreement`, `UpperSign` and `UpperQuarter`) would
   be redone, with Mills-type terms in place of the exponentials.
   `UpperScale` would be reused, with new constants in
   `call_variance_cost_le`.
5. **For 8, one of:**
   - the binomial median theorem, which is not in Mathlib;
   - a bias bound near $1/2$. It needs its own argument, that the
     classifier errs with probability at most about $1/2$ at every gap.
     Ties raise the sharp value at small budgets: $0.549$ at $N=2^6$ and
     $0.502$ at $N=2^{14}$ ([previous study](../2026-11-19-upper-constant-12/README.md#where-the-proofs-12-goes)).

## Conclusions

1. A proof that keeps Lean's structure can reach about $7.3$ to $7.8$ for
   the same estimator, if Bahadur's tail bound replaces Hoeffding's. With
   that bound alone, $9$ is safe. $8$ needs either the median bound or a
   sharp bias bound, with certificates about as tight as the current ones.
2. Interval arithmetic on exact one-coin quantities is not worth it for this
   structure: it gains at most $0.04$.
3. Below about $7$, the losses are in the union bounds of the second-moment
   proof ($2.93$ against the exact $2.24$), not in the tails.

## Reproduce

From this directory, with the repository's Python requirements:

```sh
python scope.py
```

It takes about 15 seconds on four cores and writes [scope.json](scope.json);
[scope.log](scope.log) is its output. It reads the exact one-coin values
from the previous study's
[limit12.json](../2026-11-19-upper-constant-12/limit12.json).
[blind12.py](blind12.py) is an unchanged copy of that study's module. The run
used Python 3.13, numpy 2.5.3 and scipy 1.18.1, not the versions pinned in
`requirements.txt`.
