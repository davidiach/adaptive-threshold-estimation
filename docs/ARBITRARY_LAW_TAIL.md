# Oracle-scale tail certificates for an arbitrary unknown gap law

This is a **paper proof with an executable implementation**, not a new Lean
audit. It closes one part of arbitrary-law adaptation: learning an upper bound
on unobserved small-gap mass at the oracle scale, with a physical flip cap.
It does **not** yet construct an oracle-rate confidence sequence for the
positive fraction. In particular, it does not supply the core costs and null
likelihood integrals needed by the known-law estimator.

Let the persistent magnitude of a fresh coin have any probability law $\mu$ on
$(0,1/2]$. Its sign may depend arbitrarily on its magnitude. Fresh coins are
independent, and flips are independent conditional on each coin's parameters.
Only the flips are observed. Write $F(t)=\mu((0,t])$.

## Statement

For an integer $J\ge1$, put $N=4^J$ and $t=2^{-J}$. The procedure below uses at
most $mN$ physical flips, where $m$ is any odd integer at least
$8\log(2/\delta)$, and returns $U\in[0,1]$. It requires neither a candidate
family nor any integral of $\mu$.

Define the bounded work envelope
$$
 w_J(d)=\min\{N,\,1024d^{-2}(1+\log_2^+(d/t))\},\qquad
 W_J=\int w_J(d)\,\mu(dd),
$$
where $\log_2^+x=\max\{0,\log_2 x\}$. Let $u_J$ be the probability that the
single-coin test below is unresolved. At this fixed scale, with probability at
least $1-\delta$,
$$
 F(t)\le U\le\min\{1,128\max(u_J,W_J/N)\}.                 \tag{1}
$$
Moreover,
$$
 \tfrac12 F(t)\le u_J
 \le\int\min\{1,16(t/d)^2\}\,\mu(dd).                    \tag{2}
$$
All of these are nonasymptotic statements for arbitrary probability laws.
The quantities on the right describe performance; the algorithm does not
receive or evaluate them.

For every fixed $\mu$ and $0<\rho\le1/4$ there is a finite onset $J_0(\mu,\rho)$
such that, for every $J\ge J_0$, (1) implies
$$
 F(2^{-J})\le U\le 524288\,K_{\mu,\rho}(4^J).             \tag{3}
$$
The constant is universal, while the onset depends on the law and rarity.
The algorithm does not need to know either $\rho$ or that onset. Its budget is
$m4^J$, so the confidence amplification costs the usual logarithmic factor.
This is an oracle comparison for a **tail-mass upper certificate**, not for
estimation of the sign probability.

## A sign-neutral test with a gap-dependent cost

On one coin, inspect the empirical mean after $n_k=4^k$ flips, $k=0,\ldots,J$.
Let
$$
 h_k=\left\lceil\sqrt{2n_k(J-k+2)}\right\rceil,
 \qquad r_k=h_k/n_k.
$$
Stop and call the coin resolved if $|\bar X_{n_k}-1/2|>r_k$.
Otherwise continue; if the last check fails, call it unresolved. Let $T$ be
its work and $Y$ its unresolved indicator. The strict inequality includes
ties in the unresolved/continuation case. Complementing every flip preserves
the entire stopping path and $Y$, so their conditional laws depend only on
$d$, even with a gap-dependent sign allocation. Always $1\le T\le N$.

If $d\le t$, then $r_k\ge2/\sqrt{n_k}\ge2t\ge2d$.
Resolving at check $k$ requires an empirical deviation from the true mean
larger than $r_k/2$. Two-sided Hoeffding and a union bound give
$$
 \Pr_d(Y=0)\le\sum_{k=0}^J2e^{-n_kr_k^2/2}
 \le\sum_{s=0}^{\infty}2e^{-(s+2)}
 =\frac{2}{e(e-1)}<\frac12.
$$
For example, $e>8/3$ verifies the last strict inequality. No independence
between checks on the same coin is used.

At the terminal check, $h_J=2\sqrt N$ exactly, hence $r_J=2t$.
If $d\ge4t$, being unresolved implies an empirical error of magnitude at least
$d/2$. Since $\operatorname{Var}(\bar X_N)\le1/(4N)$, Chebyshev bounds its
probability by $1/(Nd^2)$. For $d<4t$ use the bound one. These observations
prove (2), including the more convenient upper envelope $\min\{1,16(t/d)^2\}$.

Hoeffding's inequality sharpens the terminal bound. For $d\ge4t$ the same
event is a deviation of $\bar X_N$ from its mean by at least $d/2$, and
$Nt^2=1$, so
$$
 \Pr_d(Y=1)\le2e^{-Nd^2/2}=2e^{-d^2/(2t^2)}\qquad(d\ge4t).   \tag{2a}
$$
Statements (1)–(3) need only the Chebyshev envelope. The
[oracle-adaptation proof](ARBITRARY_LAW_ADAPTATION.md) uses (2a).

For completeness, the cost bound is
$$
 \mathbb E_d T\le w_J(d).                                \tag{4}
$$
Indeed, $r_k\le3\sqrt{(J-k+2)/n_k}$. Suppose there is a first $k_0\le J$ with
$n_{k_0}d^2\ge36(J-k_0+2)$. It is positive since $d\le1/2$. For every
$k\ge k_0$, $r_k\le d/2$, so
$\Pr_d(T>n_k)\le2e^{-n_kd^2/2}$. Summing the work increments and using
$e^{-x}\le2/x^2$ for $x>0$ gives
$$
 \mathbb E_d T
 \le n_{k_0}+6\sum_{k=k_0}^{J-1}n_ke^{-n_kd^2/2}
 \le n_{k_0}+\frac{64}{n_{k_0}d^4}
 \le2n_{k_0}.
$$
The last inequality follows from $n_{k_0}d^2\ge72$. By minimality,
$n_{k_0}d^2<144(J-k_0+3)$. Also $2^{k_0}d\ge1$, so
$J-k_0\le\log_2(d/t)$. Thus
$$
 \mathbb E_d T<288d^{-2}(3+\log_2(d/t))
 \le864d^{-2}(1+\log_2^+(d/t)).
$$
If no such check exists, $Nd^2<72$ and the trivial bound $T\le N$ is at
most $72d^{-2}$. Combining either case with $T\le N$ proves (4), with slack
in the coefficient 1024. Integration gives $\mathbb ET\le W_J$ without a
moment assumption on $\mu$.

## Inverse sampling under a physical budget

Test fresh coins until the first unresolved coin, or until the available
physical flip budget is exhausted. Pause in the middle of a coin if necessary;
do not count it as completed. If $n$ coins are completed, return
$V=\min\{1,8/n\}$, with $V=1$ when $n=0$. Completing the first unresolved
coin increments $n$ and ends this probe.

For a fixed $J$, this single probe covers $F(t)$ **simultaneously at every
cumulative budget**, with probability at least $7/8$. To see this, let
$u=\Pr(Y=1)$. If $F(t)>V$, then $n>8/F(t)\ge4/u$. Reaching such an $n$
before stopping requires the first $\lfloor4/u\rfloor$ coins to be resolved.
By independence of fresh coins, the probability is at most
$$
 (1-u)^{\lfloor4/u\rfloor}\le e^{-4+u}\le e^{-3}<1/8.
$$
When $u=0$, (2) gives $F(t)=0$ and failure is impossible. This argument
also protects budgets chosen from the observed path; it does not treat
the random number of completed coins as a fixed sample size.

There is a separate performance bound at every **deterministic** budget $b>0$:
$$
 \Pr\{V\le\min(1,128\max(u,W_J/b))\}\ge3/4.             \tag{5}
$$
Set $A=\max(u,W_J/b)>0$. If $A\ge1/16$ the claim is automatic. Otherwise put
$q=\lfloor1/(8A)\rfloor\ge1/(16A)$. Consider $q$ independent full
single-coin tests on a hypothetical stream, including coins the actual
probe might never reach. The chance that any is unresolved is at most
$qu\le1/8$. Markov's inequality bounds the chance their combined work exceeds
$b$ by $qW_J/b\le1/8$. Outside their union the actual probe completes at least
$q$ coins by budget $b$, hence $V\le8/q\le128A$. The two failure events
need not be independent. In particular, the budget is charged for all partial
and completed tests, rather than for completed coins alone.

Run $m$ independent probes, each capped at $b=N$, and take their median.
For validity a block fails with probability at most $1/8$; for the performance
bound it fails with probability at most $1/4$. Hoeffding applied across the
independent blocks bounds each median failure by $e^{-m/8}$. Their union is
at most $2e^{-m/8}\le\delta$, proving (1). The work cap is pathwise, including
all failure paths. Width and validity are proved jointly by a union bound;
they are not assumed independent.

## Comparison with the rare-event oracle

Use the original $K_{\mu,\rho}$, including its cap at $\rho$ and infimum over
all fractional submeasures. Let $\nu$ be the lowest-gap quantile submeasure
of mass $\rho$, splitting a boundary atom when necessary, and put $\sigma=\mu-\nu$.
Since $\mu$ has no mass at zero and $\rho>0$, there is $a\in(0,1/2]$ such that
$\sigma$ is supported on $[a,1/2]$. The existing
[quantile-tail floor](../lean/ThresholdHC/QuantileSelection/Specification.lean)
and its [proof](../lean/ThresholdHC/QuantileSelection/Full.lean) give
$$
 \tau_\nu(t):=\int\min(1,t/d)\,\nu(dd)\le K_{\mu,\rho}(N). \tag{6}
$$
These facts concern the full arbitrary-law quantile, not a finite-support
approximation or an assumption that a supplied family contains $\mu$.

For $x\ge1$, $1+\log_2x\le2x$, since $\log x\le x-1$ and $\log2\ge1/2$.
Consequently
$$
 \frac{w_J(d)}N\le2048\min(1,t/d),\qquad
 \min(1,16(t/d)^2)\le4\min(1,t/d).
$$
Their integrals over $\nu$ are at most $2052\tau_\nu(t)$. On the remaining
core $d\ge a$, their sum integrates to at most
$$
 [1024(J+1)+16]t^2/a^2\le2048(J+1)t^2/a^2.
$$
Choose $J_0$ so that, for all $J\ge J_0$,
$$
 2048(J+1)2^{-J}/a^2\le\sqrt\rho.                       \tag{7}
$$
Such an onset is finite. This condition also implies $t\le\sqrt\rho/2$.
The [elementary objective floor](../lean/ThresholdHC/EntropyTail/Objective.lean),
followed by the infimum and cap, gives $K_{\mu,\rho}(N)\ge2\sqrt\rho\,t$
at those scales. Combining the core and tail estimates with (2), (4) and (6),
$$
 u_J+W_J/N\le(2052+1/2)K_{\mu,\rho}(N)
 \le4096K_{\mu,\rho}(N).
$$
Equation (1) now proves (3). The logarithmic penalty in an individual
coin's work is absorbed by the ordinary tail kernel. On the fixed core its
cost is negligible after (7). No inverse-gap moment or rate of tail decay
is assumed.

For simultaneous statements over all $J\ge1$, call the procedure on fresh
streams with $\delta_J=\delta/[J(J+1)]$. Summability gives, on one event of
probability at least $1-\delta$, valid certificates at every scale and the
oracle comparison at every scale past $J_0$. This costs
$O(4^J[\log(1/\delta)+\log(J+1)])$ flips through scale $J$. These are
certificates for different tail thresholds; they are not nested intervals
for the positive fraction.

## Executable interface and verification boundary

The [implementation](../toolkit/threshold_toolkit/tail_mass.py) uses integer
thresholds, exact rational upper endpoints, persistent callbacks and a
cumulative budget for each probe. `run_tail_mass` checks the full requested
cap before acquiring any coin. It uses the odd integer
$m=8\lceil\log_2(2/\delta)\rceil+1$, which satisfies the proof's calibration.

```python
from threshold_toolkit.tail_mass import plan_tail_mass, run_tail_mass

plan = plan_tail_mass(7, delta="1/20")
# coin_factory(rng) returns the flip callback of a fresh persistent coin.
result = run_tail_mass(plan, coin_factory, budget=plan.flip_cap, seed=17)
print(result.scale, result.upper, result.flips)
```

`TailMassProbe` exposes the resumable single-block primitive. Repeated budgets
perform no work, decreasing budgets are rejected, and callback exceptions or
invalid bits invalidate that probe. Independence and the sampling model are
caller obligations, as for the other toolkit estimators. Python and its PRNG
are not Lean-verified. The [tests](../toolkit/tests/test_tail_mass.py) check
physical accounting, pauses, reflection, exact finite sampling calculations
and error paths; they do not replace the general-law paper proof above.

The new [arbitrary-law adaptation paper proof](ARBITRARY_LAW_ADAPTATION.md)
uses these certificates to learn a conservative finite law, transfers
the classifier bank to that law, and proves the full eventual oracle
width bound for the positive fraction. That additional construction,
like this tail theorem, still requires Lean formalization.
