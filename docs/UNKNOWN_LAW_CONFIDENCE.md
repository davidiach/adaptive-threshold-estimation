# Confidence intervals from flips when the gap law is unknown

Fresh items have iid pairs $(D,S)$, with $0<D\le1/2$ and $S\in\{-,+\}$.
Flips on an item are conditionally iid with success probability $1/2\pm D$
according to its sign. Let $\theta=P(S=+)$. The sign may depend on the gap.
The caller can supply a known upper bound $u\ge\theta$ or take $u=1$.

**Theorem.** There is an observable interval $J(B)\subseteq[0,u]$ using at
most the authorized integer budget $B$ such that, for every such population,
with probability at least $1-\delta$ it contains $\theta$ simultaneously at
all budgets and its width tends to zero. The procedure uses neither the gap
distribution nor an upper bound on its small-gap tail. The rate proved below
depends on that tail and can be slower than the known-law minimax rate.

## One stage

For a positive stage cap $c$, take $n=\lfloor\sqrt c\rfloor$ fresh items
and $m=\lfloor c/n\rfloor$ flips on each. For $0<e\le1$ let $H(k,e)$ be the
least nonnegative integer with $2H^2\ge k\lceil\log_2(1/e)\rceil$. Put
$\tau=1/n$, $r=H(m,\tau)/m$, and $a=H(n,\delta_j/3)/n$. An item is declared
positive if its observed head fraction is strictly above $1/2+r$, negative
if strictly below $1/2-r$, and unresolved otherwise. Write $p_+,p_-,p_0$
for the probabilities of these three outcomes and use hats for their sample
fractions. Return the interval
$$
 I_j=[\widehat p_+-a-\tau,\ 1-\widehat p_-+a+\tau]\cap[0,1].
$$

A Bernoulli sample mean of $k$ trials deviates in a specified direction by
more than $H(k,e)/k$ with probability at most $\exp(-2H^2/k)\le e$.
Condition on the latent pair. A wrong declaration requires such a deviation
with $e=\tau$. Thus $p_+\le\theta+\tau$ and $p_-\le1-\theta+\tau$.
When $D>2r$, even an unresolved outcome requires a deviation greater than
$r$ in one specified direction. Consequently $p_0\le P(D\le2r)+\tau$.
These applications use the one-sided bounded-sum inequality.
[Hoeffding, Theorem 2](https://doi.org/10.1080/01621459.1963.10500830)

The outcomes across the $n$ fresh items are iid. Apply the same one-sided
inequality to each of their three indicator averages. Except on an event of
probability at most $\delta_j$, all three satisfy $\widehat p_i\le p_i+a$.
The first two give $\theta\in I_j$. The third gives the width bound
$$
 |I_j|\le \widehat p_0+2a+2\tau\le P(D\le2r)+3a+3\tau .
$$

## All authorized budgets

Use stage caps $c_j=4\cdot2^j$ and $\delta_j=\delta/((j+1)(j+2))$, starting
at $j=0$. Intersect $[0,u]$ with every completed stage interval. Report the
previous intersection between checkpoints and $[0,u]$ before the first.
The failure allowances sum to $\delta$. Each stage uses $nm\le c_j$ flips,
and the ladder starts a stage only once its entire cap is available. This
gives simultaneous coverage, including at a data-dependent stopping time.
On the same event the width at each checkpoint is at most its stage bound.
As $j$ grows, $n,m$ increase geometrically, $a,r,\tau$ tend to zero and
$P(D\le2r)\to0$ by continuity at zero. This proves the theorem.

The [implementation](../toolkit/threshold_toolkit/unknown_law_confidence.py)
computes the thresholds with integer square roots and rational arithmetic.
With the toolkit on the import path, initialize
`unknown_law_confidence(coin_factory, delta="1/20", upper=1)`
and call `advance_to(B).interval` at any nondecreasing budgets. The factory gets a
population RNG and returns the next-flip callable for a fresh item. For a
known rarity bound use `upper=rho`. The existing ladder reports actual flips
and retains an empty intersection if observations fall on a failure path.
The statistical proof presumes independent draws and conditionally iid
observations. The implementation inherits the toolkit's integer-size limits.

## A time-uniform lower bound in the original experiment

Fix any known gap law and $0<\rho\le1/4$. Consider one online controller
under a physical flip cap at every integer budget $n$. Suppose a deterministic
nonincreasing envelope $t(n)$ bounds the interval half-width on a joint event
of simultaneous coverage and width with probability at least $1-\delta$ for
each admissible population. Then infinitely many $n$ satisfy
$$
 t(n)\ \ge\ \sqrt{\frac{3(1-\delta)\rho}{64}}\,
                 \sqrt{\frac{\log\log n}{n}} .
$$
This is a lower bound on the envelope. It does not require realized interval
width to exceed that expression on each individual sample path.

To prove it, restrict the sign law to a constant $\theta\in[\rho/2,\rho]$.
An iid Bernoulli($\theta$) stream can simulate the entire online experiment.
Use the next stream value as the sign of each new item. An independent seed
samples its gap and flip tape and the controller's own randomness. Revisits
retain the same latent item. At most $n$ signs are consumed by flip $n$.
The interval midpoint (arbitrary on an empty interval) is therefore an
estimator from $n$ iid draws and ancillary randomness. All budgets use the
same simulation. Formally one can augment each draw with an independent
copy of the entire random seed and use the first such copy. This preserves
both the iid model and its pairwise KL divergences.

For Bernoulli parameters $p,q\in[\rho/2,\rho]$, $\log x\le x-1$ gives
$D_{\rm KL}(p\Vert q)\le(p-q)^2/[q(1-q)]\le8(p-q)^2/(3\rho)$.
Duchi and Haque's Proposition 11 now gives the displayed lower bound with
$M=8/(3\rho)$. This transfer to the hidden-coin model uses only the
constant-sign-law subfamily.
[Duchi and Haque, COLT 2024, Proposition 11](https://proceedings.mlr.press/v247/duchi24a/duchi24a.pdf#page=8)

For the deterministic-gap law $D=1/2$, a fresh flip reveals the sign and the
repository's selection functional is $K(B)=\min(\rho,2\sqrt{\rho/B})$.
Indeed, selecting mass $x$ gives the concave objective
$2\sqrt{\rho x/B}+(1-x)\min(1,2/\sqrt B)$, whose minimum is at an endpoint,
followed by clipping at $\rho$. The lower bound thus matches the iterated
logarithm term of the known-law upper rate on this law for fixed $\delta$
as $n\to\infty$. It leaves open the full gap-law dependent lower bound and
whether a law-agnostic interval attains the known-law rate.

The [law-dependent lower-bound development](TIME_UNIFORM_LOWER.md) gives a matching paper proof when the asymptotic coefficient is finite, including every finite-inverse-moment gap law. Its prior-family and adaptive prefix-information bounds are Lean-checked. The full infinite-coefficient comparison remains open.
