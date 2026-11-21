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

**Verification boundary:** the time-uniform lower bound below was a paper proof
in this note, applying Duchi and Haque's Proposition 11 as a cited result. It
is Lean-checked since 21 November 2026 by a direct route, for every gap law,
every $0<\delta<1$ and without monotonicity of the envelope
([`bernoulli_time_uniform_lower`](../lean/ThresholdHC/BernoulliTimeUniform/Full.lean),
[record](../results/bernoulli-time-uniform-20261121/README.md)). The upper theorem was a paper proof too; it
is Lean-checked since 21 November 2026 for the construction run in the
observable simulation, with coverage at every integer budget on one measurable
event of probability at least $1-\delta$, the stage width bound and the width
limit ([`unknown_law_confidence`](../lean/ThresholdHC/UnknownLawConfidence/Full.lean),
[record](../results/unknown-law-confidence-20261121/README.md)). The toolkit's unit
tests check the integer thresholds, interval endpoints and flip budget, not
the coverage or width claims.

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

*Lean check, 21 November 2026.*
[`bernoulli_time_uniform_lower`](../lean/ThresholdHC/BernoulliTimeUniform/Full.lean)
states the displayed bound in the original hidden-gap online experiment, for
every gap law, $0<\rho\le1/4$ and $0<\delta<1$. Its hypothesis is the joint
coverage-and-width event of the law-dependent lower bound, for every sign law
of mean at most $\rho$. The envelope need not be nonincreasing, and "infinitely
many $n$" reads: for every $M$ some $n\ge\max(M,3)$. The Lean proof neither
simulates an iid stream nor uses Proposition 11. It bounds the observable
prefix KL of two constant sign laws directly by
$n(\theta'-\theta)^2/[\theta(1-\theta)]$, a statement of its own
(`constant_prior_prefix_kl`), and runs a first-crossing test of the base law
$3\rho/4$ against $3\rho/4+\rho/(4\cdot3^k)$ at geometric budgets
([record](../results/bernoulli-time-uniform-20261121/README.md)).

For the deterministic-gap law $D=1/2$, a fresh flip reveals the sign and the
repository's selection functional is $K(B)=\min(\rho,2\sqrt{\rho/B})$.
Indeed, selecting mass $x$ gives the concave objective
$2\sqrt{\rho x/B}+(1-x)\min(1,2/\sqrt B)$, whose minimum is at an endpoint,
followed by clipping at $\rho$. The lower bound thus matches the iterated
logarithm term of the known-law upper rate on this law for fixed $\delta$
as $n\to\infty$. The [full gap-law dependent comparison](TIME_UNIFORM_LOWER.md) now has a complete Lean proof. The [arbitrary-law adaptation theorem](ARBITRARY_LAW_ADAPTATION.md) gives a law-agnostic interval whose width is within a universal constant of the known-law rate after a law-dependent onset; its [full observable controller is now Lean-checked](ARBITRARY_LAW_FORMALIZATION.md#full-arbitrary-law-all-budget-controller).

The [law-dependent lower-bound development](TIME_UNIFORM_LOWER.md) proves that every deterministic joint coverage-and-width envelope exceeds a universal multiple of the known-law rate infinitely often, for every positive-gap law. Its prior-family, sequential-testing, infinite-moment and asymptotic arguments are Lean-checked, including the observable interval consequence. The [complete audit](../results/anytime-asymptotic-20261105/README.md) verifies the deterministic-envelope bound without a monotonicity assumption. The sharper Bernoulli-subfamily coefficient described on this page is Lean-checked since 21 November 2026 ([record](../results/bernoulli-time-uniform-20261121/README.md)), as is the unknown-law upper construction ([record](../results/unknown-law-confidence-20261121/README.md)).

## Adaptation within a supplied finite family

The [finite-family theorem](FINITE_FAMILY_ADAPTATION.md) gives the known-law
time-uniform rate after an explicit finite pilot cost, even when candidate
supports differ. Even products of observed flips identify moment signatures
without assumptions on how signs depend on gaps. Seventeen Lean statements
check the original components, and a further
[22-statement audit](../results/law-adaptation-realization-20261105/README.md)
verifies moment determinacy, the actual pilot and full observable selected
controller, including joint all-budget coverage and oracle width.
The [executable controller](FINITE_FAMILY_ADAPTATION.md#executable-confidence-sequence)
connects a resumable pilot to the known-law estimator's confidence stages under
one physical flip budget. Python execution remains unverified. The supplied
candidate-family premise is required for that construction. The new
[arbitrary-law adaptation theorem](ARBITRARY_LAW_ADAPTATION.md)
removes the candidate-family premise using learned conservative laws;
that additional theorem now has a [complete Lean audit](../results/arbitrary-law-controller-20261116/README.md).
