# Running the known-law rare-event estimator

The procedure takes a known gap law on $(0,1/2]$, a global rarity bound
$0<\rho\le1/4$, and a positive expected flip budget $B$. Each call to
`new_item()` creates an independent coin and returns a callable for its next
Bernoulli flip. Its gap and sign are hidden. The estimator's random generator
must be independent of the population.

With `toolkit/` on the Python import path, a finite rational table is enough
to build and execute a plan.

```python
from random import Random
from threshold_toolkit.known_law_oracle import FiniteGapOracle
from threshold_toolkit.known_rare_estimator import plan_known_rare, estimate_known_rare
from threshold_toolkit.rare_event_functional import FiniteGapLaw

law = FiniteGapOracle(FiniteGapLaw([("1/2", 1)]))
plan = plan_known_rare(law, rho="1/4", budget=65536)
population = Random(21)

def new_item():
    bit = int(population.randrange(8) == 0)
    return lambda: bit

result = estimate_known_rare(new_item, plan, rng=Random(17))
print(float(result.value), result.items, result.flips, float(plan.mse_bound))
```

Here each coin is deterministic, positive with probability $1/8$ and negative
otherwise. The supplied law gives only the magnitude $1/2$. The estimator reads
the callable's flips, including those spent on coarse corrections. The actual
flip count is random. For small budgets the planner can choose the zero-flip
estimate $\rho/2$ with squared-error bound $\rho^2/4$.

## A confidence interval under a hard flip budget

The same program can run under the existing [capped-median driver](../toolkit/threshold_toolkit/confidence_amplification.py).
Each request identifies a coin and purchases one flip. Repeated requests to
the same ID retain its gap and sign. A block can therefore stop between any
two flips, including the two halves of a classifier round.

```python
from threshold_toolkit.confidence_amplification import MedianSchedule, run_capped_median
from threshold_toolkit.known_rare_estimator import known_rare_program

schedule = MedianSchedule(10_000_000, rho="1/4", delta="1/4")
base = plan_known_rare(law, rho=schedule.rho, budget=schedule.base_expected_budget)

def coin_factory(rng):
    bit = int(rng.randrange(8) == 0)
    return lambda: bit

out = run_capped_median(
    schedule, lambda budget, rng: known_rare_program(base, rng), coin_factory, seed=17
)
radius_squared = 8 * base.mse_bound
```

Use the schedule's base budget and rarity bound to build the plan. The
confidence interval is centered at `out.estimate`, has radius
$\sqrt{8\,\texttt{base.mse\_bound}}$, and is intersected with $[0,\rho]$.
For an admissible population with independent block randomness, it covers
the target with probability at least $1-\delta$. Each block exceeds its cap
with probability at most $1/8$ by the expected-work bound, and its uncapped
estimate misses that radius with probability at most $1/8$ by the MSE bound.
The schedule controls the probability that a majority of blocks fail. Its
total flip cap holds on every execution, including timed-out blocks.

## Integrating a continuous or mixed law

The [oracle interface](../toolkit/threshold_toolkit/known_law_oracle.py) has
two methods. The finite adapter computes rational probabilities and uses upper
endpoints for logarithmic work integrals.

- `split(rho,budget,precision)` supplies the design integrals for Appendix D.
  Remove the smallest-gap mass $\rho$, splitting a quantile atom if needed.
  The retained core $\sigma$ meets finitely many bands since its gaps are
  bounded below. Split the removed mass at $Bd^2=1$, with equality assigned
  to the resolved part $\tau$ and smaller gaps assigned to $\zeta$.
  Supply a rational upper bound for every occupied core band's
  $a_j=\int_{I_j}d^{-2}\,d\sigma$, and bounds $z^+\ge\zeta((0,1/2])$ and
  $H^+\ge\int d^{-1}\,d\tau$.
  The two functions of the cap $M$ bound $\eta_{\sigma+\tau}(M)$ and
  $O_\tau(M)$ as defined in the interface. The error envelope must tend to zero.
- `null_prefix(heads,tails,tolerance)` encloses the probability of one
  particular ordered prefix under the full all-negative mixture. Integrate
  $(1/2-d)^{\mathrm{heads}}(1/2+d)^{\mathrm{tails}}$ under the original
  law, without a binomial coefficient. Return an interval inside $[0,1]$
  with width at most the requested absolute tolerance. The caller is
  responsible for enclosing the true integral. The continuous uniform
  example in the [tests](../toolkit/tests/test_known_rare_estimator.py)
  integrates this polynomial directly.

## Work and error of a returned plan

The argument below applies to valid oracle bounds, iid items, independent
conditionally iid flips on each item and independent private randomness.
It uses the ordinary classifier, likelihood-bank estimates and cap schedule
in Appendices D and F of the [paper](../paper/v6/README.md).
The implementation and the following adaptations have executable tests.
The existing Lean upper theorem is about the mathematical experiment.

Let $\bar a_j$ be the oracle's band bounds, $\pi_j=\bar a_j/\sum_i\bar a_i$
on positive entries, and $\bar G$ the computed upper entropy of this vector
of costs. Then $\sum_j a_j(1+\log(1/\pi_j))\le\bar G$. This is the quantity
in the bank work proof after integrating the reference penalties.
Taking upper bounds can increase the cost charged by the planner.

At level $\ell$, set $\delta_\ell=\rho16^{-(\ell+1)}$ and $u=\delta_\ell/4$.
Use powers of four until the resolved error envelope is at most $\delta_\ell/8$.
All scheduled levels satisfy $z^+\le\delta_\ell/8$. Thus the ordinary
classifier's error is at most $\delta_\ell/4$. The bank and ordinary
classifier alternate flips. For the positive bank, let $N$ denote the
positive mixture's probability of the observed prefix and $D$ its true
null probability. Request width $uN/2$ and stop positive when the returned
upper endpoint is at most $uN$. This only accepts $D\le uN$ and always
accepts $D\le uN/2$, including $D=0$. The negative reference tests use
allowance $u/\rho$ and have priority. The paper's two wrong-bank events
have total probability at most $2u$. The level error is therefore at most
$\delta_\ell$.

For work, the implemented bank exits by the time of the exact bank with
allowance $u/(2\rho)$. The extra $\log 2$ in its log threshold is smaller
than one extra level's $\log16$. Substituting the cross-entropy bound above
in the bank work bound in Appendix D gives the valid raced level price

$$
 C_\ell=\min\{2M_\ell,\,
 80(\ell+2)\bar G+4(H^+)^2/\rho+2O_\tau^+(M_\ell)+2z^+M_\ell\}.
$$

The ordinary dyadic early test uses success counts and refines a rational
interval for $\log 2$. A terminal majority tie returns zero.
Let $k_0=C_0$, $k_\ell=C_\ell+C_{\ell-1}$ and $v_\ell=17\delta_\ell$.
A fine-minus-coarse mark uses successive unused flips of the same coin.
Its mean telescopes and its second moment is at most $v_\ell$ by the two
error bounds. At level zero the second moment is at most $\rho+\delta_0$.

Positive rational weights $w_\ell$ approximate $\sqrt{v_\ell/k_\ell}$.
Use mean counts $n_\ell=B w_\ell/\sum_i k_iw_i$, giving
$\sum_\ell n_\ell k_\ell=B$ exactly. Independent randomized rounding of
each $n_\ell$ has that mean and variance at most $n_\ell$. For independent
marks $X$, the normalized sum at that level has variance at most
$\mathbb E[X^2]/n_\ell$. The reported bound is consequently

$$
 \mathbb E[(\widehat\theta-\theta)^2]\le
 \delta_J^2+\sum_{\ell=0}^{J} v_\ell/n_\ell .
$$

Projection onto $[0,\rho]$ preserves this upper bound. The planner uses the
constant estimate if it has the smaller bound. This certificate applies
to the actual finite level schedule. Loose oracle envelopes can give loose
certificates. Integral evaluation, exact-rational likelihood arithmetic and
sampling time are separate from the flip budget; costs can be large for tiny
gaps or very large caps.

## Comparison with the paper rate

There is also a uniform rate guarantee when the integration oracle's
upper bounds for $a_j,z,H,\eta_\nu(M),O_\tau(M)$ are at most twice the
true quantities. A zero integral then has zero upper bound. The finite
adapter satisfies these conditions. Its only upper approximation among
these integrals is the logarithm in $O_\tau$. On $[1,2]$ the log-series
remainder at the minimum allowed precision is below $1/1000$.
For $x=2^k y\ge1$ with $1\le y<2$, the upper error is at most
$(k+1)/1000\le1+\log x$. Thus $1+\overline{\log x}\le2(1+\log x)$.
The same bound and coordinatewise monotonicity and homogeneity of cost entropy
give $\bar G\le 2G(\bar a)\le 4\Gamma_\sigma$.

Write $M_\ell^*$ and $C_\ell^*$ for the ideal caps and work bounds in
Appendix D. Since the true error at $M_{\ell+1}^*$ is at most
$\delta_{\ell+1}/8=\delta_\ell/128$, even twice this number passes the
implemented level-$\ell$ cap test. The ideal caps increase, so induction
gives $M_\ell\le M_{\ell+1}^*$. The stricter cutoff
$\delta_J\ge128z^+$ ensures that level $J+1$ lies within the paper's
terminal schedule when $z>0$. For $z=0$ its work bound holds for every
finite terminal level. The work kernel increases with the cap. Substituting
the factor-two bounds in the implemented level price gives
$C_\ell\le4C_{\ell+1}^*$. Consequently $k_\ell\le4k_{\ell+1}^*$, also for
$\ell=0$, and $v_\ell=16v_{\ell+1}$. Appendix D's multilevel sum bound yields
$
 \sum_{\ell=0}^J\sqrt{v_\ell k_\ell}
 \le 8C_{\rm sum}(\sqrt{\rho\Gamma_\sigma}+H).
$
The dyadic square-root bounds satisfy
$\sqrt{v_\ell/k_\ell}\le w_\ell\le2\sqrt{v_\ell/k_\ell}$, so the
variance is at most twice the square of the left side divided by $B$.

If the small-gap mass triggers the initial constant fallback, $\rho/2\le2048z$.
Otherwise the terminal rule gives
$\delta_J\le4096z+\rho/(1+\sqrt B)$. The last term is at most $K$ by the
[elementary selection floor](../lean/ThresholdHC/EntropyTail/Objective.lean)
and the cap at $\rho$. The quantile value is
$Q=\min\{\rho,z+(H+\sqrt{\rho\Gamma_\sigma})/\sqrt B\}$. When $Q=\rho$,
the comparison with the constant plan gives RMS at most $Q/2$. In the
other case the displayed work and bias estimates give RMS at most
$K+\max\{4096,8\sqrt2 C_{\rm sum}\}Q$. Using $Q\le(8/5)K$ proves a
uniform constant multiple of $K$ for this implementation under the
stated oracle accuracy assumptions. The per-plan MSE certificate above
is available even when those tighter relative bounds are unavailable.
