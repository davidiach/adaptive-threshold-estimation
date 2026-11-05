# Oracle-rate adaptation over a finite family of gap laws

The unknown law may be any member of a supplied nonempty finite family of distinct
probability laws on $(0,1/2]$. The locations, supports and weights may differ
between candidates. The algorithm knows the family, the rarity bound
$0<\rho\le1/4$, and $0<\delta\le1/4$, but not the candidate index or the sign
law. Signs may depend arbitrarily on the gap, subject to their total mass
being at most $\rho$.

**Finite-family theorem (paper proof).** There is one observable online
procedure with nested intervals and a hard physical flip cap at every integer
budget. Under every candidate law and every admissible sign law, simultaneous
coverage holds with probability at least $1-\delta$. There is an explicit
finite pilot cost $H$, depending only on the supplied family and $\delta$,
such that on that same event, for every integer $B\ge2H$,
$$
 \operatorname{halfwidth} I(B)\le
 3000004\,K_{\mu,\rho}\!\left(\frac{B}{\Lambda(B,\delta)}\right),
 \qquad
 \Lambda(B,\delta)=\log(1/\delta)+
 2\log\!\left(2+\frac{\log(1+B)}{\log2}\right).
$$
Here $\mu$ is the true, unknown candidate. A singleton family uses the existing
known-law procedure directly; the displayed bound then holds for $B\ge1$.

This is eventual oracle-rate adaptation with an additive identification cost.
It does not establish the unrestricted unknown-law theorem or a uniform
constant-factor guarantee before that cost has been paid.

## A sign-neutral observation

For a fresh coin, buy $2k$ flips $X_1,\ldots,X_{2k}$ and record
$$
 Z_k=\prod_{\ell=1}^{2k}(2X_\ell-1)\in\{-1,1\}.
$$
Conditionally on its persistent gap $d$ and sign $s$, independence of its
flips gives
$$
 \mathbb E[Z_k\mid d,s]=(2d)^{2k}.
$$
The even power removes the sign. Thus its unconditional mean is
$a_{\mu,k}=\int(2d)^{2k}\,\mu(dd)$ for every sign allocation, even one
depending on $d$. Fresh coins give independent observations of $Z_k$.
No latent gap or sign is observed or sampled by the algorithm.

## Finite moment signatures distinguish the candidates

Distinct probability laws on $(0,1/2]$ have different sequences of these
moments. Indeed, push a law forward by the injective map $d\mapsto(2d)^2$
into $[0,1]$. Equality of all positive moments and of total mass gives equality
of integrals of every polynomial. Polynomial uniform approximation gives
equality for every continuous function on $[0,1]$, which determines the
probability measure. The map has a measurable inverse on $(0,1]$, so the
original laws are equal as well.

For every pair of distinct candidates choose a differing moment. Taking the
largest of their finitely many indices gives an integer $m\ge1$ for which
the signatures $(a_{i,1},\ldots,a_{i,m})$ are pairwise distinct. Put
$$
 \eta=\min_{i\ne j}\max_{1\le k\le m}|a_{i,k}-a_{j,k}|>0,\qquad
 n=\left\lceil\frac{32}{\eta^2}\log\frac{4m}{\delta}\right\rceil,\qquad
 H=n\,m(m+1).
$$
The family and its moments determine all three quantities before observation.

For each $k=1,\ldots,m$, use $n$ fresh coins, each with $2k$ paid flips.
Let $\widehat a_k$ be the average parity. The total physical cost is exactly
$H$, including every revisit. Each coordinate is an average of independent
variables in $[-1,1]$. Hoeffding's inequality gives
$$
 \Pr\{|\widehat a_k-a_{i,k}|>\eta/4\}
 \le2\exp(-n\eta^2/32).
$$
A union bound over the $m$ coordinates is at most $\delta/2$.

Choose the first candidate whose every signature coordinate is within
$\eta/4$ of the empirical coordinate; use candidate zero if there is none.
On the event that all coordinates are accurate, the true candidate is
compatible. Two compatible candidates would have distance at most
$\eta/2<\eta$, so it is the unique compatible candidate. Hence the pilot
selects the true law with probability at least $1-\delta/2$, uniformly over
all admissible sign allocations. There is no union bound over candidate
procedures and no assumption about the sign probabilities conditional on a gap.

For finite-support candidates whose union of supports has $s$ points,
moments $1,\ldots,s-1$ suffice. After including the zeroth moment, the
Vandermonde matrix on the distinct values $(2d)^2$ is invertible, so equal
signatures would give equal masses at every support point.

## Reusing the known-law online procedure

During the pilot report $[0,\rho]$. After its $H$ paid flips, run the
known-law time-uniform procedure for the selected candidate with failure
allowance $\delta/2$. Use fresh coin labels and independent private randomness,
and charge its flips to the remaining budget $B-H$. The pilot can pause
between any two flips; after identification the selected procedure is fixed.
Consequently one shared controller supplies all budget prefixes, and the
physical cap holds even on pilot failure paths.

For the proof under true candidate $i$, consider the hypothetical known-law
procedure for $i$ on the fresh post-pilot stream. Its simultaneous failure
probability is at most $\delta/2$. On correct identification the actual
procedure agrees with it. The failure event of the combined procedure is
contained in the union of pilot error and failure of that one hypothetical
true-law procedure. Their probabilities sum to at most $\delta$.
Independence between these two failure events is not required. Independence
and fresh labels ensure the post-pilot stream has the law required by the
known-law theorem.

On this joint good event, for $B-H\ge1$ the known-law theorem gives radius
at most
$$
 1500002\,K_{\mu,\rho}\!\left(
 \frac{B-H}{\Lambda(B-H,\delta/2)}\right).
$$
If $B\ge2H$, then $B-H\ge B/2$. Monotonicity in budget and the identity
$\Lambda(B,\delta/2)=\Lambda(B,\delta)+\log2$ give
$\Lambda(B-H,\delta/2)\le2\Lambda(B,\delta)$. Therefore the effective
post-pilot budget is at least $B/[4\Lambda(B,\delta)]$.
Monotonicity and square-root budget scaling of $K$ prove the stated
coefficient $3000004$. Intersecting the selected intervals preserves nesting
and coverage. The same simultaneous event protects data-dependent stopping
budgets.

## Executable pilot for rational finite candidates

The [pilot](../toolkit/threshold_toolkit/law_identification.py) uses exact
rational moment signatures. Its failure argument uses the larger integer
$\lceil\log_2(2m/\delta_{\rm pilot})\rceil$ in place of the natural logarithm.
For the theorem above pass $\delta_{\rm pilot}=\delta/2$.

With `toolkit/` on the import path:
~~~python
from threshold_toolkit.rare_event_functional import FiniteGapLaw
from threshold_toolkit.law_identification import plan_law_pilot, run_law_pilot

candidates = [FiniteGapLaw([("1/2", 1)]), FiniteGapLaw([("1/4", 1)])]
plan = plan_law_pilot(candidates, delta="1/40")
# coin_factory supplies independent persistent coins through their flip callbacks.
result = run_law_pilot(plan, coin_factory, budget=plan.flip_cap)
selected_law = candidates[result.selected]
~~~

The function checks authorization for the entire pilot before creating a coin.
It returns a candidate index and the actual flip count, not a test that the
true law belongs to the family. A singleton family costs zero flips.
Duplicate laws are rejected. The default search limit is 32 moments;
increase `max_moments` if the candidate signatures are not yet separated.
The sampler does not itself construct the subsequent confidence sequence.

## Verification boundary and next work

The new Lean modules check the finite-prefix parity identities, bounded
average concentration, separated-signature identification and its error
union bound, transfer of simultaneous properties after selection, physical
budget arithmetic, and the delayed oracle-rate comparison. These are
components of the theorem. The moment-determinacy argument, the concrete
fresh-coin pilot realization, and the complete selected-controller
construction above remain paper proofs. Python execution is not Lean-verified.

The candidate-family premise is substantive and cannot be verified by this
pilot. Very close signatures can make $H$ large. This theorem gives no
family-uniform onset time and no guarantee under a law outside the supplied
family. To obtain the unrestricted result, a further argument must control
model approximation and unobserved small-gap mass while retaining honest
coverage and oracle-rate width. Finite-family identification alone does not
supply that argument.

