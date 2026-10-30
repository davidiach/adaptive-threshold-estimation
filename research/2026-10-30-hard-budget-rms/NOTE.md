# Hard-budget RMS without logarithmic rate loss

Integration baseline: `2bc506d62387c511bac8fecbd07ec0e4026b10ce`.
This is a focused extraction of the round-three contribution, not a replacement
for the original delivery. All new mathematical statements here are paper
proofs, not Lean-checked. The ordinary and critical applications use existing
formalized premises; the arbitrary-law rare-event application additionally
uses the paper-only entropy-tail theorem. No literature-wide priority claim
is made. Confidence sequences and optional-stopping guarantees are separate.

## 1. Statistical model and scope

Each fresh coin draws an independent hidden magnitude D with law mu on
(0,1/2] and a hidden sign with positive probability q(D). Conditional flips
have mean 1/2 plus or minus D. Its latent state persists on revisits.
Algorithms see only their independent randomness and purchased flips;
creation, revisits, interleaving and stopping may be adaptive. Every flip
costs one. The target is theta = integral q dmu.

In the rare-event class, 0 <= q <= 1 and integral q dmu <= rho, with known
0 < rho <= 1/4. This is global rarity, not q(d) <= rho. Known-law rare-event
base procedures may use mu and rho; the ordinary family is law-independent.

Write R_exp(B) for minimax RMS under sup E T <= B, and R_hard(B) under the
pathwise cap T <= floor(B). Necessarily R_exp(B) <= R_hard(B).

## 2. General reduction

Let theta range in [0,M], 0 < M <= 1. For each dyadic b >= 1 suppose an
observable base procedure has output Y_b and integer work T_b with

$$E T_b\le b,\qquad E(Y_b-\theta)^2\le C^2f(b)^2$$

uniformly over the parameter class. Assume C >= 1/2, f(1/2)=M and

$$f(b)\le\sqrt{B/b}\,f(B)\quad\text{for }B\ge b\ge1/2.$$

Complete runs use independent seeds, fresh latent coins and observation tapes
under each fixed parameter. There is **no** independence assumption between
a run's error and its runtime. The uncapped output need not be bounded or
unbiased. Clip it to [0,M] when it is returned.

At stage j >= 0 set

$$b_j=2^j,\quad n_j=4\cdot2^j,\quad
S_j=\sum_{i=0}^j n_i=4(2^{j+1}-1).$$

Initialize Z_-1=M/2. Run the base procedure with expected allowance b_j but
abort before observation n_j+1. On completion set Z_j to the clipped output;
on timeout retain Z_(j-1). Completion immediately after observation n_j is a
success. At a deterministic authorized allowance B >= 4, execute through the
largest m with S_m <= floor(B). Caps, not realized spend, determine this
reservation schedule. At B < 4 return the midpoint without work.

**Theorem.** For B >= 4 this procedure has a pathwise cap floor(B) and

$$\sup E(Z_m-\theta)^2\le32C^2f(B)^2.$$

It never evaluates f or C. A nuisance-law-independent base family gives a
nuisance-law-independent transformed family.

**Proof.** The pathwise cap follows by summing reservations. Markov gives
p_j = P(T_(b_j) > n_j) <= 1/4. Independence of the previous retained estimate
from the next complete run gives, for D_j = E(Z_j-theta)^2,

$$D_j=E[(\operatorname{clip}(Y_{b_j})-\theta)^2;T_{b_j}\le n_j]
       +p_jD_{j-1}
\le C^2f(b_j)^2+\tfrac14D_{j-1}.$$

The error guarantee is not conditioned on successful completion: a
nonnegative part of the full moment is simply discarded. Introduce b_-1=1/2.
Then D_-1 <= M^2/4 <= C^2 f(1/2)^2, so

$$D_m\le C^2\sum_{k=-1}^m4^{-(m-k)}f(b_k)^2
\le C^2\frac{B}{b_m}f(B)^2\sum_{l=0}^{m+1}2^{-l}.$$

The next checkpoint satisfies B < S_(m+1) = 16 b_m - 4. Hence B/b_m < 16
and the geometric sum is less than two. This proves the result. All
inequalities are uniform in the parameter. QED.

**Observable realization.** Pair a stage index and local coin identifier to
obtain disjoint namespaces, retaining each pairing on revisits. Independent
seed and tape arrays realize independent complete runs. The cap controller
reads only requested observations and termination. Clipping and retaining a
previous measurable output are measurable operations. No rate, latent state
or target is revealed. This is a paper-level realization, not a Lean proof.

The same stages can be retained while the authorized allowance increases.
The theorem holds at every *deterministic* allowance. It does not justify
substituting a data-selected stopping time or realized spend for B. It does
not preserve unbiasedness, prove simultaneous normalized error control, or
bound arbitrary callback CPU time.

### General moment version

For s > 0 and gamma > 0 suppose the s-th moment is at most C^s f(b)^s,
f(b) <= (B/b)^gamma f(B), and M/2 <= C f(1/2). Use integer caps a 2^j,
where a > 2^(gamma s). For B >= a, the identical argument gives

$$\bigl(E|Z_m-\theta|^s\bigr)^{1/s}
\le C\frac{(4a)^\gamma}{(1-2^{\gamma s}/a)^{1/s}}f(B).$$

The timeout probability is at most 1/a, B/b_m < 4a, and the series ratio is
2^(gamma s)/a. No triangle inequality or condition s >= 1 is needed.
For s=2, gamma=1/2 the squared factor is 4a^2/(a-2), minimized at a=4.
This only optimizes this displayed bound within the dyadic construction.
The implementation supports the RMS calibration, not arbitrary s and gamma.

## 3. Scaling of the threshold rates

The ordinary rate is f(B)=omega_mu(B^(-1/2)), with

$$\omega_\mu(h)=\int\min\{1,h/d\}\,\mu(dd).$$

For rare events use canonical dyadic bands I_j=(2^(-j-2),2^(-j-1)],
a_j(sigma)=integral_(I_j) d^(-2) dsigma, and
G(a)=A+sum a_j log(A/a_j), A=sum a_j. Define Gamma_sigma as the monotone
supremum of G over finite band prefixes, allowing infinity. The inherited
functional is

$$K_{\mu,\rho}(B)=\min\left\{\rho,\inf_{0\le\sigma\le\mu}
\left[B^{-1/2}\sqrt{\rho\Gamma_\sigma}
 +\int\min\{1,B^{-1/2}/d\}\,d(\mu-\sigma)\right]\right\}.$$

For c >= 1, the pointwise inequality min(1,sqrt(c)x) <= sqrt(c)min(1,x)
gives

$$\omega_\mu(\sqrt{c/B})\le\sqrt c\,\omega_\mu(B^{-1/2}),
\qquad K(B/c)\le\sqrt c\,K(B).$$

For K, apply this to every fixed selection and then take the infimum and
outer cap. Infinite objective values cause no problem since the zero
selection has finite cost. Both rates are nonincreasing in B.

For B <= 4 both rates saturate: omega=1 and K=rho. Indeed h >= 1/2 makes
the ordinary integrand one. If sigma has mass z then Gamma_sigma >= 4z,
so its objective is at least sqrt(rho z)+1-z. Concavity in z on [0,1]
bounds this below by min(1,sqrt(rho)) >= rho. The outer cap proves K=rho.

For all B > 0 the same argument with the ordinary lower integrand
min(1,2/sqrt(B)) gives

$$K(B)\ge\min\{\rho,2\sqrt{\rho/B}\}>0.$$

This positivity permits strict-slack approximate minimizers without
assuming that the statistical minimax infimum is attained.

## 4. Applications and dependency ledger

**Ordinary, distribution-blind.** The pinned source supplies one observable
family chosen before mu with expected work b and RMS <=512 omega_mu(b^(-1/2)),
and the expected-budget lower coefficient 1/64. The new paper reduction gives

$$\frac1{64}\omega_\mu(B^{-1/2})\le R^{\rm hard}_\mu(B)
\le3000\omega_\mu(B^{-1/2}),\qquad B\ge1,$$

since 512 sqrt(32) < 3000; the midpoint handles B < 4. These premises have
Lean statements. Their application through a paper-only controller is not a
new Lean theorem.

**Known-law arbitrary rare events.** The general-law paper states
10^(-17) K <= R_exp <= 33000 K. Choose approximate minimizers with coefficient
33001 at the countably many dyadic budgets. The reduction gives

$$10^{-17}K(B)\le R^{\rm hard}(B)\le190000K(B),\qquad B>0,$$

using 33001 sqrt(32) < 190000 and the saturated midpoint case. This application
is conditional on the inherited paper-only general-law statistical proof.
No unknown-law or unknown-rarity adaptation is claimed.

**Critical law.** For mu(dd)=32d dd on (0,1/4], let
L=1+log(1/rho) and H=1+log L. Applying the reduction directly to the existing
critical upper and lower results gives

$$R^{\rm hard}(B)\asymp\min\{\rho,\sqrt{\rho LH/B}\}.$$

The original upper coefficient 100000 gives a conservative hard coefficient
570000. This path uses the existing critical premises, not the arbitrary-law
packing or the round-two confidence transfer. The new conclusion is still
paper-only.

## 5. Necessary assumptions: counterexamples

At mu=delta_(1/2), a fresh flip reveals an iid Bernoulli sign. Fix rho=1/4.
For dyadic b >= 4, take b/4 fresh observations and form a clipped sample mean.
Independently, with probability p=1/8, request 4b discarded observations
before returning. Expected work is b/4+(1/8)4b=3b/4 <= b. The uncapped MSE
is at most min(rho^2,4rho/b)=K(b)^2. At b=1,2 use the zero-work midpoint.

At theta=0 the uncapped estimate is zero. A single cap at 4b followed by a
midpoint on timeout instead has MSE p(rho/2)^2=rho^2/32, a nonvanishing floor.
For the independent fallback ladder, after stage m >= 2 the exact MSE is
(rho/2)^2 p^(m-1). If the *same* delay bit is reused at every stage, every
base still has the same marginal work/error guarantees but the floor remains.
Thus independence of complete runs cannot be replaced by marginal guarantees
or by restarts on unused flips of the same hidden coin.

## 6. Implementation, verification, and formalization targets

`budget_ladders.py` is a standard-library driver. Generators request local
coin IDs; revisits persist within each stage. Callbacks must honor the
statistical contract. Separate PRNG seeds are interfaces for independent
runs, not a mathematical proof of arbitrary callbacks or the PRNG.
An exception invalidates the driver. Reservations and actual flips are
reported separately. The driver does not implement the optimal base family.

The 24 extracted unit tests and exact finite audits are reproducible with:

```sh
python -m unittest discover -s toolkit/tests -p 'test_budget_ladders.py' -v
python research/2026-10-30-hard-budget-rms/verify.py
```

The verifier writes only `.runtime/hard-budget-rms/`. Its 56 recurrence
instances, 26,232 independent paths, 224 work-premise checks, 112 risk bounds
and 10,301 schedules are finite evidence, not universal proofs. Local
integration tests used an additive checkout because a full network clone
was unavailable. Full upstream tests and CI must be checked at the uploaded
commit. No new Lean kernel build was run.

First lock the full observable controller statement. Then prove cap and
persistent-label semantics, independent stage execution, the risk recursion,
and the ordinary and critical instantiations. A scalar recursion lemma alone
would not establish the complete algorithmic theorem.

## Sources

The inherited premises and definitions are at baseline `6ad675e`:
`lean/ThresholdHC/BlindUpper/Full.lean`, `lean/ThresholdHC/Tier6/Full.lean`,
`lean/ThresholdHC/CriticalUpper/Full.lean`, `docs/RESULTS.md`,
`paper/v6/entropy-tail-statement.tex`, and
`paper/v6/appendix-entropy-tail-lower.tex`.
The source of this extraction is the round-three archive with SHA-256
`1ffd571e2a5cd5ff10f681624cc00fbe535e7723ce65a1390d0b066563823e9f`.
Its original archive, PDF and validation record remain unchanged as delivered
artifacts. This integration does not silently upgrade their review status.
