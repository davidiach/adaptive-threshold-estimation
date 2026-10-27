# Alternate attack: nonlinear aggregation with fixed acquisition

Date: 2026-10-27. Role: alternate mathematical construction and source check.
This agent contributed the arguments below and is **not** an independent
reviewer of them. Model diversity among the agents is not guaranteed. The
unrestricted critical minimax problem remains open in this file.

The current checkout was `d75c775633df545b892e69fc876930d6d2dcc329` when
this investigation began. Concurrent Tier5 and population-step files were
read only and are not owned by this work. No existing verification record
was overwritten.

## What the neighboring population work already establishes

The inspected files were `research/2026-10-27-population-step/FINAL_REPORT.md`,
`lower/RESULT.md`, `upper/RESULT.md`, and `ALGORITHMS.md`. They record a
paper-proof counterexample to an extra-logarithm information upper bound on
the known radial profile, a calibrated estimator attaining the candidate
rate on that profile, and a conditional information/work direct-sum theorem.
Those results do not give an arbitrary-q upper bound. In particular, another
radial Fisher search would duplicate a resolved restricted question.

The inherited critical-two theorem establishes the extra factor
`H = 1 + log(1 + log(1/rho))` for uniformly small-bias single-coin estimators
and for the stated noninteractive additive population class. It does not
itself bound clipped or otherwise nonlinear outputs. The present target is
to decide whether nonlinear postprocessing of fixed acquisition can escape
that result, without silently permitting acquisition feedback.

## Direct iid foundation and scope warning

For one fixed observable acquisition kernel, let `P_q` be its stopped
transcript law, including its independent seed. The kernel can depend on
the known law, rarity, and budget, and can have unbounded stopping with
finite uniform expected work. Conditional on the hidden `(D,S)`, it is one
fixed probability kernel, so `q -> P_q` is affine. The global set
`0 <= q <= 1, integral q <= rho` is weak-star compact in `L-infinity(mu)`.

Theorem 1 and Proposition 4 of [Polyanskiy--Wu, arXiv:1902.05616v2,
Section 2](https://arxiv.org/pdf/1902.05616) apply directly: take the test
space to be all bounded measurable transcript functions. Such functions
are dense in every `L2(P_q)`. Both their first and second moments are
weak-star continuous, since conditional expectations given `(D,S)` are
bounded measurable functions integrated against `mu`. The target is the
continuous affine functional `integral q`. Thus their iid affine-risk
comparison has its stated uniform constant; no finite stopping or strong
Feller assumption is being added. An arbitrarily small optimization slack
avoids claiming an attained optimal score.

This is an application of an existing theorem, not a new general affine
optimality theorem. It applies to a deterministic number of independent
copies of the same acquisition kernel. Feeding the entire population
transcript into this result as if its law were affine is invalid: even two
independent coin transcripts have the product law `P_q tensor P_q`, which
is generally nonlinear in `q`. The iid structure is an explicit premise of
the cited result. A history-dependent acquisition policy is not reduced to
that structure merely because the reservoir class is convex.

## Poisson replication: complete proposed extension

**Status:** paper argument proposed for separate adversarial review. The
parent proposed the enlarged Poisson reference measure; this agent checked
and developed the domination, approximation, smoothing, and risk steps.
It is not yet an independently accepted result in this file.

### Precise model and claim

Fix `0 < rho <= 1/4`, one known gap law, and one measurable observable
single-coin acquisition procedure with uniformly finite expected charged
work `W`. Its complete stopped transcript takes values in a standard Borel
space `Z`. This includes canonical independent seeds and finite observed
bit words, with a cemetery value on nontermination. Since the expected work
is finite under the admissible reference `q_*(d)=rho`, that cemetery event
has probability zero under the reference and all admissible populations.

Choose a finite deterministic `lambda > 0` independently of unknown `q`.
Draw `N ~ Poisson(lambda)` independently before all observations and run
`N` independent copies of this *same* procedure. An arbitrary terminal
estimator may use `N`, all stopped transcripts, and additional independent
randomness, but cannot change the acquisitions or the count using their
outcomes. Suppose its worst-case RMS is `r` for estimating
`theta(q)=integral q`. Then for every `epsilon > 0` there is an estimator
of the form

`c + sum_{i=1}^N g(Z_i)`

with `g` a bounded measurable function and with worst-case RMS at most
`21 r + epsilon`, using precisely the same genuine observations. Its offset
and all separate component moments are finite. This comparison is uniform
in the law, `rho`, `lambda`, and kernel. It concerns existence in the usual
measurable-policy model, where computation is uncharged; it does not assert
a tractable algorithm for optimizing `g`.

### Step 1: a uniformly dominating reference, including arbitrary counts

Let `P_* = P_{q_*}`. Comparing the positive and negative latent components
before applying the observable kernel gives, as measures,

`P_q <= rho^(-1) P_*`.

Indeed `q <= 1 <= q_*/rho` and
`1-q <= 1 <= (1-q_*)/rho`. This argument neither observes the latent sign
nor changes the actual acquisition procedure.

Let `Q_q` be the law of the ordered Poisson sample and let `R` instead use
`N ~ Poisson(lambda/rho)` and iid marks `P_*`. For each fixed `q`, choose
a Radon--Nikodym version of its mark density. On the stratum of size `n`,

`dQ_q/dR = exp(lambda/rho-lambda) rho^n product_i (dP_q/dP_*)(Z_i)
         <= exp(lambda/rho-lambda) =: C_ref < infinity`.

The domination is for every admissible `q`; its possibly very large
constant is harmless for existence of a finite approximation. Using the
same Poisson rate for the reference would leave a factor `rho^(-N)` and
would not give this uniform bound. These are mathematical comparison
measures, not extra genuine observations supplied to the estimator.

### Step 2: finite mark partitions, without capping actual work or count

Clip the given estimator to `[0,rho]`, average over its independent final
randomization, and average over all `n!` permutations on each size-`n`
stratum. Jensen's inequality and iid marks show that these operations
cannot increase risk. The result `F` is a bounded measurable function of
the finite unordered marked sample.

Choose a countable separating algebra of the standard Borel mark space.
Its first `m` generators give a finite refining partition `A_m`. The
associated count vectors generate the sigma field of finite counting
measures: counts on that algebra determine the finite marked measure, and
the evaluation sigma field is generated by those counts. Therefore

`F_m = E_R[F | counts on A_m] -> F in L2(R)`.

Each `F_m` is a known `[0,rho]`-valued function of a finite count vector.
The domination above yields

`sup_q ||F_m-F||_(L2(Q_q)) <= sqrt(C_ref) ||F_m-F||_(L2(R)) -> 0`.

Thus a finite count-vector estimator achieves RMS `r+eta` for any chosen
`eta > 0`. This approximation retains the entire acquisition and the
unbounded preselected count; it adds no charged observations. Partition
membership is a measurable function of the observable stopped transcript.
No partition can inspect `D`, `S`, or the unknown `q`.

### Step 3: finite convex Poisson model, with zero intensities handled

Write `p_j(q)=P_q(A_m,j)`. By Poisson marking, the count coordinates are
independent Poisson variables with means `lambda p_j(q)`. The image

`X = {(p_1(q),...,p_J(q),theta(q)): q in Q_rho}`

is compact and convex: all coordinates are weak-star continuous affine
functionals. Keep `theta` as its own coordinate. It need not be identifiable
from the finite probability vector. Hence a theorem requiring the target
to be a linear function of those observed intensities cannot be invoked
without an additional argument.

For a small `tau > 0`, add independent artificial counts
`K_j ~ Poisson(tau/J)` using only internal randomness. All augmented
intensities are strictly positive. Evaluate `F_m` on the augmented counts.
Under the coupling this differs from the original output only when some
artificial count is positive, a probability `1-exp(-tau) <= tau`; therefore
its uniform RMS is at most `r+eta+rho sqrt(tau)`.

The augmented finite Poisson product is a good observation family in the
sense of [Juditsky--Nemirovski 2009, Examples 2 and 4 and Theorem 3.1]
(https://www2.isye.gatech.edu/~nemirovs/AnnStat_Saddle_2009.pdf). Its log
moment-generating function for an affine count score is affine in the
intensities. Their underlying convex parameter can be the full vector in
`X`, so nonidentifiability of the target at a finite partition is allowed.

### Step 4: quadratic risk from one fixed exponential certificate

The cited theorem is stated for confidence risk, so the following step is
necessary. Do **not** integrate risk bounds of different estimators chosen
at different confidence levels.

Fix the confidence level `e_0=1/16` and put `t_0=log(32)`. The saddle
construction in its Lemma 3.1 supplies an affine score `A` and a positive
scale `alpha` with a risk certificate `R_c`, arbitrarily close to its
optimal certificate, such that uniformly in the parameter and for `s>=0`,

`Pr{|A-theta| > R_c+s} <= e_0 exp(-s/alpha)`.

Putting the same parameter on both sides of its saddle objective gives
`alpha <= R_c/t_0` (equation (3.1) and the following diagonal inequality).
Theorem 3.1 and Lemma 3.2 bound the optimal certificate by five times the
best `e_0`-confidence radius. An estimator of RMS `u` has such radius at
most `4u`, with an arbitrarily small strict slack by Markov's inequality.
Consequently `R_c <= 20u + arbitrarily small slack`. Integrating the tail
of this **single** score gives

`sup E(A-theta)^2 <= R_c^2 + 2 e_0 R_c alpha + 2 e_0 alpha^2
                  <= R_c^2 [1 + 1/(8 log32) + 1/(8 (log32)^2)]`.

The square root of the bracket is less than `21/20`. Therefore the affine
RMS is at most `21u` with arbitrary slack. Set
`u=r+eta+rho sqrt(tau)` and take the approximation parameters sufficiently
small to obtain the claimed `21r+epsilon` comparison. This proof only uses
the finite-dimensional confidence theorem and its actual exponential
certificate; no unproved RMS assertion for arbitrary exponential families
is imported.

### Step 5: observable additive implementation and moment audit

The resulting affine score has the form
`c + sum_j beta_j (C_j+K_j)`. Average over the artificial counts to replace
their contribution by the known constant `tau sum_j beta_j/J`; Jensen's
inequality can only improve squared risk. What remains is

`c' + sum_{i=1}^N beta_{label(Z_i)}`.

The score has finitely many finite coefficients, so it is a bounded
single-coin output. In particular
`sup_q E sum_i g(Z_i)^2 <= lambda ||g||_infinity^2 < infinity` and
`sup_q E(c'+sum_i g(Z_i))^2 < infinity`. The count has finite mean
`lambda` and work is exactly `lambda E_q T` for each `q`, hence at most
`lambda W` uniformly. Its acquisition receives the same allowed inputs as
the original procedure. This is an element of the inherited additive
class, not merely an abstract square-integrable random variable.

### Consequence and restrictions

If separately accepted, applying the inherited additive lower bound gives
the same critical rate, up to universal constants, for *arbitrary nonlinear
terminal aggregation of independent Poisson replication of one fixed
kernel*. Thus clipping, robust averaging, and a nonlinear fit to these
already acquired iid transcripts cannot remove the critical `sqrt(H)`
factor uniformly over all global-rarity allocations.

This statement does not allow count selection from observations,
pilot-dependent acquisition, a shared seed choosing the acquisition law,
heterogeneous acquisition across coins, or interleaving that changes a
coin's policy using another coin's outcomes. Those models require separate
arguments. A single exact Poisson count is covered; arbitrary preselected
random count distributions are not inferred from the calculation above.

## A possible central lemma for the unrestricted question

The remaining difficulty is not whether the transcript family of a fixed
single-coin policy is convex. For a population information reduction the
denominator must be work under the comparison population actually used in
the divergence, rather than its unrelated worst-case work.

A potentially sufficient stronger premise is: at a fixed target
separation `delta`, every one-coin policy admits `q0,q1 in Q_rho` with
`theta(q1)-theta(q0) >= delta` and

`chi-square(P_A,q1 || P_A,q0) <= kappa E_q0 T_A`.

The pair domain with that oriented target constraint is convex, and the
left side minus the work term is convex in the pair for a fixed policy.
It is affine under a revealed independent mixture of policies. Under
appropriate compactness and semicontinuity, a minimax argument could then
seek a single pair valid against every policy, followed by a population
direct sum. **This is an unproved research route.** Existing separate
variance/work bounds do not establish the premise with `E_q0 T_A`; a
bound using `sup_q E_q T_A` does not suffice. Uniform domination only gives
a potentially disastrous `1/rho` comparison, not a constant comparison.

No unrestricted minimax theorem, counterexample, or new formal result is
claimed by this alternate investigation.

## Subsequent base-cost advance and scoped second review

The parent proposed restricting the adversarial class to `q<=1/2` and
tracking only all-negative work. This agent proved the stronger entropy
product in the new `base_cost.md`, then translated it into `base_cost.tex`
with the full finite-gap dependency reproduced. Its statement is
`sup_q Var_q(Y) * E_0 T >= c rho L H` under uniform bias at most `rho/64`
on that capped global class. The all-negative cost, rather than an
unrelated worst-case cost, repairs the specific alignment obstacle above.
The independent adversarial role reported no blocking finding in the
Markdown proof at SHA256
`58a235efbd06757826ad688f246a0f03d9ea92a965444136c270d00cea19f969`.
The TeX translation hash is
`6c02a467ac9a8b989ccb3e3618a9bb567e332ed1d3830d70fca27c01e5e3265a`;
translation review is a separate check. This is paper-proof status, not
Lean acceptance.

I then read the construction agent's distinct fragment
`affine_comparison.tex`, SHA256
`c243a6ad355aeabb2fea3df195166faf066b95b4e5778e3bc02512d61a80f7c2`.
No blocking defect was found in its finite convex-experiment RMS
comparison, exact stopped `(T,heads)` reduction, per-policy hard-pair
extraction, and simultaneous-pair minimax argument. Specifically:

- Conditional on `(T,heads)`, the full seed and stopped word have a
  population-independent law. The finite conditional Bernoulli word
  likelihood cancels, including for continuous independent seeds.
- The positive finite probability image with the target retained as an
  extra coordinate is compact and convex. The saddle comparison proves
  an exponential bound for one fixed estimator, and integration of that
  bound gives the advertised RMS constant twelve.
- The one-index additive reduction has base work exactly `w=E_0T_A`
  and uniform variance at most `(7/3)n r^2`. The common-mass calculation
  uses `theta<=rho`, not the false pointwise condition `q<=rho`.
- Both branches of the hard-pair choice
  `x=beta^2 rho L H/(4 delta^2 w)` have the stated constants; the
  `w=0` branch is treated before division.
- Revealing a mixture index makes the one-coin squared Hellinger
  distances affine in mixing weights. Finite-simplex minimax followed
  by the finite intersection property on the weak-star compact pair
  set produces one pair for every capped policy. No topology on all
  policies or false unrevealed-mixture identity is needed.

This review is independent of the *authorship of that fragment*. It is
not an independent review of the whole candidate theorem, since I
authored the base-cost input and contributed the direct-sum calculation.
The full population passage and the final source still require their
own review and validation.
