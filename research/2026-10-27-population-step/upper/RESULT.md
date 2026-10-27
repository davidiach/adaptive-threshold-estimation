# A verified restriction on pilot learning, and an exact two-gap estimator

Status: **PROVED-ON-PAPER**; exact-arithmetic finite checks accompany the proof.
No Lean declaration, external review, or novelty claim is supplied. The full
unrestricted population minimax problem remains unresolved.

## Result

One plausible population strategy is to learn unknown sign allocation from
independent pilot coins and use it to select a control-variate coefficient for
production coins. For a fixed unbiased production feature and a scalar
zero-mean feature with parameter-independent positive variance, this strategy
cannot improve worst-case squared error over the best fixed coefficient. This
holds for an arbitrary pilot algorithm and coefficient, even a hypothetical
oracle coefficient that knows the unknown allocation.

Precisely, let Q be the compact convex global-rarity polytope for a fixed finite
gap law. Let fixed per-coin features Y and Z satisfy

* E_q Y = theta(q), and E_q Z = 0 for every q in Q;
* E_q Z^2 = v > 0, independent of q;
* all second moments are finite (and hence continuous in the finite mixture).

Write f(q,b) = Var_q(Y-bZ). There exist q_* and b_* such that

    f(q_*,b) >= f(q_*,b_*) = max_q f(q,b_*) =: F_*  for every real b.

Consequently, the raw average of n independent production features, corrected
by any independent pilot coefficient, has worst-case MSE at least F_*/n. The
fixed coefficient b_* attains F_*/n without a pilot. The proof explicitly
establishes coercivity for unrestricted real coefficients. It does not assume
that a minimum over an unbounded coefficient domain is attained.

This is a restricted impossibility result. It does **not** cover clipping,
biased features, pilot-dependent acquisition, changing the number of
production coins using production outcomes, or nonlinear aggregation.

## A nonvacuous hidden-gap example

For two known gaps 0 < d1 < d2 <= 1/2 with positive known masses, take three
flips from each coin. Put x_i=2d_i and R_j=2X_j-1, and define

    A = (R1+R2+R3)/3,
    B = R1 R2 R3,
    C = (R1R2+R1R3+R2R3)/3,
    a = (x1^2+x1*x2+x2^2)/(2*x1*x2*(x1+x2)),
    b = -1/(2*x1*x2*(x1+x2)),
    Y = 1/2 + a*A + b*B,
    Z = C - E[x_D^2].

Y is exactly unbiased for theta for every sign allocation; Z has mean zero
for every allocation. Their computation uses only observed flips and the
known law, never the sampled gap. With m2=E[x_D^2],

    Var(Z) = (1-m2)*(m2+1/3) > 0.

An explicit pilot implementation estimates the optimal coefficient from m
independent pilot triples, then uses n independent production triples. If
c=E_q[YZ] and k=Var_q(Y), its exact raw MSE is

    (k - c^2/v + Var_q(YZ)/(m*v))/n.

Total work is deterministically 3(m+n) flips. This is an implementable
multicoin unbiased estimator, but the theorem proves that the pilot cannot
improve worst-case MSE over the fixed-coefficient counterpart with the same
production sample count. At the same total work, the fixed procedure may use
m+n production coins. The interpolation coefficients can be very large for
small gaps: this construction is not a rarity-optimal estimator.

## Reproduction and scope

Run from the repository root:

    python research/2026-10-27-population-step/upper/check_exact.py

The script uses Python `fractions.Fraction` only, enumerates all eight
three-flip transcripts, and verifies the displayed moments and the finite
pilot/production MSE identity at rational parameter settings. It checks
theta=0, the global-rarity boundary, an endpoint gap d2=1/2, and strongly
separated gaps. Its output is `exact_checks.json`. These are exact rational
identity checks, not an unrestricted minimax certificate or a Monte Carlo
benchmark.

The written proof is in `proof.tex`. This work rules out a particular
population escape from the single-coin obstruction. Acquisition adaptation
and nonlinear population estimation still require a separate argument.

## Prior-art position

The control-variate estimator is a standard construction; the saddle argument
is an elementary convexity argument. No priority or novelty assertion is made.
The exact hidden-gap specialization and the restricted negative result are
documented here to expose a failed route, not presented as a resolution of the
rare-event conjecture.
