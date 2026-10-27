# Second independent review checkpoint

This is an additive review record. `REVIEW.md`, `replay_final.json`, and the
earlier source snapshots remain unchanged. The new mathematical sources
were constructed by the separate lower and upper agents. Their review here
is independent agent review, not external peer review, Lean formalization,
or a priority judgment.

The shared repository HEAD at the fresh replay was
`7311b6da2620924dad79bdfd795a87465746f67e`; the first audit checkpoint had
HEAD `d75c775633df545b892e69fc876930d6d2dcc329`. The new replay confirms
every source hash from the first final arithmetic checkpoint is unchanged.
This agent did not change Git history or other agents' sources.

## Full-class deterministic-cap feedback separation: accepted

Reviewed `lower/full_class.tex` at SHA-256
`bff3e1e5ead021b4f8b36e84b2b5eea504e62a22f245f0a4f96a82d1e483329e`.
For the fixed known law `mu=(delta_(1/4)+delta_(1/8))/2`, rho=1/4, this
extends the earlier two-profile result to **all** feasible global-rarity
allocations. The class is exactly the triangle `q1,q2>=0, q1+q2<=1/2`.

The independent symbolic checks give

`theta=(q1+q2)/2`, `A=q1/8+q2/16`,
`4A<=theta<=min(8A,1/4)`.

Each two-flip likelihood depends only on A. For any fixed output table, the
feedback risk has second derivative two in theta. Thus its maximum lies on
one of the three triangle edges. On a diagonal edge its degree in A is at
most three: the apparent fourth-degree term cancels because probabilities
sum to one. On the horizontal edge it has degree at most two. The exact
second derivatives exceed 30, 124, and 3/100, respectively, at both endpoints.
Their affinity therefore proves convexity on each full edge, and the global
maximum is a vertex. This is a continuum proof using exact polynomial
coefficients; the rational grid check is only a supplementary diagnostic.

The literal rational output table is used unchanged over the whole class.
It has worst-case MSE strictly below `15443/1000000`. A prior supported on
the null and `(q1,q2)=(0,1/2)` lower-bounds every noninteractive comparison
procedure by strictly more than `15475/1000000`. The previously reviewed
cap-two domination argument still applies because the null has positive
probability for every finite local history. Its Bayes bound permits all
terminal nonlinear estimates and all stated shared-seed independent local
acquisition policies. The minimax MSE separation is therefore greater than
`32/1000000` over the **full** rarity class for this law.

The deterministic total cap of two is essential to this comparison. A
policy with only expected budget two may sometimes spend more, so it is
outside the domination argument. No growing advantage or critical-law rate
separation follows from this certificate.

`replay_v2.py` independently integrates the latent mixture at 153 feasible
rational points; reconstructs all three edge polynomials using exact
Vandermonde elimination, independent of the author's polynomial arithmetic;
checks the literal output table; and recomputes the two Bayes risks from
posterior losses. It also re-executes the author's complete certificate and
compares its output with the stored JSON. All checks passed.

## Arbitrary-law finite approximation: accepted on paper

Reviewed `upper/FINITE_APPROXIMATION.tex` at SHA-256
`b01ca6fee968feb6b82121be9b762a1748dd64bd7d19c26323bbe6c6d6e3109e`.
Let V_mu(B) denote unrestricted minimax MSE with the original uniform
expected flip budget B>0. Let G be the fully adaptive finite experiment
having total cap N, magnitude mesh eta, downward allocation grid gamma,
and the same expected budget B over its finite parameter set. With

`C=N^2(eta+gamma)`, `E=rho^2 N(eta+gamma)+2rho gamma`,

the accepted error bound is

`|V_mu(B)-G| <= rho^2 B/N + E + rho^2 C/[4(B+C)]`.

The proof correctly includes the following necessary steps.

1. Clip all outputs to the known interval [0,rho], without increasing risk
   or changing work. Stop an expected-budget algorithm at N total flips;
   Markov's bound gives the displayed uniform truncation error.
2. Couple original and rounded fresh coins by retaining the sign and
   replacing D by its representative. Averaging q within each bin preserves
   its target and global rarity exactly. The pointwise probability difference
   is at most eta even after past observations, so arbitrary feedback does
   not invalidate the coupling. Transcript TV is at most N eta; expected
   work error is N^2 eta, not N eta. Both forward averages and reverse
   bin-constant lifts are explicit.
3. Round allocation coordinates downward. This preserves global rarity and
   changes the target by at most gamma. At most N fresh coins give TV at
   most N gamma. The risk comparison includes both transcript change and
   target change; its latter term is 2rho gamma. Work slack is N^2 gamma.
4. An independent activation probability B/(B+C), with midpoint output on
   nonactivation, restores the exact original expected budget. Its risk
   penalty is retained explicitly. Both minimax inequalities are proved;
   the reverse direction needs only magnitude rounding because the finite
   grid is a subclass.

These arguments apply to arbitrary probability measures, including atoms,
mixtures, singular laws, deterministic endpoint masses and infinite inverse
moments. They do not require any regular-variation approximation. Taking
N to infinity with eta=gamma=N^(-3) gives convergence for each fixed
mu,rho,B>0. Policies and their deterministic caps vary with N; the uniform
expected budget remains B through the explicit activation step. This is
an MSE approximation result, not a confidence-radius theorem.

The exact finite convex formulation also passed review. Its variables are
policy realization weights, not event probabilities. Both observation
children inherit the parent's action weight; likelihood factors carry the
chance probabilities. Terminal cost is linear in these weights, and squared
risk is a closed quadratic perspective of the scaled output and terminal
weight. The perspective is continuous on `0<=y<=rho t`, including t=0.
Compactness and a feasible constant estimate yield an attained minimum.

The formulation retains arbitrary cross-coin feedback and shared seeds.
Given the complete action/identity/bit history, the consistency condition on
the seed is parameter independent, and the observation likelihood is common
to all consistent seeds. Hence its conditional seed distribution can be
represented by parameter-independent behavioral action probabilities.
Remaining terminal randomness can be replaced by its conditional mean
simultaneously for every grid parameter. No universal independence of
adaptive transcripts is assumed.

One model-fidelity clarification was requested and applied before acceptance:
the source now uses interval bins and pairwise-distinct rounded magnitudes.
It no longer permits separate hidden types at identical rounded D with
different q-values. Such types could be aggregated observably, but retaining
them would unnecessarily complicate the original requirement that q be a
function of D. The final source has no such ambiguity.

The computational caveat is explicit and necessary. Arbitrary mu is not
automatically a computable object. The theorem grants exact bin masses and
real arithmetic on resulting finite coefficients; a certified executable
solve needs exact coefficients or separately bounded coefficient errors.
Neither this reviewer nor the construction agent solved the finite convex
program. The theorem supplies controlled approximation, not an efficient
algorithm or the unresolved minimax rate.

## Reproducible evidence and remaining gaps

`replay_v2.json` records matching before/after hashes for both new proofs,
the new certificate and its JSON, this review's executable replay, and the
earlier final replay file. It additionally verifies freshness of every
earlier audited proof/checker hash. Its finite arithmetic does not formally
prove the general approximation theorem.

The strongest new accepted claim in this extra pass is the full-rarity-class
feedback separation. The finite approximation theorem supplies a rigorous
way to relate future finite solves to the original expected-budget problem,
but its error budget must actually be applied. No arbitrary-law rare-event
minimax formula has been proved or disproved by this additional pass.
