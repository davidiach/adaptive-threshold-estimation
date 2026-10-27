# Independent mathematical and implementation review

Reviewer: the separately tasked audit agent. Reviewed claims authored by the
population-upper and population-lower agents, and the parent's finite-prior
experiment. This is independent agent review, not human peer review or Lean
formalization. The clipping note was authored by this reviewer and separately
checked by the population-upper agent; that distinction is material.

Baseline HEAD during review and arithmetic replay:
`d75c775633df545b892e69fc876930d6d2dcc329`. Existing unrelated Tier5 sources,
`nonlinear-critical/`, and other untracked research were preserved. The
inherited additive extension was read, not re-proved or re-formalized here.
Its source hash is recorded in `LV_AND_PILOT.md`.

## Accepted scoped paper statements

| Statement | Independent review result | Boundary |
|---|---|---|
| Quadratic-law bounded local-depth indistinguishability | Accepted. The normalized odd Legendre polynomial divided by x has the asserted bound, cancelled moments, and nonzero target moment. | Fixed cap 2K on **every** coin, including pilot and production. |
| Unrestricted feedback depth-tail necessity | Accepted. Stopping before the first forbidden query gives a common terminal law and equal exit probabilities. | Necessary depth probability and work only; no sharp arbitrary-law minimax rate. |
| Strict cap-two feedback minimax improvement | Accepted. The positive-history domination argument covers the stated independent acquisition designs and arbitrary terminal nonlinear estimators. | Deterministic total cap two and the displayed two-point parameter class; not expected-budget two or the whole rarity class. |
| Two-flip information comparison | Accepted for every magnitude law on (0,1/4]. | Constant allocation path q_t=t. The small-rho Bayes advantage is order rho^4 with fixed mu, not a growing rate advantage. |

For the bounded-depth theorem, direct substitution gives

`(1-x^2)u''+(2/x-4x)u'+2K(2K+3)u=0`.

The derivative of `u^2+(1-x^2)u'^2/[2K(2K+3)]` is
`(6x-4/x)u'^2/[2K(2K+3)]`. It decreases and then increases, so its maximum
is at an endpoint. The endpoints are 1 and `1/P'_(2K+1)(0)^2 <= 1`.
Rodrigues integration by parts proves exactly the needed K odd-moment
cancellations. The target gap is `Delta_K=rho/[(K+1)(2K+1)]`.

Local word probabilities agree through depth 2K. Conditional on all
independent algorithm randomness, any finite global transcript likelihood
factorizes over the different coins' local words, including adaptively
interleaved acquisition. Its scheduling indicator is parameter independent.
Thus prefix laws agree. Almost-sure termination under both hypotheses and
measurable output justify the terminal limit. The proof includes infinite
second moments in the final nonnegative risk inequality.

The depth-tail extension preserves that argument by stopping **before** the
first local query numbered 2K+1. The no-exit output law is a common
subprobability measure of mass 1-p. Its sum of squared errors is at least
`(1-p)Delta_K^2/2`. Therefore RMS at most epsilon under both laws implies
`p >= 1-4 epsilon^2/Delta_K^2`, and each expected work is at least `(2K+1)p`.
Later unrestricted transcript laws need not agree. The source makes this
distinction explicitly. A shallow pilot followed by deeper production is
not ruled out by the bounded-depth theorem.

For the cap-two separation, after fixing the independent seed, either one
local policy can take two flips (forcing every other policy to take zero),
or at most two policies can take one each. Strict positivity of finite word
probabilities makes this classification common to both hypotheses. It gives
domination by a seed-dependent mixture of the full same-coin and two-fresh
experiments. Nonlinear postprocessing cannot beat their Bayes risks under
the pinned prior. The feedback policy's maximum risk is strictly below both
Bayes lower bounds. All displayed strict comparisons were replayed with
exact fractions, including the other two separated-gap examples.

For the information comparison, independently checked
`c p_T-p_H h=m-m^2-v >= m/2 > 0` and
`p_T z-c p_H=m+m^2+v > 0`. The chain-rule score calculation yields the
conditional information expressions. At quadratic a=1/4 the exact values
are `I_A=97/66`, `I_O=576/473`, `I_N=1`. The stated Bayes expansion follows
by expanding its finite positive-denominator identity; normalization cancels
the first derivative and the sum of second derivatives. No LAN or
unrestricted lower bound is being inferred.

## Clipping and pilot claims constructed during this review

`CLIPPING_BOUNDARY.tex` proves that an unbiased raw output with variance
sigma^2 and fourth moment at most K sigma^4 has clipped MSE at least
`min(sigma^2,rho^2)/(256K^2)`, including parameter endpoints. Uniform K
therefore transfers the inherited unbiased additive lower bound through
clipping with an explicit loss. The fourth-moment premise is additional and
has not been established for the randomized telescopes.

The separate upper-agent review checked the Hölder interpolation, one-sided
Paley--Zygmund step, endpoint geometry, constant, supremum transfer, and seed
noise accounting. Finite arithmetic checks are supplementary, not the proof.
Independent rare mean-zero seed noise can increase raw variance arbitrarily
at unchanged observation cost while adding at most epsilon rho^2 to clipped
risk. To make that risk small, the base estimator must itself be accurate at
its actual charged budget. This demonstrates why a variance lower bound for
a particular raw candidate cannot be transferred to clipping without a tail
condition; it does not defeat the additive minimax theorem.

`LV_AND_PILOT.md` records the primary-source comparison and the exact
conditional bias identity

`bias_H(q)=integral (q-qhat_H)(g_H-1) dmu`.

Its consequence is a concrete unresolved pilot obligation: finite-word
likelihood fit must control this response-weighted residual, including any
large terminal coefficients. Independent pilot/production data do not
remove conditional bias. The suggested robust confidence-set design is a
research route, not a completed upper bound. Concurrent JN transcript work
is not treated as an accepted proof dependency in this review.

## Frozen implementation and accounting review

`feedback_experiment.py` was read completely. The policy receives known mu,
rho and a `flip(identity)` callback. Actual q, D and S are used by the
reservoir to generate bits and are not supplied to the policy. The finite
prior is a fixed design choice. Conditional on one prior hypothesis, other
coins are independent, so each existing coin's head/tail likelihood correctly
determines its next-bit predictive probability. The global posterior update
is valid under that finite prior with adaptive scheduling. The action value
`Cov(theta,p)^2/[pbar(1-pbar)]` is exactly one-step posterior variance reduction,
not a globally optimal adaptive strategy or an arbitrary-q guarantee.

All 7,680 stored rows and their 240 cells were independently inspected:
32 replicates per cell, 3,440,640 genuine charged flips in total, row work
equal to the configured budget, output and ground-truth bounds correct,
fresh/block depths correct, and the deliberately unseen profile outside
each finite prior support. The original frozen source, contract, lock and
raw-data hashes agree. No benchmark was rerun by this reviewer.

The frozen wording about zero calibration expense and all policy wall time
needed the separately saved accounting clarification. Zero extra statistical
observations does not mean zero computation. Model construction contains
known-law bisection; total run timing includes it, whereas per-row timing
excludes it and shares a warmed predictive cache. Those row timings cannot
support a one-shot speedup or break-even claim. The clarification preserves
the locked method and data. No confidence procedure was supplied, and the
small numerical suite does not establish uniform or stable superiority.

## Reviewed source versions and evidence

The first upper proof reviewed had SHA-256
`a3643bcfae634178239559237511638411228771d08e0779f1c1ccf0c06b1916`.
Its evidence remains in `replay.json`. The final expanded depth-tail proof
has SHA-256
`72df0ee46660c1a72b9c15271f29867dce1760ccaf6253bd43327964373b26f1`.
`replay_final.json` records matching before/after hashes for all final
reviewed proof and checker files, with fresh exact arithmetic results.
It is a later checkpoint, not a retroactive replacement of the first one.

The final lower feedback proof is
`205058563b01463089ef2cc8359d7424a77c54da13c4850f01b69a58da1a5fab`,
and its local information note is
`36060a9fb39f8c7cdd7cfaaf6dd652cfb5d633d45a8ade27c6961a227b85dd12`.
The final clipping note is
`0bfe2de3d20346c5536834eb574cd206a368839a918340a6eb6824a51559415b`.
`experiment_audit.json` independently pins the frozen numerical inputs and
records its checks; `experiment_audit_final.json` repeats those checks and
also pins the saved audit checker. `RUN_LOG.md` supplies actual commands and limitations.

No new Lean declaration or build was supplied in this pass. No novelty,
priority, external review, unrestricted minimax resolution, or future
background continuation is claimed.
