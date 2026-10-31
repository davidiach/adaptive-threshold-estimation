# Confidence transfer and valid sequential stopping

This package reuses the observation accounting of the
[hard-budget RMS package](../2026-10-30-hard-budget-rms/README.md), which does
not depend on it. The
[certified-selection package](../2026-10-30-certified-selection/README.md) is
not duplicated here. The [results guide](../../docs/RESULTS.md#confidence-rates-and-sequential-stopping)
summarizes the claims and their status.

## Read in this order

1. [Original round-two paper proof](NOTE.md).
2. [Claim dependencies](CLAIMS.json) and [adversarial review targets](ADVERSARIAL_NOTES.md).
3. [Round-three anytime application](ANYTIME.md).
4. The drivers `confidence_amplification.py` and `confidence_ladders.py` in
   `toolkit/threshold_toolkit/`, and their corresponding tests.

## Exact scope

The proposed fixed-confidence characterization is
`r_exp(B,delta) ~ r_hard(B,delta) ~ K(B/log(1/delta))` for known positive-gap
law and known global rarity. It is a **paper-proof extension**, not Lean-checked.
The arbitrary-law application imports the paper-only common-pair, null-work
and entropy-packing arguments. The critical corollary has a shorter dependency
path. These inherited ingredients have not been independently re-proved by
this integration. The optional Q corollary additionally needs round one's
comparison and is not necessary for the core transfer. Some inherited inputs
have since been Lean-checked; see the [integration review](#integration-review).

The anytime result is a simultaneous-coverage construction and a conditional
upper-width bound, **not a matching anytime minimax theorem**. It does not
supply unknown-law confidence intervals. Empty intersections remain empty;
timeouts preserve coverage but do not promise shrinking width.

Neither driver implements the optimal general-law base estimator or validates
its statistical premises. Both cap observations, not callback CPU time.
The fresh-Bernoulli interval is not valid for pooling repeated flips of
heterogeneous hidden coins. PRNG and Python correctness are not formalized.

## Local integration validation

Python 3.13.5, additive checkout only:
- 29 original median-driver tests and 16 extracted confidence-ladder tests pass.
- Including #31's 24 tests, all 69 additive tests pass together.
- Exact transfer audit: 202 categorical pairs, 404 directed smoothing bounds,
  48 adaptive populations, 216 hybrids, 1,198 exact leaf identities and
  216 null-work domination checks pass.
- The anytime audit checks 501 telescoping identities and exact integer path
  counting of the optional-stopping counterexample (horizon 512).

These are finite checks, not proofs of the universal claims. No new Lean
build or independent specialist review is claimed. GitHub CI passed on the
extraction commit `144f58a`, including the then-separate workflow's audits on
Python 3.10 and 3.12.

## Reproduce from the repository root

```sh
python -m unittest discover -s toolkit/tests -p 'test_confidence*.py' -v
python research/2026-10-30-confidence-transfer/verify_transfer.py --output .runtime/confidence-transfer/transfer.json
python research/2026-10-30-confidence-transfer/verify_anytime.py
```

In CI, the toolkit workflow runs the unit tests with the rest of the toolkit
suite on Python 3.10 and 3.12, and the `research-evidence` job of
`checks.yml` runs both audits on Python 3.12. Replays write only under
`.runtime/`; the package has no tracked evidence records.

## Integration review

The draft asked for an exact-model review of seven points, plus a separate
check of the median construction. On 31 October 2026 an AI review (Claude
Code), not a specialist review, checked each against NOTE.md, and the
sequential construction against ANYTIME.md, and found no error:

- **One common pair.** Theorem 3 uses the pair of v6 `thm:bias-transfer` as
  stated: one pair for every capped local policy and cap, fixed before the
  population algorithm, the cap passage and the confidence level.
- **Coinwise smoothing.** Only the one-coin transcript law is treated as
  affine in the prior. The two-coin example shows correctly that the
  population law is not.
- **Adaptive factorization.** Under a fixed seed, (5) writes each leaf
  probability as a product of per-coin word probabilities. The hybrid
  identity (6) is therefore exact, and each slot ratio lies in $[1/3,3]$.
- **Typed conditional independence.** A coin's type is fixed before its first
  flip, and (7) is applied conditionally on the prehistory.
- **Reference work.** Bound (7) applies null domination (1) to the one genuine
  coin, with the other coins held at the smoothed reference prior. The local
  works sum to the population's work.
- **Unbounded stopping.** The pair is fixed before the cap grows, and overflow
  changes each error probability by at most $B/N$.
- **Annular saturation.** (18) keeps the minimum-band-mass branch. The lower
  bound reruns the deterministic assembly of v6 Appendix E at $B/\ell$. That
  assembly's statistical steps are the bias transfer applied to
  `prop:psi-null` and additive localization applied to `prop:scaled-annular`.
  (17) and Theorem 4 replace them with the same coefficients, $1/8192$ and
  $1/128$, at budget $B/\ell$.
- **Median.** Markov's and Chebyshev's inequalities bound each block's failure
  probability by $1/4$, with no independence assumed between a run's cost and
  its error. The Chernoff step gives $(\sqrt3/2)^m\le\delta$, and $m\le10\ell$.

The review also rechecked the constants: $224s^2B/J\le7\ell/32<\ell/4\le
\operatorname{kl}(1-\delta,\delta)$, $8\cdot33000\sqrt{10}<840000$, the
telescoping sum of the stage allowances, $n_m>B/4$, $\ell_m\le\Lambda$ and
the factor $2$ in the anytime width bound. Both drivers implement the
constructions as described, and their tests and audits pass.

Since this package was written, three of its inputs have Lean-checked
counterparts in `main`:
- **General-law upper bound.** The RMS upper bound used for Theorem 6, the
  paper's $R\le33000\,\mathcal K$, is Lean-checked as
  $R\le28000\,\mathcal K$. The upper half of Theorem 6 therefore inherits no
  paper-only result; the median amplification and the scaling (15) remain
  paper proofs.
- **Critical common pair.**
  [CriticalCommonPair.lean](../../lean/ThresholdHC/CriticalEntropy/CriticalCommonPair.lean)
  proves premise (3) directly for the critical law. The critical corollary (21)
  can use it in place of the paper-only bias transfer, so both of its
  inherited inputs are Lean-checked. The new transfer and amplification steps
  are still paper proofs.
- **Closed-quantile comparison.** The Q corollary can use the Lean-checked
  $\mathcal K\le Q\le(1+2\sqrt2)\mathcal K$ instead of round one's paper-only
  $8/5$.

The lower half of Theorem 6 still inherits the paper-only common-pair theorem,
both null-work obstructions and the entropy packing. The power-law statement
(22) follows from (20) once $\mathcal K$ is evaluated for the power law; the
note does not write that evaluation out.

## Provenance and extraction changes

Prepared by ChatGPT at David Iach's request. Integration starts from main
`2bc506d62387c511bac8fecbd07ec0e4026b10ce` via #31.
`NOTE.md`, `CLAIMS.json`, `ADVERSARIAL_NOTES.md`, `verify_transfer.py`, the
median driver and its tests are preserved from round two. Historical status,
counts and commands inside that note describe its original delivery; this
README is the integration entry point. It references some original package
files not republished here, including its PDF/reproduction wrapper. The full
original artifacts remain the user's delivered archive.

`ANYTIME.md` extracts the mathematical anytime portion of round three;
`confidence_ladders.py` and its tests are separated from the original combined
module. A missing `stage` import exposed by the split was repaired. The anytime
extraction restores standalone equation definitions and explicitly distinguishes
unconditional error at a stopping rule from coverage conditional on termination. The RMS
module itself is not changed by this PR. No frozen project source, historical
manuscript or published evidence is modified. On integration, the separate
workflow was folded into `checks.yml`, `test_confidence_amplification.py` gained
the two-line `sys.path` setup the other toolkit tests use, so it runs without an
installed package, and the drivers were documented in the
[toolkit guide](../../toolkit/README.md#research-modules-high-confidence-and-sequential-stopping).

Original archive SHA-256 values:
- Round two: `b2fdd832626b2b40044066d8ae9ee593a019b6bc0a2b9cde2a1f7e33dfb1b332`.
- Round three: `1ffd571e2a5cd5ff10f681624cc00fbe535e7723ce65a1390d0b066563823e9f`.

No literature-wide novelty claim is made. The source note cites the relevant
Lee-Valiant and convex-estimation antecedents; the anytime note distinguishes
standard confidence-sequence methodology from this application.
