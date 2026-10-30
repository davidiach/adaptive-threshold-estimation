# Confidence transfer and valid sequential stopping

This draft is stacked on the hard-budget RMS PR (#31) to reuse its observation
accounting. The RMS theorem has no dependency on this PR. Round-one integration
remains in #30 and is not duplicated here.

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
comparison and is not necessary for the core transfer.

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

These are finite checks, not proofs of the universal claims. A full clone was
unavailable; full upstream tests and CI are checked separately at the uploaded
commit. No new Lean build or independent specialist review is claimed.

## Reproduce from the repository root

```sh
PYTHONPATH=toolkit python -m unittest discover -s toolkit/tests -p 'test_confidence*.py' -v
python research/2026-10-30-confidence-transfer/verify_transfer.py --output .runtime/confidence-transfer/transfer.json
python research/2026-10-30-confidence-transfer/verify_anytime.py
```

The workflow repeats these on Python 3.10 and 3.12. Replays write only under
`.runtime/`, not over supplied evidence. Existing full-toolkit CI still applies.

## Review gates

Keep this draft until the exact-model review checks: a common pair for all
caps and policies; coinwise rather than whole-population smoothing; the
adaptive likelihood factorization; typed conditional independence; charging
the correct reference work; the unbounded-stop limit with a fixed pair; and
the retained annular saturation constraints in the general-law application.
Check the strict-budget median construction separately from the lower bound.
No headline result is promoted into the root results table by this draft.

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
manuscript or published evidence is modified.

Original archive SHA-256 values:
- Round two: `b2fdd832626b2b40044066d8ae9ee593a019b6bc0a2b9cde2a1f7e33dfb1b332`.
- Round three: `1ffd571e2a5cd5ff10f681624cc00fbe535e7723ce65a1390d0b066563823e9f`.

No literature-wide novelty claim is made. The source note cites the relevant
Lee-Valiant and convex-estimation antecedents; the anytime note distinguishes
standard confidence-sequence methodology from this application.
