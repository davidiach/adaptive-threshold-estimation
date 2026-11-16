# Arbitrary-law manuscript and evidence publication

This record reconciles the complete arbitrary-law theorem, the v6 manuscript
and the completion tracker. It preserves the distinction between the formal
mathematical construction and the separately tested Python toolkit.

## The checked result

For known `0 < rho, delta <= 1/4`, one observable controller, independent of
the unknown positive-gap law, has unconditional physical caps and consistent
prefixes. Its nested intervals cover at every integer budget on one event
of probability at least `1-delta`; on the same event their half-width is at
most `2^32 C_* K_mu,rho(B/Lambda)` after a deterministic finite onset, uniform
over measurable sign laws with positive mass at most `rho`. The same event
protects observation-dependent stopping budgets. No candidate family, moment
or tail regularity, or integration oracle for the unknown law is supplied.

The formal continuation uses exactly the pilot repetition count for its
capped copies. It selects its reference estimator classically and evaluates
the reference functional exactly. These choices and the scope of every
component are in the [formalization guide](../../docs/ARBITRARY_LAW_FORMALIZATION.md).

## Source and proof evidence

- [#114](https://github.com/davidiach/adaptive-threshold-estimation/pull/114)
  merged at `39e3587b5a8f4d9466df7762f455ff587a40202e`. Its head
  `0fbe4b78731acce7d5de426d90a75046cdc33e34` passed all fourteen CI checks
  and completed automated review with no findings.
- The [controller record](../arbitrary-law-controller-20261116/README.md)
  identifies proof checkpoint `3f07e30a9a74a3b2b28c24ff5d017d3d60e093b1`,
  the 99 independent exact statements and transitive reports, all twelve
  kernel replays, and the 730-module proof closure.
- The [whole-project CI audit](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/43900918376/job/133416957807)
  at the PR head verified 12,993 constants (10,509 theorems) in 1,213 modules,
  125 exported instances including six registered orphans, all 2,373 locked
  definitions, and 204 main-theorem kernel replays. Only `propext`,
  `Classical.choice` and `Quot.sound` occurred.
- The [adaptation CI audit](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/43900918376/job/133416958510)
  passed the component sequence and the final 99-statement audit, followed
  by independent kernel replay of the twelve controller modules.

The publication changes no Lean source, proof audit or definition lock.
The [machine-readable reconciliation](reconciliation.json) and
[proof-source manifest](proof-source-manifest.json) bind manuscript checkpoint
`ab67c39108931528d52acd42856e33343dbb2e31` to this reused evidence.
The [proof CI snapshot](proof-ci.json), [two manuscript runs](manuscript-ci.json)
and their [first](manuscript-build-1.log) and [second](manuscript-build-2.log)
TeX logs preserve the run identities and build outputs.
The [new PDF](../../paper/v6/builds/arbitrary-law-complete-20261116.pdf) and
[build record](../../paper/v6/builds/arbitrary-law-complete-20261116.json) identify the exact bytes,
source hashes, reproducibility and visual checks. CI on the final
publication head is recorded separately in its PR and the completion tracker;
the earlier successful run is not a claim about a later commit.

## Status reconciliation

The [single status source](../../paper/v6/status.json) tracks 31 results:
30 Lean-checked and one paper-proof entry. The following entries include the
extensions named in publication issue #84; component counts are not extra
claims added to the 31-result total.

| Status entry or component family | Evidence and exact boundary |
|---|---|
| Finite-family adaptation | [17 component statements](../law-adaptation-20261105/README.md) and [22 observable-construction statements](../law-adaptation-realization-20261105/README.md), including the paid pilot and selected controller |
| Arbitrary-law adaptation | Thirty-three audits, 1,065 exact statements and 1,063 transitive reports; [full component map](../../docs/ARBITRARY_LAW_FORMALIZATION.md), ending in the concrete all-budget theorem |
| Stochastic envelope | [RMS, confidence and unbiased scope](../stochastic-envelope-20261105/README.md) under the stated envelope |
| Localization transfers | [Common-pair](../common-pair-20261105/README.md), [fractional-submeasure](../additive-confidence-20261105/README.md) and [RMS](../rms-localization-20261105/README.md) results retain the single-coin obstruction premise |
| Finite-menu construction | [14 cost-grouping statements](../band-cost-formal-20261105/README.md) and [13 finite-law menu statements](../gap-law-menus-20261105/README.md); Python optimization is not certified |
| Remaining v6 §14.8 entry | Paper proofs for the closed form, distance from the rate and uniform power-margin claims; the separately tracked Psi lower bound is already [Lean-checked](../psi-selection-20261109/README.md) |

The abstract, introduction and status table are generated by
`tools/build_v6.py`; the README summary and results table are generated by
`tools/build_status_docs.py`. The final build is linked from the
[manuscript index](../../paper/v6/README.md#all-budget-controller-build).
Historical reports and published PDFs retain their original status.

## Completion and remaining boundaries

The pilot chain #77–#80 and the concrete continuation and controller needed
by #81–#83 are complete. No physical zero-gap coin is needed: the proof charges
unresolved mass and uses a positive-part reference split. This does not assert
the unused fair-coin experiment requested in the original #81 checklist.

The [tracker](https://github.com/davidiach/adaptive-threshold-estimation/issues/76)
keeps numerical/toolkit specification and stochastic Python/PRNG refinement
(#85–#86), secondary paper claims (#89), the assembled finite-law approximation
theorem (#93), and the remaining §14.8 formalization (#100) separate from the
completed core theorem. The simpler [unknown-law confidence sequence](../../docs/UNKNOWN_LAW_CONFIDENCE.md)
retains its own paper-proof status. Exact-selection complexity (#87) and sharp
finite-cap convergence (#88) remain open research; proof/audit refactoring
(#90–#91) remains optional maintenance. Practical superiority and external
specialist review are not established.
