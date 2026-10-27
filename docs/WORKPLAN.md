# Verification and consolidation

This is the active completion ledger for the follow-up authorized on 27 October
2026. The starting published commit is `b3f88e6bc02b3d59ec9fe99529688e2bd911e1db`.
It preserves the full requested scope; a partial formalization does not complete
this plan. New work is published on `research/verification-consolidation-20261027`.

| Work | Completion evidence | Current state |
|---|---|---|
| Adversarial audit of the critical quadratic theorem | Trace every proof dependency, record objections and their resolution, distinguish paper arguments from kernel checks | Initial source audit in [CRITICAL_AUDIT.md](CRITICAL_AUDIT.md); further verification in progress |
| Specialist review package | Short overview, complete consolidated proof, precise questions, source and prior-art references | [Prepared](../paper/critical-review/README.md): three-page brief plus complete proof, 16-page PDF compiled and visually checked; external review itself remains pending |
| Formal critical argument | Exact statistical specification, proved dependency chain, kernel and axiom audit; scalar lemmas alone do not satisfy this item | Critical single-coin variance and raw-moment base-cost theorems proved for every rarity. Capped finite-observation reduction now proves full seed/transcript reconstruction and preservation of canonical affinity and expected work. Abstract common-point theorem also proved. Statistical compactness, convex risk comparison, common-pair instantiation, unrestricted population transfer and the critical upper construction remain pending |
| Original distribution-blind upper bound | One budget-indexed observable algorithm independent of the magnitude/sign laws, realized in the original experiment; uniform work and RMS bounds; exact type and axiom audit | Pending; existing classifier and negative-binomial identities are ingredients |
| Consolidated v5 manuscript | Original minimax law, unbiasedness, 713 bound, rare-event regimes, critical result and correction to the Psi conjecture; accurate verification labels; compiled and visually checked | [Written](../paper/v5/README.md): 56-page manuscript with complete source-derived proof appendices, explicit editorial changes, source checks, and rendered-page review. No separate review of the new consolidation is claimed |
| Process note | Reproducible account of construction, frozen statements, semantic review, failed approaches, reviewer dependence, and limits | [Written](process/METHOD.md); update verification boundaries as further work lands |
| Repository cleanup and publication | Clear current entry points, preserved source/evidence identities, passing relevant guards and CI, pushed commits and reviewable changes | First checkpoint pushed in [draft PR #3](https://github.com/davidiach/adaptive-threshold-estimation/pull/3); baseline CI confirmed; current verification status must be checked per commit |

## Working rules

* Preserve the existing frozen sources, imported manuscripts and historical
  evidence. Corrections should be conspicuous and must not silently rewrite
  what an earlier audit actually checked.
* Keep current mathematical explanations separate from chronological evidence.
  Reuse this ledger and the audit document rather than producing another package
  for every intermediate attempt.
* Record a failed proof or counterexample before changing course. If a claim
  fails, repair or qualify all current summaries that depend on it.
* A proved implication with a statistical hypothesis is not a proof of that
  hypothesis. Expose pending realization and probability steps explicitly.
* Push checked checkpoints. Do not label a run successful until its actual jobs
  have completed on the corresponding commit.

## Baseline verification

GitHub Actions [run 40488398325](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/40488398325)
completed successfully on the starting main commit. This resolves the reviewers'
earlier observation that its run was still in progress. The new audit does not
turn those regression checks into verification of the critical paper theorem.

The original working tree contains pre-existing untracked research files. Work
here uses a separate Git worktree, leaving that material intact. No history
rewrite is planned to remove wording from old commit messages.

The published probability checkpoint `8e0124f9c2691163f015ceda93d5f01b29604def`
also passed all three Linux jobs in
[run 40494565796](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/40494565796),
including its four scoped critical targets and the existing complete Lean
audits.

The finite-gap extension and updated specialist packet, published at
`071b650d928ba3fd35ff737ab2a455e8225f17e6`, passed all three jobs in
[run 40497825571](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/40497825571),
including the five exact critical targets and all 63 declaration checks.
The later v5 consolidation has separate source, compilation, link, and visual
checks. Its numerical and research jobs passed in
[run 40499796986](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/40499796986),
while the Lean job was cancelled after the subsequent push; that run is not
recorded as a full CI pass. The stopped-suffix checkpoint
`0bbd0ee7164b3b15aa2bda68466e5c0e25a6480f` passed all three jobs in
[run 40501696138](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/40501696138),
including all six exact targets and 84 declaration checks.

The fixed-count restart checkpoint `af25e8827254f8ce9050cca409c7294ede0c64b8`
passed all three jobs in
[run 40504616018](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/40504616018),
including its eight exact targets and 117 declaration checks. The subsequent
sign-test and estimator-entropy checkpoint `65131e6e782afebc6c320ca2b1b0010f4afb2a0d`
also passed all three jobs in
[run 40506853150](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/40506853150),
including its ten exact targets and 135 declaration checks. The population
moment checkpoint `145a78519b58e84a01314da356b380882b644c5b` passed all three jobs in
[run 40510054032](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/40510054032),
including twelve exact targets and 189 declaration checks. The good-gap
checkpoint `13435c1464e449bfc76225ac3d2544e9699e7e4f` passed all three jobs in
[run 40513347586](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/40513347586).
The finite-scale checkpoint `891d5dc4e74d849cc93b100fbf99a28da112ccc3` also
passed all three jobs in
[run 40516081123](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/40516081123),
including seventeen exact targets and 251 declaration checks. Later extensions
require their own CI results. The published base-cost and manuscript correction
checkpoint `5ba7166a6975e1d874e9166d9dbe015b90a5cbc5` passed all three jobs in
[run 40520815549](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/40520815549),
including all twenty exact critical targets and 290 declaration checks.
