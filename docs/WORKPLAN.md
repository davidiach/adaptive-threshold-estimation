# Verification and consolidation

This is the active completion ledger for the follow-up authorized on 27 October
2026. The starting published commit is `b3f88e6bc02b3d59ec9fe99529688e2bd911e1db`.
It preserves the full requested scope; a partial formalization does not complete
this plan. New work is published on `research/verification-consolidation-20261027`.

| Work | Completion evidence | Current state |
|---|---|---|
| Adversarial audit of the critical quadratic theorem | Trace every proof dependency, record objections and their resolution, distinguish paper arguments from kernel checks | Initial source audit in [CRITICAL_AUDIT.md](CRITICAL_AUDIT.md); further verification in progress |
| Specialist review package | Short overview, complete consolidated proof, precise questions, source and prior-art references | [Prepared](../paper/critical-review/README.md): three-page brief plus complete proof, 16-page PDF compiled and visually checked; external review itself remains pending |
| Formal critical argument | Exact statistical specification, proved dependency chain, kernel and axiom audit; scalar lemmas alone do not satisfy this item | Entropy packing, abstract common-point quantifier interchange, and seeded Bernoulli prefix information/event transfer proved; full stopping-window/sign-test argument, statistical common-pair realization, and base-cost theorem pending |
| Original distribution-blind upper bound | One budget-indexed observable algorithm independent of the magnitude/sign laws, realized in the original experiment; uniform work and RMS bounds; exact type and axiom audit | Pending; existing classifier and negative-binomial identities are ingredients |
| Consolidated v5 manuscript | Original minimax law, unbiasedness, 713 bound, rare-event regimes, critical result and correction to the Psi conjecture; accurate verification labels; compiled and visually checked | Pending |
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
