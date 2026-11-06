# Research contract: approximate finite-law selection

Baseline: `68adbf3` (6 November 2026), isolated branch
`research/selection-fptas-20261106`. Existing worktrees and frozen sources are
preserved. This is the first application of the research workflow discussed
alongside PSI's Aaronson–Ambainis announcement.

## Target and scope

For every finite rational probability law on gaps in `(0,1/2]`, rational
`0 < rho <= 1/4`, rational `B > 0`, and rational `0 < epsilon <= 1`, construct
an actual bandwise-suffix selection whose **capped deterministic entropy-tail
objective** is between `K` and `(1+epsilon) K`. The mathematical algorithm
should run in time polynomial in binary input length and `1/epsilon`, without
a bound on the number of distinct band costs.

This is a deterministic computation of the known-law rate functional. It
does not sample coins, estimate an unknown law, or establish a new minimax
statistical theorem. The existing suffix theorem must connect the finite
menus to all fractional submeasures. Exact optimization remains a separate
open question. No novelty claim follows merely from a successful proof.

## Baseline ledger

* The suffix reduction and concrete finite-law menu connection are already
  Lean-checked; see `ThresholdHC.GapLawMenus.finite_law_solver` and
  `docs/BAND_COST_SELECTION.md`.
* Exact compression by repeated cost multisets is checked mathematically,
  but may have exponentially many states for distinct costs.
* Quantile comparison already supplies a constant-factor approximation.
  The intended improvement is arbitrarily prescribed relative accuracy.
* The existing Python arithmetic and solvers are not Lean-verified.
* These baseline claims were read at the named checkpoint; their full Lean
  audits have not been independently replayed in this session.

## Dependency graph

Existing suffix theorem -> finite menus -> rational logarithm surrogates ->
two-coordinate trimming invariant -> entropy perturbation lemma -> retained
near-optimal witness -> rational endpoint selection -> `(1+epsilon)` bound.

## Failure tests

Attack cancellation in the entropy formula, the empty selection, zero or
very small tail costs, disparate scales, band endpoints, exact bin boundaries,
near ties, tiny rarity, and accumulation of rounding over many bands. Compare
small instances against every hard subset with a separately written Decimal
evaluator. Force actual compression with many distinct, nearly equal costs.
Resource exhaustion must raise rather than return an unjustified certificate.

Fallback: if uniform perturbation control fails, retain the counterexample
and state the restricted comparison that survives. Do not relabel a restricted
or constant-factor result as the requested approximation scheme.

## Acceptance and review

Deliver a complete paper argument, executable rational-arithmetic prototype,
reproducible adversarial evidence, and explicit verification boundaries.
The new theorem is not Lean-checked unless a separate exact-type and axiom
audit is actually performed. Self-review is not an independent agent or
specialist review. Published records and manuscript claims are not upgraded
by numerical tests.
