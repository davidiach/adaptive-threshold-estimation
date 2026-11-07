# Increasing-gap coupling and selection transport: native Lean audit

Proof checkpoint: `5fb6820bb33898a2a23ce7183fb3aa9aa5e64a02`.
Base checkpoint: `cb3b011ef70123605ccc15657e63155d5a455799`, the previously published
countable-transport checkpoint of PR #75.

The [record](status.json) identifies all 57 project sources in the
dependency closure, 5 fresh serial native compilations with empty logs,
and 52 compiled dependencies matching previously published hashes.
No inherited artifact is first identified here. The pinned compiler, package
manifests, verifier sources and prior records are bound by their hashes.

The two audits independently restate 32 exact statements and check 32 transitive
axiom reports, permitting only `propext`, `Classical.choice` and `Quot.sound`:

- Coupling: [19 exact statements](arbitrary_law_coupling.lean) and
  [19 reports](arbitrary_law_coupling.log).
- Selection transport: [13 exact statements](arbitrary_law_selection.lean)
  and [13 reports](arbitrary_law_selection.log).

## Checked scope

For every finite measure on pairs of positive gaps in `(0,1/2]` satisfying
`old <= new` almost surely, the canonical dyadic cells give
`Gamma(new marginal) <= 3 Gamma(old marginal)`. The construction proves row
identities, geometric cell contraction and local column summability. It
handles atoms at band boundaries and permits infinite total inverse-square
cost and entropy.

Every fractional selection of the old marginal lifts by its Radon--Nikodym
density to a dominated subcoupling. The new selection preserves its total
mass and domination. Its entropy increases by at most three and its residual
tail cost decreases. The original capped infimum over all fractional
submeasures therefore satisfies `K(new) <= sqrt(3) K(old)`.

The coupling is supplied. CDF-to-coupling existence, extension to unresolved
mass at zero, light random contraction and the statistical adaptation/controller
arguments remain outside this checkpoint. The full arbitrary-law adaptation
theorem and Python execution are not claimed formally verified.
See the [current scope](../../docs/ARBITRARY_LAW_FORMALIZATION.md).

## Replay

With the pinned Lean toolchain and Mathlib cache:

~~~sh
python tools/verify_arbitrary_law_coupling.py
python tools/verify_arbitrary_law_selection.py
~~~

The source guard checks 1,132 Lean files. The audit-validator and source-guard
regression suites pass 18 tests. Frozen-source, relative-link and whitespace
checks pass. GitHub CI is separate and must be identified by its checked commit.
