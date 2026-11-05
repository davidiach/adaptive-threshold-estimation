# Finite-menu cost grouping: native Lean verification

The source checkpoint is `2052d00fb76d67b0f7ca68e112cebde91d427f2f`.
The [machine-readable record](status.json) binds all seven project sources
in the dependency closure, six fresh compiler logs, one previously published
compiled dependency, and the exact-type/transitive-axiom audit.

The six new modules compile natively with empty logs. All 14 independently
restated theorem types check. Every transitive axiom report contains only
Lean's standard `propext`, `Classical.choice` and `Quot.sound` axioms
(or a subset).

## Checked statements

- Compression retains an actual feasible maximum-saving representative per key.
- The recursive finite-menu solver retains a feasible trace with the same cost
  multiset and at least the saving of every enumerated trace.
- A minimizer of any clipped multiset-price-minus-saving objective survives.
- With `r+1` cost tags, the terminal frontier has at most
  $\binom{m+r}{r}$ states. The transition-count recurrence has the corresponding
  sum bound over stages.
- The multiset entropy equals the existing finite cost-entropy functional.
  Zero costs contribute nothing, and nonnegative vectors satisfy the log formula.
- The entropy-tail finite-menu objective attains its minimum on the frontier.
- The rational branch rule for $x+y/\sqrt B>0$ is exact for $B>0$, including ties.
- Valid endpoint intervals certify a separated optimizer, and overlapping
  intervals still give a valid enclosure of the finite minimum.

[Exact audit input](band_cost_selection.lean) and
[transitive reports](band_cost_selection.log) are preserved alongside the record.

## Boundary

This is a proof of the mathematical finite-menu algorithm. It does not verify
Python's dictionaries, backtracking, rational/interval implementation, or its
construction of suffix menus from a finite gap law. The derivation identifying
those concrete menus with the measure-theoretic selection functional $K$ remains
a paper argument. The existing bandwise-suffix theorem is separately Lean-checked.

The bound counts arithmetic operations, not bit complexity or the precision
needed to separate terminal logarithmic prices. Unrestricted distinct costs can
still give exponentially many states; no general polynomial algorithm or
hardness theorem is established here. There is no independent specialist review.

## Replay

From the repository root with the pinned Lean toolchain and Mathlib cache:

```sh
python tools/verify_band_cost_selection.py
```

The publication used the native compiler with `-j1`, the unchanged dependency
manifests, and source/direct-dependency/object hashes before reusing the single
dependency. The compiler identity is recorded in `status.json`.

Four existing Python solver regressions, 15 shared verifier-guard regressions,
the three proof-escape scanner regressions and frozen-source verification also
passed locally. CI status belongs to the exact GitHub commit, separately from
this native record.

