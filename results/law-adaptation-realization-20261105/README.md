# Observable finite-family law adaptation: native Lean audit

Proof checkpoint: `b18f73fc0120b0b68b45b31e5aad08c943867fde`.
The [machine-readable record](status.json) binds all 648 project sources,
eight fresh native compilations with empty logs, and 640 unchanged compiled
dependencies whose hashes match previously published evidence.
There are no first-time inherited artifacts.

All 22 independently restated exact theorem types and transitive axiom reports
pass, using only `propext`, `Classical.choice` and `Quot.sound`.
The [audit input](law_adaptation_realization.lean), [reports](law_adaptation_realization.log)
and eight empty compilation logs are preserved here.
The prior [17-component record](../law-adaptation-20261105/README.md) remains unchanged.

## Checked result

For every supplied finite nonempty family of distinct positive-gap probability
laws, known rarity $0<\rho\le1/4$ and $0<\delta\le1/4$, Lean constructs a single
observable procedure before the true candidate or sign law is supplied.

- Positive even moments determine the law; finitely many moments separate the family.
- The pilot reads $2m$ flips on each of $n$ fresh persistent coins and uses the
  shared even-prefix parity statistics. Their expectations under the original
  population law are independent of the gap-dependent sign distribution.
- The selected procedure uses fresh coin labels and its own oracle seed.
  Its output is proved equal to a function of its actual observed history.
- The physical cap, compatibility across budgets and nesting hold on every path,
  including misidentification paths. Budgets within the pilot report the full
  parameter range.
- On one event of failure probability at most $\delta$, coverage holds at every
  integer budget and half-width is at most
  $3000004\,K_{\mu,\rho}(B/\Lambda(B,\delta))$ for every $B\ge2H$, where $H=2mn$.
- Both reported endpoints at each budget jointly have their law in the original
  observable experiment.

The full theorem is [finite_family_anytime](../../lean/ThresholdHC/LawAdaptation/Full.lean).
[Properties](../../lean/ThresholdHC/LawAdaptation/Properties.lean) supplies nesting
and the original-experiment law. The [research note](../../docs/FINITE_FAMILY_ADAPTATION.md)
states the pilot calibration and the mathematical scope.

This is a finite-family theorem. It does not give a family-uniform onset time,
test family membership, or establish arbitrary-law oracle adaptation.
The mathematical construction is noncomputable; the Python runtime is tested,
not formally verified. No independent specialist review is claimed.

## Replay

With the pinned Lean toolchain and Mathlib cache:

~~~sh
python tools/verify_law_adaptation_realization.py
~~~

The native build uses `-j1` and validates source, direct-dependency and compiled
object hashes before reuse. The record identifies its compiler and unchanged
dependency manifests. The three proof-escape guard tests, frozen-source and
whitespace checks passed. CI is separate and belongs to its exact commit.
