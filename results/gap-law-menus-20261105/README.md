# Concrete finite-gap-law menus: native Lean audit

Proof checkpoint: `9d670f22a9981a7bb5085878d9d9fb85a545ac1c`.
The [machine-readable record](status.json) binds all 64 project sources,
five fresh native compilations with empty logs, and 59 unchanged compiled
dependencies whose hashes match previously published evidence. There are no
first-time inherited artifacts.

All 13 independently restated exact theorem types and transitive axiom reports
pass using only `propext`, `Classical.choice` and `Quot.sound`.
The [audit input](gap_law_menus.lean), [reports](gap_law_menus.log) and five empty
compilation logs are preserved here. The original
[14-statement algorithm audit](../band-cost-formal-20261105/README.md) remains unchanged.

## Checked result

For every finite-support probability law on positive gaps, $0<\rho\le1/4$ and
$B>0$, the [full theorem](../../lean/ThresholdHC/GapLawMenus/Full.lean) constructs
the occupied-band suffix menus from the actual support and proves that the
cost-compressed solver retains a selection attaining the original
entropy-tail functional $K$, against all fractional submeasures.

The proof checks:

- Exact equality between the union of enumerated menu traces and the full
  family of bandwise suffix selections.
- Disjointness of choices from distinct bands.
- The exact cost vector of each selected measure and its entropy, including
  equality with the original supremum over finite band prefixes.
- Equality of accumulated savings with the removed ordinary tail cost.
- Equality of the real clipped menu objective with the original measure objective,
  and preservation of its global optimum by the existing compression algorithm.
- The atomic formulas $a=\sum_d w_d/d^2$ and
  $s=\sum_d w_d\min(1,h/d)$ for the concrete menu costs and savings.

The mathematical menu construction is noncomputable. Python execution remains
tested rather than formally verified. This result does not settle efficient
exact selection for unrestricted distinct band costs or the bit complexity of
transcendental comparisons. No independent specialist review is claimed.

## Replay and additional checks

With the pinned Lean toolchain and Mathlib cache:

~~~sh
python tools/verify_gap_law_menus.py
~~~

The native build uses `-j1` and checks source, direct-dependency and object
hashes before reuse. All four existing solver regressions pass, including
comparison with exhaustive subsets, the 64-band repeated-cost example, exact
cancellation and refined near ties. The three proof-escape tests,
frozen-source and whitespace checks pass. CI status is specific to its commit.
