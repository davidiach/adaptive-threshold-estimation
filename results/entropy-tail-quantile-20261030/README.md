# Arbitrary-law quantile comparison audit

This additive checkpoint starts from repository commit `8fc36ac` and verifies
the exact frozen `QuantileSplitStatement` and `QuantileComparisonStatement` in
`ThresholdHC.EntropyTail.Specification`.

For every probability law on `(0,1/2]`, rarity `0 < rho <= 1/4`, and budget
`B > 0`, the checked comparison is

`K(B) <= Q(B) <= (1 + 2 sqrt 2) K(B)`.

The split includes fractional boundary atoms. The remaining core has finite
cost entropy. The supporting development also proves saturation at `rho`
when the budget scale is at least the quantile threshold, the scale-separated
entropy bound with constant `4`, and extended-real inverse-moment estimates.

The audit rebuilt all 53 local dependency modules, checked 20 new modules and
121 declarations, and checked both exact targets. The only transitive axioms
are `propext`, `Classical.choice`, and `Quot.sound`. Five verifier regression
tests and the original frozen-source check also passed.

`status.json` records source hashes and command outcomes. Logs `001.log` through
`053.log` are source compilations; `054.log` contains the exact-target and axiom
audit. Reproduce with `python tools/verify_entropy_tail_components.py`, using
the pinned Lean toolchain and Mathlib revision. Fresh output goes to `.runtime`.

This is a deterministic functional comparison. It does **not** certify the
entropy-tail statistical upper bound, its separately assigned statistical
lower bound, the closed quantile minimax characterization, or the finite-law
upper constant `30001`. The full risk targets remain explicit unproved
propositions in the specification.
