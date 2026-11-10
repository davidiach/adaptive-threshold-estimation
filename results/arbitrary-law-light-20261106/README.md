# Concrete light contraction: native Lean audit

Proof checkpoint: `28d163ebb2f23b696e43f1bd92867ebcef12f248`.
Base checkpoint: `96b545d5ed88ba156778f96403dcf4381ed48b01`.
The product-entropy component was first pushed at
`ba66b9e3bb30a635bcb2c1e05a3483f4a62f8e69`.

The [record](status.json) binds all 63 project sources, seven fresh serial
native compilations with empty logs, and 56 dependencies whose compiled
hashes match earlier published records. No inherited artifact is first
identified here. The pinned compiler, package manifests, audit tools and
prior evidence records are included in the hash bindings.

Two audits independently restate 62 exact statements and check 62 transitive
axiom reports, allowing only `propext`, `Classical.choice` and `Quot.sound`:

- Product entropy, constants and actual cells: [36 statements](arbitrary_law_light_entropy.lean)
  and [36 reports](arbitrary_law_light_entropy.log).
- Residual tails, exact CDF and full comparison: [26 statements](arbitrary_law_light.lean)
  and [26 reports](arbitrary_law_light.log).

## Checked scope

The multiplier is explicitly constructed from uniform volume on the unit
interval by `V = min(1/4, 1/sqrt(2 log(2/u)))`, with value `1/4` at the null
endpoint `u=0`. Lean proves probability normalization and the exact CDF:
zero at nonpositive arguments, `2 exp(-1/(2v^2))` for `0 < v < 1/4`, and
one for `v >= 1/4`. This includes the CDF jump at one quarter.

For every finite positive-gap measure, independence is realized by the
product measure and the gap map is exactly `VD/2`. The two possible
destination bands are proved from the canonical half-open partition.
Actual cell integrals, their product bounds and their destination sums
give the entropy bound `Gamma(new selection) <= 1024 Gamma(old selection)`.
The inverse first-moment and residual-tail bounds give coefficient 32.
Transport of every fractional selection, an exact residual identity, and
passage through the infimum and cap prove
`K(law(VD/2)) <= 32 K(mu)` for the constructed multiplier law.

No multiplier-existence, inverse-moment or finite-entropy premise is
assumed in the final theorem. The proof uses a fixed reference code and
post-division entropy estimates; it does not separately formalize the
paper's sharper intermediate `C_V < 256` calculation in (A4).

Pilot probability bounds and law-dependent onset, robust continuation,
and the full all-budget controller remain outside this checkpoint.
The complete arbitrary-law adaptation theorem remains a paper proof,
and Python execution remains unverified. See the
[current scope](../../docs/ARBITRARY_LAW_FORMALIZATION.md).

## Replay

With the pinned Lean toolchain and Mathlib cache:

```sh
python tools/verify_arbitrary_law_light_entropy.py
python tools/verify_arbitrary_law_light.py
```

All 1,147 Lean sources pass the source guard. All 18 audit-validator and
source-guard regression tests pass. Frozen-source, relative-link and
whitespace checks pass. CI is separate and must be identified by its
actual checked commit.
