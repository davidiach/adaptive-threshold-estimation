# Dominated-mass comparison: native Lean audit

Proof checkpoint: `8a02e6b89883802cd3d0cdd32ba723b527c90054`.
Base checkpoint: `3177cfe4996259d18c4a83ca68a17c9b3ca71eb7`.

The [record](status.json) binds all 63 project sources, three fresh serial
native compilations with empty logs, and 60 dependencies whose compiled
hashes match earlier published records. No inherited artifact is first
identified here. The pinned compiler, package manifests, audit tools and
prior evidence records are included in the hash bindings.

The audit independently restates [22 exact statements](arbitrary_law_dominated.lean)
and checks [22 transitive axiom reports](arbitrary_law_dominated.log), permitting
only `propext`, `Classical.choice` and `Quot.sound`.

## Checked scope

The zero-atom entropy is monotone and homogeneous. Its residual tail cost
is additive, homogeneous and exactly one for a unit atom at zero.
A clipped Radon–Nikodym density restricts every fractional selection to
a dominated finite law, with explicit domination and residual identities.
Consequently the capped selection functional K is monotone under measure
domination.

For finite measures, `lambda <= c eta + e delta_0` gives
`K(lambda) <= c K(eta) + e` when `c >= 1` and `e >= 0`.
This is the paper's dominated-mass inequality (A5), proved without finite
inverse moments or finite entropy. The original infimum over all fractional
selections and cap at rho are retained. The Lean statement uses `ofReal e`,
so it also covers negative real inputs by clipping them to zero.

The light random contraction, pilot probability bounds and onset, robust
continuation, and full all-budget controller are outside this checkpoint.
The complete arbitrary-law adaptation theorem remains a paper proof, and
Python execution is unverified. See the [current scope](../../docs/ARBITRARY_LAW_FORMALIZATION.md).

## Replay

With the pinned Lean toolchain and Mathlib cache:

```sh
python tools/verify_arbitrary_law_dominated.py
```

The source guard and all 18 audit-validator/source-guard regression tests
pass. Frozen-source, relative-link and whitespace checks pass. CI is
separate and must be identified by its actual checked commit.
