# Sharp finite-core selection reduction

Proof checkpoint [3212ff9](https://github.com/davidiach/adaptive-threshold-estimation/commit/3212ff9f1668f96dbca2b58dbecf7bd6267a7da2).

The [status record](status.json) identifies 49 independently restated theorem types and 49 transitive axiom reports. Its dependency closure contains 28 project modules, comprising 27 native compiled modules from this PR and one reused dependency with a previously published matching object hash. All 27 compiler logs are empty.

The [audit input](quantile_sharp_law.lean) and [raw output](quantile_sharp_law.log) are preserved for this checkpoint. Source hashes, compiler identity and object hashes identify the checked closure. The scalar-root dependency has its own [54-statement record](../optimal-quantile-root-20261105/README.md).

For arbitrary nonnegative finite core vectors $v,b$, Lean checks
$$
1+\sqrt{G(v+b)}
\le c_{\rm vec}\left(\sqrt{G(v+e_0)}+b_0+\sum_{j\ge0}2^j b_{j+1}\right).
$$
The sums are finite and $c_{\rm vec}$ is the previously checked unique scalar root.

The proof includes the 1-Lipschitz entropy bound, skipped-tail absorption, concavity, reduction to disjoint selected and skipped coordinates, interaction monotonicity and growth, the dyadic weighted entropy bound, and both boundary-coordinate cases. Zero coordinates and an empty family above the boundary are included.

Run `python tools/verify_quantile_sharp_law.py` for these exact statements and transitive axiom reports.

General-law measure normalization and finite-law realization remain paper proofs. This record establishes the deterministic finite-core reduction used in that bridge.
