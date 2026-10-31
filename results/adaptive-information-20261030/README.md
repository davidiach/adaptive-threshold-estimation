# Adaptive information, sharp testing, and finite-prefix comparison

This additive checkpoint follows `f677f77` on the branch based at `8fc36ac`.
Protected source identities and all commands appear in `status.json`.
`ExactAudit.lean` records seven independently stated theorem targets.

For arbitrary measurable estimators and probability measures P and Q, the
maximum squared risk is at least gap squared times affinity squared divided
by four. Infinite risks and zero endpoint densities are included. The RMS
version is gap times affinity divided by two.

The midpoint information/work bound transfers from a single coin to finite
adaptive populations, unrestricted natural-number coin labels, arbitrary
measurable random seeds, and the original observable seed/prefix experiment.
The Hellinger distance is at most K_N times midpoint expected work divided by
four; each physical flip is charged once. Symmetric contraction of endpoint
priors preserves their midpoint, scales the mean gap by s, and scales the
actual count-flow information ratio by s squared, including s = 0.

Combining these facts proves the factor-eight finite-prefix comparison: if
an actual globally rare-budget algorithm has a measurable N-prefix estimate
with RMS risk at most T for every globally rare prior, then P_N <= 8T.
This is stated for all probability gap laws, 0 < rho <= 1/2 and B > 0.
The truncation bridge from arbitrary infinite-process outputs, the universal
rarity floor, and the final factor-sixteen certificate are not part of this
checkpoint. Genie convergence and the cloud session's entropy-tail statistical
lower bound are also not claimed.

The audit rebuilt nine new modules, checked 498 declarations in 78 modules,
seven exact types, and all transitive axioms. Only `Classical.choice`,
`Quot.sound`, and `propext` occur. Other dependencies used cached objects with
recorded source hashes; this was not a full dependency rebuild or a CI run.
All four verifier regression tests passed.

Reproduce with `python tools/verify_adaptive_information.py --cached-dependencies`;
omit the flag for a full local-dependency rebuild. Fresh runs belong in `.runtime`.
The first nine logs are source builds; `010.log` is the exact-type/axiom audit.
