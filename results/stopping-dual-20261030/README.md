# Attained four-prior stopping dual

This additive checkpoint follows `1779988` on the branch based at `8fc36ac`.
Exact identities of the 116 protected proof/tool/dependency sources are in
`status.json`; `ExactAudit.lean` preserves the checked target source.

For every probability law on `(0,1/2]`, `0 < rho <= 1/4`, positive budget,
and positive finite cap, Lean proves the unchanged `AttainedDualStatement`:
the squared robust stopping-program value equals its four-prior dual, both
the primal minimum and dual maximum are attained, the value is positive,
and an optimal quadruple has finite information/work ratio.

The proof constructs compact moment images of the actual global rarity
class, derives finite convex multipliers from geometric separation, selects
four actual priors by compact minimax, eliminates outputs with explicit
cone flows, and handles null variance references. Primal attainment uses
closedness and compact objective sublevels after pruning universally null
output coordinates. Neither strong duality nor compactness is assumed as
an extra premise of the final theorem.

The audit checks 188 declarations in 30 stopping-program modules, two exact
types (the named specification and an independently expanded statement), and
all transitive axioms. Only `Classical.choice`, `Quot.sound`, and `propext`
occur. The four verifier regression tests passed. This checkpoint rebuilt
the six new primal-attainment modules, used cached dependency objects for
the earlier value-identity development, and recorded their source hashes.
It did not rebuild the complete local dependency closure. This is local
verification, not a CI claim.

Reproduce with `python tools/verify_stopping_dual.py --cached-dependencies`;
omit the flag to rebuild every local dependency. Fresh reruns belong in
`.runtime`. Logs `001.log` through `006.log` are source compilations and
`007.log` contains the exact-target and transitive-axiom check.

This proves the conic-program theorem. Statistical flow realization, the
factor-sixteen minimax certificate, and genie convergence remain separate
unfinished work. The entropy-tail statistical lower bound remains assigned
to the independent cloud session.
