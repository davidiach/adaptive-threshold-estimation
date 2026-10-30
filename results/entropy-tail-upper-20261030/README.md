# Observable entropy-tail and quantile upper audit

This additive checkpoint verifies the full upper construction introduced in
commit `1f4a371`, on the branch based at `8fc36ac`. Exact source identities are
recorded in `status.json`; later stopping/identification changes do not alter
this audited dependency closure.

For every probability law on `(0,1/2]`, `0 < rho <= 1/4`, and `B > 0`, Lean
checks the original observable minimax risk bound

`R(mu,rho,B) <= 28000 K(mu,rho,B)`.

It also checks the frozen upper targets with coefficient `33000`, the
closed-quantile upper coefficient `30001` for every law, and the deterministic
comparison `K <= Q <= (1 + 2 sqrt 2) K`, including fractional boundary atoms.
The estimator observes only its independent seed and purchased coin flips.
Poisson sampling, shared-coin increments, the adaptive controller, expected
physical work, risk identities, and removal of support/integrability cutoffs
are included in the proof.

The audit rebuilt all 306 local dependency modules and checked 611 declarations
in 77 new modules, six independently specified exact types, all transitive
axioms, proof-escape scans, the specification freeze, and source identities.
Only `propext`, `Classical.choice`, and `Quot.sound` occur. The eight verifier
regression tests and original frozen-source check also passed during this
development. This is local verification, not a CI claim.

Logs `001.log` through `306.log` are source compilations; `307.log` is the
exact-target/transitive-axiom audit. Reproduce with
`python tools/verify_entropy_tail_upper.py`, using the pinned Lean and Mathlib
versions. Fresh reruns belong in `.runtime`.

This record does not certify the separately assigned entropy-tail statistical
lower bound, the two-sided quantile minimax characterization, or the full
stopping-program and genie theorems. Those flags remain false.
