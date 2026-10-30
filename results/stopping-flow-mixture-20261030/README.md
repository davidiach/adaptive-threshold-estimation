# Finite flow mixtures and observable calls

This additive checkpoint follows `c008d90` on the branch based at `8fc36ac`.
Exact identities of 237 protected sources are in `status.json`.
`ExactAudit.lean` preserves the five independently stated targets.

Lean proves weighted flow conservation and total stopping mass equal to root
activation under every probability prior. Bellman potentials bound every
admissible count flow. Each cone flow has exact stopping and continuation
weights given by a finite nonnegative mixture of deterministic count decision
tables, whose weights sum to one. Every positive-weight table continues at
the root and stops at the cap. The construction includes zero-intensity and
unreached states. It does not assume a policy decomposition theorem.

Deterministic tables are also implemented as actual observable `FiniteCall`s.
They have positive cost, stop by the cap, compute outputs from the stopped
count state, and have an explicit finite output bound. Prefix observability
and measurability are fields of the proved call construction.

The audit rebuilt ten new modules, checked 158 declarations in 17 modules,
five exact types, and all transitive axioms. Only `Classical.choice`,
`Quot.sound`, and `propext` occur. Dependencies used cached objects with recorded
source hashes; this was not a full dependency rebuild or a CI run. All four
verifier regression tests passed.

Reproduce with `python tools/verify_stopping_flow_mixture.py --cached-dependencies`;
omit the flag for a full local-dependency rebuild. Fresh runs belong in `.runtime`.
The first ten logs are source builds; `011.log` is the exact-type and axiom audit.

This checkpoint does not yet prove that the observable calls have the flow's
statistical moments, or that their Poisson estimator realizes a certificate.
The statistical program upper bound, the factor-sixteen comparison, Bellman
attainment for the information ratio, and genie convergence remain separate
work. The entropy-tail statistical lower bound remains with the cloud session.
