# Ordered stopping procedures and local information

This additive checkpoint follows `6213150` on the branch based at `8fc36ac`.
Protected source identities and commands appear in `status.json`.
`ExactAudit.lean` records four independently expanded theorem statements.

Every capped measurable seeded stopping procedure, including procedures that
depend on observation order or stop before taking any observations, aggregates
to a feasible count flow. Its expected physical work equals the count-flow work.
For arbitrary endpoint sign laws, midpoint information I and the actual stopped
transcript Hellinger distance h satisfy 4h <= I <= 8h. Consequently
h <= K_N E_midpoint[T]/4 for the actual midpoint information/work ratio K_N.
Boundary probabilities, null prefixes, and zero work are included.

The audit rebuilt eleven new modules, checked 359 declarations in 47 modules,
four exact types, and all transitive axioms. Only `Classical.choice`,
`Quot.sound`, and `propext` occur. Other dependencies used cached objects with
recorded source hashes; this was not a full dependency rebuild or a CI run.
All four verifier regression tests passed.

Reproduce with `python tools/verify_ordered_information.py --cached-dependencies`;
omit the flag for a full local-dependency rebuild. Fresh runs belong in `.runtime`.
The first eleven logs are source builds; `012.log` is the exact-type/axiom audit.

Adaptive population testing transfer, the factor-sixteen risk certificate,
and genie convergence remain separate work. This checkpoint does not prove
the entropy-tail statistical lower bound assigned to the cloud session.
