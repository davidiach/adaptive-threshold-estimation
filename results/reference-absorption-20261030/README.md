# Reference absorption and the midpoint modulus

This additive checkpoint follows `936fd6d` on the branch based at `8fc36ac`.
Exact identities of 122 protected sources are in `status.json`.
`ExactAudit.lean` preserves three independently stated targets.

For every probability gap law, positive budget and `0 < rho <= 1/2`, the
actual stopping-program value satisfies `D_N <= P_N <= 3 D_N`, where `D_N`
is the two-prior modulus with both reference priors equal to the endpoints'
midpoint. The supremum uses actual globally rare sign laws.

Each four-prior tuple is transformed into a midpoint tuple by adding both
references to each endpoint and dividing by three. This preserves rarity,
divides the target gap by three, and decreases the extended information/work
ratio. The proof includes zero reference coefficients and infinite ratios;
it does not assume all likelihood coefficients are positive. The comparison
then uses the previously proved attained four-prior conic dual.

The audit rebuilt five new modules, checked 225 declarations in 36 modules,
three exact types, and all transitive axioms. Only `Classical.choice`,
`Quot.sound`, and `propext` occur. Other dependencies used cached objects with
recorded source hashes; this was not a full dependency rebuild or a CI run.
All four verifier regression tests passed.

Reproduce with `python tools/verify_reference_absorption.py --cached-dependencies`;
omit the flag for a full local-dependency rebuild. Fresh runs belong in `.runtime`.
The first five logs are source builds; `006.log` is the exact-type/axiom audit.

This comparison does not prove the adaptive testing reduction, the
factor-sixteen certificate, Bellman information-ratio attainment, or genie
convergence. Those remain separate. The entropy-tail statistical lower bound
remains with the cloud session.
