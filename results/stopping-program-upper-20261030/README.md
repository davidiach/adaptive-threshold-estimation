# Observable stopping-program upper bound

This additive checkpoint follows `36b4b3d` on the branch based at `8fc36ac`.
Exact identities of 313 protected sources are in `status.json`.
`ExactAudit.lean` preserves three independently stated targets.

The unchanged `ProgramUpperStatement` is proved in the original observable
experiment: for every probability gap law, `0 < rho <= 1/4`, positive budget
and positive cap, `R <= P_N`. Every feasible certificate is realized by an
actual measurable estimator with its uniform expected-work and squared-risk
bounds. No statistical realization or estimator-existence premise is assumed.

The proof identifies actual Bernoulli prefix laws and stopped-table moments,
then realizes arbitrary flow weights by a finite mixture of deterministic
count tables. Positive-rate tables give bounded observable calls. Independent
Poisson replication reproduces the flow mean and work, bounds its second
moment, and the deterministic offset supplies the certificate's bias. The
zero-intensity case is handled separately. Primal attainment yields the final
minimax comparison.

The audit rebuilt fourteen new modules, checked 304 declarations in 45
modules, three exact types, and all transitive axioms. Only `Classical.choice`,
`Quot.sound`, and `propext` occur. Dependencies used cached objects with recorded
source hashes; this was not a full dependency rebuild or a CI run. All four
verifier regression tests passed.

Reproduce with `python tools/verify_stopping_program_upper.py --cached-dependencies`;
omit the flag for a full local-dependency rebuild. Fresh runs belong in `.runtime`.
The first fourteen logs are source builds; `015.log` is the exact-type and axiom audit.

The factor-sixteen risk comparison, information-ratio Bellman attainment, and
genie convergence remain separate work. The entropy-tail statistical lower
bound remains with the cloud session. This checkpoint does not claim those
results or full completion of the stopping-program paper.
