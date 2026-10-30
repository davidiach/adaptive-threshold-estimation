# Exact finite stopping-program risk certificate

This additive checkpoint follows `a2f2206` on the branch based at `8fc36ac`.
Protected source identities and all commands appear in `status.json`.
`ExactAudit.lean` records eight independently stated theorem targets, including
all three unchanged stopping-program specifications.

For every probability law of gaps in (0,1/2], 0 < rho <= 1/4 and B > 0,
the original unrestricted observable minimax risk satisfies

    R <= P_N <= 16 R,  N = ceil(64 max(B, rho B^2)).

The proof includes the uniform Bernoulli-label floor
R >= min(rho, sqrt(rho/B))/16 and the sharp truncation comparison
P_N <= 8(R + rho sqrt(B/(N+1))/2). The truncation estimate is a measurable
function of the original random seed and finite observed prefix. It returns
the actual terminal output if the policy has stopped, or rho/2 otherwise.
Its squared loss is at most the original squared loss plus the midpoint loss
on the continuation event. A pathwise work bound supplies the Markov penalty.
Infinite original risks are retained, with no integrability assumption on the
estimator. The Bernoulli floor uses constant sign priors, a uniform latent-label
information bound, and the limit of these prefix estimates.

No entropy-tail statistical lower theorem is assumed or proved here. The
cloud session owns that separate result. The infinite-cap dual, genie
convergence and executable approximation accuracy remain separate work.

The audit rebuilt nine new modules, checked 559 declarations in 96 modules,
eight exact types, and all transitive axioms. Only `Classical.choice`,
`Quot.sound`, and `propext` occur. Other dependencies used cached objects with
recorded source hashes; this was not a full dependency rebuild or a CI run.
All four verifier regression tests passed.

Reproduce with `python tools/verify_finite_risk_certificate.py --cached-dependencies`;
omit the flag for a full local-dependency rebuild. Fresh runs belong in `.runtime`.
The first nine logs are source builds; `010.log` is the exact-type/axiom audit.
