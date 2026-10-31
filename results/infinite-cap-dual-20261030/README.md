# Exact attained infinite-cap dual

This additive checkpoint follows `5573e93` on the branch based at `8fc36ac`.
All protected source identities and commands appear in `status.json`.
`ExactAudit.lean` independently checks eight theorem types.

For an arbitrary probability gap law, 0 < rho <= 1/2 and B > 0, the
infinite-cap stopping value satisfies

    P_infinity^2 = max_Q (theta_H - theta_L)_+^2 / (4 + B K_infinity(Q)),
    D_infinity <= P_infinity <= 3 D_infinity,
    R <= P_infinity <= 8 R.

The maximum is attained by actual globally rare priors. For 0 < rho <= 1/4,
it is positive and an attaining quadruple has finite information ratio.
Increasing caps increase ordinary information and decrease primal values;
both sequences converge monotonically to their defined infinite-cap limits.

One compact product image records all finite count coefficients and target
means simultaneously. Chosen prior representatives need not be continuous:
their observable moments are. Closed-perspective lower semicontinuity,
positive root work and a finite continuous numerator give upper
semicontinuity of each dual objective, including infinite denominators.
Nested compact superlevel sets retain a maximizer as the cap increases.
The statistical comparison uses the actual observable minimax experiment,
finite-cap realization and the sharp truncation limit. Positivity uses the
independent Bernoulli-label floor, not the entropy-tail lower theorem.

The audit rebuilt all 14 new modules, checked 68 declarations and eight
exact types, and inspected their transitive axioms. Only `Classical.choice`,
`Quot.sound`, and `propext` occur. Other local dependencies used cached
objects with recorded source hashes. This was neither a full dependency
rebuild nor a CI run. All four audit regression tests passed.

Latent-reveal brackets and convergence are separate work. This checkpoint
does not prove the entropy-tail statistical lower bound.

Reproduce with `python tools/verify_infinite_cap_dual.py --cached-dependencies`;
omit the flag for a full local-dependency rebuild. Use a fresh `.runtime`
output directory. Logs 001 through 014 are source builds; 015 is the
exact-type and transitive-axiom audit.
