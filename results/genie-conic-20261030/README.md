# Direct risk certificate and finite atom genie SOCP

This additive checkpoint follows `261875f` on the branch based at `8fc36ac`.
Exact sources, commands and audited declarations are recorded in `status.json`.

For a certified genie price kappa, endpoint gap t after reference absorption,
and x = B*kappa, the original unrestricted adaptive minimax risk obeys

    R^2 >= t^2/4 * (1-x/4)^2  if x <= 4/3,
    R^2 >= 4*t^2/(27*x)        otherwise.

Here t is one third of the original four-prior endpoint gap. The optimal
contraction is proved to attain the maximum over [0,1]. A nonpositive
modified Bellman root provides the price certificate when latent divergence
is finite.

For finite positive atom weights at distinct positive gaps, nonnegative
rarity, positive budget and positive integer cap, the explicit atom conic
program has value exactly G_N^2. Its constraints are linear or rotated
quadratic cones and its objective is linear. Every feasible atom point
realizes globally measurable admissible priors, including zero endpoint
scale and zero work price. Singular references and infinite information are
handled without replacing closed perspectives by ordinary division.
The formal variable bound is 3 + 6m + (N+1)^2; no bit-complexity or numerical
solver-accuracy result is claimed.

The audit rebuilt eleven new modules, checked 230 declarations in 35 Genie
modules and nine exact types. Only Classical.choice, Quot.sound and propext
occur as transitive axioms. Other dependencies used cached objects with
recorded source hashes. This is not a full dependency rebuild or CI run.
All four verifier regression tests pass. The entropy-tail statistical lower
bound and explicit infinite-divergence counterexample are outside this audit.

Reproduce with `python tools/verify_genie_conic.py --cached-dependencies`;
omit the flag for a full local-dependency rebuild. Use fresh output.
