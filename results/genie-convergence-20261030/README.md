# Posterior information and convergent genie certificates

This additive checkpoint follows `4c30f6e` on the branch based at `8fc36ac`.
The exact protected sources, commands and audit roots are in `status.json`.

The latent state and iid Bernoulli tape are constructed from the original
gap law and variance prior. The latent score's second moment is C_v.
Finite-prefix conditional expectations have second moments exactly equal
to the terminal information sum, including null cells. The strong law
identifies the Bernoulli parameter and hence the positive gap and sign.
Levy upward convergence and Fatou's lemma then prove, when C_v is finite,

    terminalInformation_N -> C_v, e_N -> 0, K_N^+ -> K_infinity.

Only the variance prior is regularized toward the endpoint midpoint.
It remains admissible, has C_v <= 4/epsilon, and increases K_infinity by
at most the factor 1/(1-epsilon). Taking the cap limit first, then removing
regularization, proves optimized convergence for every probability gap law,
0 < rho <= 1/2 and B > 0:

    0 < G_N increases to P_infinity,
    G_N/8 <= R <= P_N,
    eventually P_N <= 2 G_N, certifying R <= P_N <= 16 R.

The original adaptive minimax experiment is used. There is no uniform cap
rate, bit-complexity claim, or claim that an unregularized quadruple with
infinite latent divergence converges. The entropy-tail statistical lower
bound, finite-support genie SOCP, direct squared certificate and explicit
infinite-divergence counterexample are outside this checkpoint.

The audit rebuilt twelve new modules and checked 223 declarations in 33 Genie modules, twelve exact types and all transitive axioms.
Only `Classical.choice`, `Quot.sound`, and `propext` occur. Other local
dependencies used cached objects with recorded source hashes. This is not
a full dependency rebuild or CI run. All four verifier regression tests pass.

Reproduce with `python tools/verify_genie_convergence.py --cached-dependencies`;
omit the flag for a full local-dependency rebuild. Use fresh `.runtime` output.
