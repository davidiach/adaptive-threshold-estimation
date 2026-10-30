# Infinite-divergence counterexample

This additive checkpoint follows `cc661d9` on the branch based at `8fc36ac`.
Exact sources, commands and audited declarations are in `status.json`.

The law is uniform on (0,1/2], with density 2. At rarity 1/4 the priors
are q_L = 0, q_H = q_w = 1/4, and q_v(d) = 1/2-d. Lean proves:

- This is a probability law and all four priors are admissible.
- The latent divergence is infinite, and so is every positive-cap genie ratio.
- Every finite count flow has information at most 3/4 times its actual
  work under q_w. Therefore the ordinary infinite-cap ratio is at most 3/4.
- The unregularized genie ratios do not converge to that ordinary ratio.

The work comparison is proved for arbitrary stopping flows, using a
stopping-depth telescoping identity and elementary beta-moment recurrences.
The auxiliary uniform Bernoulli mixture need not be an admissible rare prior.
This is the specific example in the preserved manuscript, not an abstract
assumption of the desired coefficient or divergence.

Eight new modules were rebuilt. The audit checked 89 declarations in fifteen
Genie modules and three exact statements; the only transitive axioms are
Classical.choice, Quot.sound and propext. Other local dependencies used
cached objects with recorded source hashes. This is not a full dependency
rebuild or CI run. All four verifier regressions pass.

The entropy-tail statistical lower bound is outside this checkpoint.
Reproduce with `python tools/verify_genie_counterexample.py --cached-dependencies`;
omit the flag for a full local-dependency rebuild. Use fresh output.
