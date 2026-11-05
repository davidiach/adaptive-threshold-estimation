# Sharp finite-vector quantile factor

Proof checkpoint [df8be8c](https://github.com/davidiach/adaptive-threshold-estimation/commit/df8be8cc6472a3fec98dca63ea0f5eb58a4d17f3).

The [status record](status.json) identifies 54 independently restated theorem types and 54 transitive axiom reports, fifteen freshly compiled modules, and one reused dependency with a previously published matching object hash. All fifteen compiler logs are empty. The closure contains sixteen project modules.

The [audit input](optimal_quantile.lean) and [raw output](optimal_quantile.log) are preserved for this checkpoint. The record includes source hashes, compiler identity and object hashes. The roots use only the standard Lean axioms allowed by the verifier.

## Checked statements

- The finite Gibbs criterion and attained square-root tangent give the exact partition test for every finite nonnegative cost vector.
- Finite partitions converge to the summable exponential series.
- The series is jointly continuous on its domain. Its compact maximum is attained, continuous and strictly decreasing in the factor.
- Analytic bounds put the maximum above one at $\sqrt2$ and below one at $31/20$.
- A unique scalar root lies strictly between those endpoints.
- For every real factor, all finite-vector inequalities hold exactly when the factor is at least that root. Every smaller factor has a finite nonnegative-vector counterexample.

Run `python tools/verify_optimal_quantile.py` for the exact statements and transitive axiom reports.

The normalization of arbitrary gap laws, the reduction of arbitrary selections, and the finite-law realization of cost vectors remain paper proofs. The numerical bracket of width $10^{-12}$ retains its separate exact-arithmetic certificate in `tools/verify_optimal_quantile_factor.py`. This record establishes the finite-vector optimum.
