# Infinite partition-series audit

Proof checkpoint [d70f84b](https://github.com/davidiach/adaptive-threshold-estimation/commit/d70f84bcc0c0c1ded61158747347821fbf037efd).

The [status record](status.json) identifies 29 independently restated theorem types and their transitive axiom reports, ten freshly compiled modules, and one reused dependency with a previously published matching object hash. All ten compiler logs are empty. The closure contains eleven project modules.

The [audit input](optimal_quantile.lean) and [raw output](optimal_quantile.log) are preserved for this checkpoint. The record includes source hashes, compiler identity and object hashes. The roots use only the standard Lean axioms allowed by the verifier.

The all-finite-vector bound is equivalent to the infinite exponential partition inequality for every tangent parameter. The record also checks summability, convergence of finite partitions, strict decrease in the factor, and monotonicity above the factor in the tangent parameter.

The unique scalar root, arbitrary-law reduction and finite-law sharpness construction are outside this record.
