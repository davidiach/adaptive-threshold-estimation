# Entropy Lipschitz and skipped-tail absorption

Proof checkpoint [8579e42](https://github.com/davidiach/adaptive-threshold-estimation/commit/8579e4226e04755cdac9f4efd69b63e6c7a708d9).

The [status record](status.json) identifies 17 independently restated theorem types and transitive axiom reports, four freshly compiled modules, and one reused dependency with a previously published matching object hash. All four compiler logs are empty. The closure contains five project modules.

The [audit input](quantile_sharp_law.lean) and [raw output](quantile_sharp_law.log) are preserved for this checkpoint. The record includes source hashes, compiler identity and object hashes.

For every finite nonnegative vector, adding the square of a nonnegative scalar to one coordinate makes the square root of its cost entropy a nondecreasing 1-Lipschitz function of that scalar. This includes the endpoint zero, zero background coordinates and an empty family of other coordinates. The skipped-tail absorption inequality follows.

The proof checks the binary entropy slope inequality, entropy coarsening, the derivative and its upper bound, and continuity at the endpoint. The complete arbitrary-law normalization and finite-law realization remain outside this record.
