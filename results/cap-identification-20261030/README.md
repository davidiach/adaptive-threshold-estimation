# Fixed-cap identification checkpoint

This additive development starts from `8fc36ac` and follows the observable
upper-bound checkpoint `d064279`. Exact source identities are in `status.json`.

For every probability law on positive gaps at most one half, `0 < rho <= 1`,
and positive integer cap `N`, Lean checks that the largest target difference
between globally rare priors matching the first `ceil(N/2)` odd moments is
attained. Writing this difference as `Delta_N`, it proves
`P_N(B) -> Delta_N/2` as the expected budget tends to infinity. The proof uses
compact moment images, finite-dimensional affine recovery, and explicit
full-depth feasible certificates; it does not assume strong duality.

For a law with exactly `m` support points, `Delta_N = 0` exactly when
`N >= 2*m-1`. Infinite support implies `Delta_N > 0` for each fixed cap.
Moment matching is equivalent to matching all capped count coefficients and
implies equality of actual seed-and-stopped-word laws for every independently
randomized single-unit procedure with this cap.

This checkpoint rebuilt 36 new stopping/identification modules and checked
245 declarations, ten independently written exact types, proof-escape scans,
source identities, and all transitive axioms. Only `Classical.choice`,
`Quot.sound`, and `propext` occur. It used cached objects for dependencies
outside these two groups, recording all 194 protected source/tool hashes;
it did not rebuild that entire dependency closure. This is local evidence,
not a CI claim. `ExactAudit.lean` preserves the checked source, and `037.log`
contains its axiom reports.

Reproduce with `python tools/verify_stopping_components.py
--cached-dependencies`; omit the flag to rebuild all local dependencies.
Fresh runs belong in `.runtime`.

The stopping program's strong four-prior duality, statistical realization,
factor-sixteen certificate, and genie convergence remain unfinished. This
record does not certify the separately assigned entropy-tail statistical
lower bound or the two-sided entropy-tail/quantile characterization.
