# Exact quantile-factor characterization and finite-law sharpness

Proof checkpoint [43a6057](https://github.com/davidiach/adaptive-threshold-estimation/commit/43a60579395c6b14f33ccd9a23f5e7a928eb843e).

The [status record](status.json) identifies 219 independently restated theorem types and 219 transitive axiom reports across three audits.

| Audit | Exact statements | Transitive reports |
|---|---:|---:|
| Scalar root and finite-vector optimum | 54 | 54 |
| All-law upper comparison | 84 | 84 |
| Finite-law realization and sharpness | 81 | 81 |

The closure contains 126 project modules. It includes 59 compiled modules from this PR and 67 reused dependencies with previously published matching object hashes. All 59 compiler logs are empty. No unmatched artifacts remain.

The exact inputs and raw output are preserved for the [scalar audit](optimal_quantile.lean), [all-law audit](quantile_sharp_law.lean), and [finite-law audit](quantile_optimality.lean). Their corresponding log files and the status record retain source, compiler and object identities.

## Checked conclusion

For every real factor $k$, the universal comparison on the original selection functional holds exactly when $c_{\rm vec}\le k$. The same equivalence holds when the gap law is restricted to finite support. The coefficient $c_{\rm vec}$ is the unique scalar root in $(\sqrt2,31/20)$.

For every smaller factor, the construction gives a positive-gap finite probability law, $0<\rho\le1/4$ and $B>0$, for which that factor fails. The proof checks probability mass, support, fractional quantile splitting, core entropy, feasible selection prices, clipping and the limit. It covers zero vector coordinates and an empty family above the boundary.

The all-law upper proof handles arbitrary support, countably many tail bands, infinite selected entropy, fractional atoms, saturation and the selection infimum.

## Reproduce

Run the three tools from the repository root.

```sh
python tools/verify_optimal_quantile.py
python tools/verify_quantile_sharp_law.py
python tools/verify_quantile_optimality.py
```

The separate exact-arithmetic certificate was rerun successfully with 85 certified cells and maximum depth 21. It certifies
$1.462554551279<c_*<1.462554551280$. The decimal bracket has rational verification outside the Lean audits.

Earlier checkpoints are preserved in the [finite-vector](../optimal-quantile-finite-20261105/README.md), [series](../optimal-quantile-series-20261105/README.md), [root](../optimal-quantile-root-20261105/README.md), [Lipschitz](../quantile-lipschitz-20261105/README.md), [core reduction](../quantile-core-reduction-20261105/README.md), [all-law upper](../sharp-quantile-upper-20261105/README.md), and [finite-family](../finite-law-family-20261105/README.md) records.

Independent specialist review remains unverified.
