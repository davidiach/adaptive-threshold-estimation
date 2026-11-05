# All-law quantile comparison at the exact scalar root

Proof checkpoint [6325369](https://github.com/davidiach/adaptive-threshold-estimation/commit/6325369d250e370a5c433addbae142fcd600815b).

The [status record](status.json) identifies 84 independently restated theorem types and 84 transitive axiom reports. The closure contains 95 project modules, with 40 compiled modules from this PR and 55 reused dependencies having previously published matching object hashes. All 40 compiler logs are empty. No unmatched artifacts remain.

The [audit input](quantile_sharp_law.lean) and [raw output](quantile_sharp_law.log) are preserved with source, compiler and object identities. The scalar-root characterization also has its separate [54-statement record](../optimal-quantile-root-20261105/README.md).

For every positive-gap probability law, $0<\rho\le1/4$ and $B>0$, Lean checks
$$
\mathcal K_\mu(\rho,B)\le Q_\mu(\rho,B)
\le c_{\rm vec}\mathcal K_\mu(\rho,B),
$$
using the original selection functional. The corresponding mathematical selection value comparison holds throughout $0<\rho\le1$.

The coefficient is the exact unique scalar root. The proof handles arbitrary support, fractional quantile atoms, countably many tail bands, infinite selected entropy, saturation and the selection infimum. It includes the finite-core reduction, entropy Lipschitz bound, countable tail merging, Cauchy moment bound, dyadic work bound and normalization.

Run `python tools/verify_quantile_sharp_law.py` for the exact statements and transitive axiom reports.

Finite-law realization, which proves that no smaller factor works over gap laws, remains a paper proof. The tight decimal bracket retains its separate exact-arithmetic certificate.
