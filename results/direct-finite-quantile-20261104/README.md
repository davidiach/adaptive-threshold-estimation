# Explicit finite-law quantile bounds

For every finite-support gap law, $0<\rho\le1/4$ and $B>0$, the original
observable minimax risk satisfies $10^{-20}Q(B)\le R(B)\le30001Q(B)$.
The [finite-law target](https://github.com/davidiach/adaptive-threshold-estimation/blob/5557334/lean/ThresholdHC/FiniteQuantile/Specification.lean)
was committed before the proof. The [proof checkpoint](https://github.com/davidiach/adaptive-threshold-estimation/tree/fc61852123b37c723bbb671d0b4ed294d3b6ee06/lean/ThresholdHC/FiniteQuantile)
also includes one budget-feasible estimator attaining the stated upper bound
uniformly over all rare priors, and the matching converse for every feasible estimator.

The direct lower proof uses a fractional quantile-tail pair with separation
$T_h/8$ and risk floor $T_h/32$. It filters the dyadic core and spends the
full rarity budget in proportion to the entropy of the retained groups.
This gives the paper's lower coefficient with a different choice of filter
and allocation. For the estimator witness, the established upper bound of
$28000Q$ leaves enough slack to obtain one feasible estimator at $30001Q$.

The [status record](status.json) identifies the source bytes, toolchain,
native commands and 43 transitive axiom reports. All 16 new modules, including
the [exact-type audit](ExactAudit.lean), were rebuilt serially. Its seven
examples include the two-sided bound, estimator witness and converse.
Only `propext`, `Classical.choice` and `Quot.sound` occur. The numbered
logs correspond to the commands in the status record. The [last log](16.log)
contains the axiom reports. The dependency scan excludes the general statistical
entropy-tail lower theorem and the general-law closed-quantile corollary.

This local run reused 494 project dependencies. Each source and all
494 recorded native artifact hashes matched entries in the merged
[entropy-tail](../entropy-tail-complete-20261101/README.md) or
[closed-quantile](../closed-quantile-law-20261101/README.md) records. Their
identities and the protected sources were checked before and after the build.
The [reproduction command](../../tools/verify_finite_quantile.py)
uses Lake to build the audit from current sources:

```sh
python tools/verify_finite_quantile.py
```
