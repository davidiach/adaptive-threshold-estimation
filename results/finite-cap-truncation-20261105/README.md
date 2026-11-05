# Ordinary finite-cap convergence: native Lean verification

The source checkpoint is `2dc570206292ce88a0636d82e9bdfff54663e80d`.
The [record](status.json) identifies all 380 project sources in the dependency
closure, five fresh native compilations with empty logs, and 375 unchanged
compiled dependencies whose hashes match previously published records.

All ten independently restated theorem types and transitive axiom reports
passed. Only standard Lean axioms occur. The
[exact audit input](finite_cap_truncation.lean) and
[axiom reports](finite_cap_truncation.log) are preserved here.

## Result

For every probability law on positive gaps and every integer $N\ge1$,
$$
 P_\infty(B)\le P_N(B)\le
 \left(1+\sqrt{\frac{B}{N+1}}\right)P_\infty(B).
$$
The formal statement allows every real rarity parameter and $B\ge0$.
In the statistical domain $0<\rho\le1/2$, $B>0$, the risk corollary is
$$
 R(B)\le P_N(B)\le8\left(1+\sqrt{\frac{B}{N+1}}\right)R(B).
$$
Thus $N+1\ge B$ suffices for $P_N\le16R$.

The proof preserves the old stopped outputs through depth $N$ and forces
remaining paths to stop with output zero. It proves the capped flow is
feasible, work and second moments decrease, discarded stop mass is at most
$B/(N+1)$, and discarded mean is at most $\sqrt{BV/(N+1)}$. Taking the
infimum over feasible certificates and then larger caps gives the optimized
comparison.

## Scope

This improves the ordinary upper program's sufficient relative rate from
a cube root to a square root. It does not prove this exponent optimal,
a matching convergence lower bound, or a square-root rate for the genie
lower program. The sufficient cap $N+1\ge B$ gives the risk bound directly;
it does not assert the genie criterion $P_N\le2G_N$ at that cap.

The theorem uses the original count-flow certificate and program values.
There is no finite-support, lower-gap, finite-inverse-moment, or
unit-root-intensity assumption. Python execution and numerical conic solvers
are not verified here. No independent specialist review is claimed.

## Replay

With the pinned Lean toolchain and Mathlib cache:

```sh
python tools/verify_finite_cap_truncation.py
```

The publication uses the native compiler with `-j1` and checks source,
direct-dependency and compiled-object hashes before cache reuse. All five
fresh compiler logs are empty. The proof-escape scanner and its three
regressions, frozen-source verification, and whitespace checks passed.
CI status is separate and belongs to the corresponding GitHub commit.

