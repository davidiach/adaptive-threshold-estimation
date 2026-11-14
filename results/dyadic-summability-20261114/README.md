# Convergence of the dyadic series of targets H3 and H4

The frozen targets `Targets.dyadic_sum_v1` and `Targets.dyadic_sum_v2` of
[Statements.lean](../../lean/ThresholdHC/Statements.lean) bound `∑'` sums:
$\sum_k 2^k e^{-b2^k}\le2/b$ and $\sum_k 4^k e^{-b2^k}\le8/(3b^2)$ for $b>0$.
In Mathlib the sum of a series that does not converge is $0$, so those
targets alone do not say that the series converge. The specification file is
frozen. [DyadicSummable.lean](../../lean/ThresholdHC/Proofs/DyadicSummable.lean)
adds the convergence, from bounds on the partial sums.

| Statement | Lean-checked guarantee |
|---|---|
| H3 partial sums | For $b>0$ and every $m$, $\sum_{k<m}2^k e^{-b2^k}\le2/b$. |
| H3 converges | For $b>0$ the series has a sum $s$, in the sense of `HasSum`, and $s\le2/b$. |
| H4 terms | $4^k e^{-b2^k}\le(2/b)\,2^k e^{-(b/2)2^k}$, since $xe^{-x}\le1$. |
| H4 partial sums | For $b>0$ and every $m$, $\sum_{k<m}4^k e^{-b2^k}\le8/b^2$. |
| H4 converges | For $b>0$ the series has a sum $s$, in the sense of `HasSum`, and $s\le8/(3b^2)$, the frozen bound. |

The audit also restates the two frozen targets by `Iff.rfl`, so the sums it
proves convergent are the ones they bound. The frozen targets themselves are
unchanged, and nothing previously claimed was false: the series always
converged. These theorems make the convergence available to later proofs.

At [the proof checkpoint](https://github.com/davidiach/adaptive-threshold-estimation/commit/b4a88c43a7ad7f4b68dfeb78f69d205102e7e359),
the new module was built from source on Linux with Lean `v4.36.0-rc1` against
the Mathlib cache for the pinned revision, and compiled without warnings.
[7 exact statements](dyadic_summability.lean), five for the module and two
for the frozen targets, passed with
[5 transitive axiom reports](dyadic_summability.log), one for each
declaration of the module, using only `propext`, `Classical.choice` and
`Quot.sound`. The [native record](status.json) lists the source hash of every
project module in the import closure. Its base checkpoint is `b471d6b`.

Run `python tools/verify_dyadic_summability.py` with the pinned toolchain.
