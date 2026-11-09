# The arbitrary-law Ψ lower bound through the entropy-tail law

For a probability law $\mu$ on $(0,1/2]$, write $\Psi_{\mu,\rho}$ for the
variational modulus and $\mathcal K_{\mu,\rho}$ for the entropy-tail selection
functional, both as defined in the
[results guide](../../docs/RESULTS.md#rare-event-optimizer). The experiment is
the original observable one: budgets count actual flips, rarity is the global
bound $\int q\,d\mu\le\rho$, and magnitudes and signs stay hidden.

| Statement | Lean-checked guarantee |
|---|---|
| [Deterministic comparison](../../lean/ThresholdHC/PsiSelection/Comparison.lean) | $\Psi_{\mu,\rho}(B^{-1/2})\le\mathcal K_{\mu,\rho}(B)$ for every law, every real $\rho$ and every $B>0$. |
| [RMS lower bound](../../lean/ThresholdHC/PsiSelection/Full.lean) | $10^{-17}\,\Psi_{\mu,\rho}(B^{-1/2})\le R_{\mu,\rho}(B)$ for $0<\rho\le1/4$ and $B>0$. |
| [Confidence lower bound](../../lean/ThresholdHC/PsiSelection/Full.lean) | $10^{-17}\,\Psi_{\mu,\rho}\bigl(\sqrt{\log(1/\delta)/B}\bigr)\le r_{\mu,\rho}(B,\delta)$ for $0<\rho\le1/4$, $B>0$ and $0<\delta\le1/4$, under a uniform expected budget. |

The comparison splits the $\Psi$ integrand over a submeasure $\sigma\le\mu$
and its complement. On the complement, $\min\{v,h\sqrt v/d\}\le\min\{1,h/d\}$.
On $\sigma$, Cauchy–Schwarz gives
$\int h\sqrt v/d\,d\sigma\le h\sqrt{\int v\,d\sigma}\sqrt{\int d^{-2}\,d\sigma}\le h\sqrt{\rho\Gamma_\sigma}$.
The two statistical bounds then follow from the checked explicit
[entropy-tail law](../entropy-tail-explicit-20261104/README.md) and the
checked [general-law confidence coefficient](../entropy-confidence-20261105/README.md).

This is v6 Theorem A.5 with an explicit coefficient and every positive
budget. Its paper proof in Appendix A imports the single-coin Hellinger bound
of Lee and Valiant; this route does not. The paper proof is unchanged.
The bound is a lower bound only: the matching-$\Psi$ upper bound is false at
the critical quadratic law.

At [the proof checkpoint](https://github.com/davidiach/adaptive-threshold-estimation/commit/ce0897b178f3b14c5706b5273843aea7008157ac),
every project module was rebuilt from source on Linux with Lean
`v4.36.0-rc1` and the Mathlib cache for the pinned revision; the
[native record](status.json) lists the source hashes. The three new modules
compiled without warnings. [Six exact statements](psi_selection.lean) passed
with [ten transitive axiom reports](psi_selection.log), every declaration in
the directory included, using only `propext`, `Classical.choice` and
`Quot.sound`. Run `python tools/verify_psi_selection.py` with the pinned
toolchain. The specification was written together with the proof; its hash is
pinned in the verifier from this checkpoint on.
