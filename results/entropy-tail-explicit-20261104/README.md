# Explicit general-law entropy-tail comparison

Lean verifies $10^{-17}\mathcal K_{\mu,\rho}(B)\le R_{\mu,\rho}(B)\le28000\mathcal K_{\mu,\rho}(B)$
for every gap probability law on $(0,1/2]$, $0<\rho\le1/4$ and $B>0$.
The same lower coefficient applies to the closed quantile value $Q$.
The [statement](https://github.com/davidiach/adaptive-threshold-estimation/blob/b05fead1e1a672e9142a5e26868e30891aa91382/lean/ThresholdHC/EntropyTailSharp/Specification.lean)
was committed before the proof. The [final declarations](https://github.com/davidiach/adaptive-threshold-estimation/blob/8a701c8db6c42930ad2a187f3d895ca55265afd6/lean/ThresholdHC/EntropyTailSharp/Full.lean)
also check the literal coefficients $10^{-17}$ and $33000$ from Appendix E
and the converse for each estimator satisfying the uniform expected-flip budget.

The tail argument integrates bounded prefix likelihoods and posterior energy
against the original law, including its fractional quantile atom. On the core,
the maximum of the three gate estimates is at most $4096e^{48}$.
This gives certificate variance coefficient $16384e^{48}$ and hence packing
cost $M_B\le3\cdot10^{16}R$. The label floor and the tail cover the other
cases. Combining $T_h\le32R$ and $\mathcal K\le Q\le T_h+2M_B$ yields
the stated lower coefficient.

The [native record](status.json) binds the proof sources, compiler, commands,
cached inputs and rebuilt native artifacts. The Windows run rebuilt the 10
sharpened-proof modules and 11 imported finite-quantile modules in an isolated
output directory. The other 496 project sources and native inputs matched the
published audit records identified in the JSON. All 22 compiler commands
exited successfully. The [type checks](../../lean/ThresholdHC/EntropyTailSharp/Audit.lean)
and the [final compiler input](ExactAudit.lean) check six exact statements.
All 18 declarations use only the permitted standard axioms, as recorded in the
[final compiler log](22.log). The source and artifact hashes were rechecked
after compilation. This run used the pinned external dependency cache.

Reproduce the checks from the repository root with Lake and the pinned toolchain.

```sh
python tools/verify_entropy_tail_sharp.py
```
