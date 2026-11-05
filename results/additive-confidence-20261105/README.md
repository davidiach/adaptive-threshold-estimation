# Fractional-submeasure additive confidence localization

This record verifies the additive confidence lower bound for finite
overlapping submeasures in the original hidden-gap observation model.

The proof checkpoint is
`b64f44f43aa0bb2c43f83ad428a4bc9627a5f773`.
It extends the common-pair checkpoint
`52bf67c8b7f1e7dd85507e9a95aeeac8c5ee6e8b`.

## Checked conclusion

For finitely many nonzero $\sigma_i$ with $\sum_i\sigma_i\le\mu$,
write $\tau_i=\sigma_i((0,1/2])$ and $\nu_i=\sigma_i/\tau_i$.
Suppose each $\nu_i$ has a variance–null-work obstruction
$(b_i,J_i)$ on its half-prior class with $0<r_i\le1/4$,
$b_i,J_i>0$, and $\sum_i\tau_i r_i\le\rho$.
Then, for $B>0$ and $0<\delta\le1/4$,

\[
r_{\rm exp}(B,\delta)\ge
\frac1{128}\sum_i\tau_i
\min\{b_i,\sqrt{J_i\log(1/\delta)/B}\}.
\]

The theorem covers each observable estimator with uniform expected
work at most $B$ and uniform failure probability at most $\delta$,
as well as the minimax infimum. The component supports may overlap.

## Native evidence

- 41 exact theorem statements and 41 transitive axiom reports.
- 356 project modules in the dependency closure.
- 15 newly compiled modules with empty diagnostic logs.
- 341 inherited compiled modules matched to their published hashes and unchanged source identities.
- Source, direct-dependency object and output-object hashes checked together.
- Only `propext`, `Classical.choice` and `Quot.sound` appear in the reports.
- The source guard checked all 980 Lean sources, including the new modules.
- The frozen-source guard and 15 existing verifier regression tests passed.

The [status record](status.json) identifies every source and compiled
dependency, the compiler version, and the [exact input](additive_confidence.lean)
and [native log](additive_confidence.log). Logs 01–15 correspond to the
fresh modules in the status record.

The reused dependencies include the common-pair construction,
finite sufficient-statistic identity and original stopped KL/testing
theorems. Their source and object hashes were checked against the
records listed in the status file.

## Construction and scope

The proof normalizes the submeasures and keeps their exact residual.
It constructs global half-priors using Radon–Nikodym densities,
checks the positive and negative sign measures, and derives the
parameter, tape and finite-statistic mixture laws. The common residual
cancels in the Hellinger comparison. Weighted component work is
bounded by the actual original all-negative work.

The [proof map](../../docs/ADDITIVE_CONFIDENCE.md) gives the module
dependencies. The [full formal statement](../../lean/ThresholdHC/AdditiveConfidence/Full.lean)
retains the conditional variance–null-work premises explicitly.

The general-law entropy-packing application and the sharp
quantile-factor characterization retain separate paper proofs.
The previously checked general-law confidence coefficient remains
$10^{-17}/30$. The absence of human specialist review remains a
project limitation.

## Manuscript

The [updated manuscript](../../paper/v6/builds/additive-confidence-20261105.pdf)
contains the construction and proof. Its [build record](../../paper/v6/builds/additive-confidence-20261105.json)
records reproducible builds, source identities and visual checks.
The 160-page PDF has two byte-identical offline builds. All seven
changed pages were inspected at high resolution, with no new layout
defects. It contains 366 labels and 29 citations. The 12 manuscript
regression tests and 1170 file-link checks passed.
All earlier records and PDFs remain preserved.
