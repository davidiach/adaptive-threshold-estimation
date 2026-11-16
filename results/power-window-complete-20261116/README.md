# Uniform power-law entropy and deterministic quantile comparison

The [proof checkpoint](https://github.com/davidiach/adaptive-threshold-estimation/commit/6965262b95490eeabf5d5158ad55e0393027f28c)
proves all five statements in the unchanged
[specification](../../lean/ThresholdHC/PowerWindow/Specification.lean).
For an exact-CDF power law, `0 < alpha <= 4`, `0 < a <= 1/2` and
`0 < rho < 1`, the actual quantile core satisfies

`a^2 A_core = Phi_alpha(rho)` and
`(1/2)(1 + log N_alpha) <= 1 + E_core <= 3.83(1 + log N_alpha)`.

This includes exponent two and arbitrary scale; no dyadic alignment,
density formula or entropy bound is an additional premise. The proof
transports the actual core through its power quantile, bounds every
normalized band cost, and uses a finite probability vector with labels
measured from either endpoint. Its weighted first-moment bound gives the
geometric entropy estimate uniformly near exponent two.

For `0 < rho <= 1/4` and every positive budget, the deterministic comparison
is `R_alpha/sqrt(2) <= Q <= 2 R_alpha`. The full RMS and both confidence
targets now follow without an unproved quantile premise. The RMS coefficients
are `10^-17/sqrt(2)` and `60002`; the confidence lower coefficient is
`10^-17/sqrt(2)` and its upper coefficient is `1500000`. The paper's
`10^-18` and `66000` are weaker; its confidence upper coefficient agrees.

The [audit input](audit.lean) checks 16 exact statements, including
independent restatements of all five targets. The [audit report](audit.log)
checks all 78 declarations in the registered modules using only `propext`,
`Classical.choice` and `Quot.sound`. [Source identities](status.json)
pin this local validation to the proof checkpoint. Run
`python tools/verify_power_window.py`; its six guard tests reject changed
specifications, omitted modules or targets, proof escapes, unreadable
declarations and incomplete or unsound axiom reports.

Corollary 14.14 and the asymptotic interpretation in Remark 14.15 remain
paper results outside the formal targets and have a separate status entry.
The earlier foundation record, all earlier PDFs and the floating-point
numerical script retain their original bytes and verification scope.
This record describes local proof verification; CI evidence must identify
the actual reviewed PR head separately.
