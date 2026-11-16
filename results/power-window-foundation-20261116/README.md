# Power-law quantile split and core cost

For every exact-CDF power law with exponent `alpha > 0`, scale
`0 < a <= 1/2` and `0 < rho < 1`, Lean identifies the actual lower
quantile measure and its complementary core by transporting a uniform
variable through the power quantile map. No density or quantile-split
identity is assumed. The core has inverse-square cost

`a^2 A_core = Phi_alpha(rho)`.

The closed formula is `log(1/rho)` at exponent two and
`alpha (1-rho^(1-2/alpha))/(alpha-2)` otherwise. These statements cover
arbitrary scale `a` and all positive exponents, so include the cost part
of v6 Lemma 14.12.

The [specification](../../lean/ThresholdHC/PowerWindow/Specification.lean)
was committed at `ced5fcb` before the proofs. The
[proof checkpoint](https://github.com/davidiach/adaptive-threshold-estimation/commit/ddb8872d91d185ae7e3acee5a9f554c97557abdf)
contains the completed foundation. The [exact audit input](audit.lean)
checks eight statements: the named Phi target, its independent restatement,
the tail and core measures, the actual core cost and the exponent-two
specialization, and the conditional RMS/confidence implications of the
uniform quantile comparison. The [report](audit.log) audits all 27 declarations with
only `propext`, `Classical.choice` and `Quot.sound`.
[Source hashes and scope](status.json) identify this local audit.

Run `python tools/verify_power_window.py`. Its six regression tests cover
the statement hash, target and module registry, proof escapes, unreadable
declarations and the completeness/soundness of axiom reports. CI runs both.

The audit **does not prove** `PowerCoreStatement`, `PowerQuantileStatement`,
`PowerRiskStatement` or `PowerConfidenceStatement`. These are frozen target
definitions, not theorem declarations. The remaining work is the normalized
band-cost entropy estimate with constants `1/2` and `3.83`, including the
band offset from arbitrary `a`, followed by the deterministic uniform
quantile comparison. `power_risk_of_quantile` and
`power_confidence_of_quantile` now prove that this comparison implies the
full RMS and both confidence targets. They retain the unproved quantile
statement as an explicit premise. The intended RMS coefficients are `10^-17/sqrt(2)`
and `60002`, compared with the paper's `10^-18` and `66000`; the confidence
upper coefficient is the same `1500000`. The statistical composition with these coefficients is checked; the
unconditional bounds remain targets because the quantile premise is unproved.

Corollary 14.14 and the asymptotic interpretation in Remark 14.15 stay as
paper results outside the current formal targets. Issue #100 remains open.
