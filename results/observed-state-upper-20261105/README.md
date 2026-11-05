# Fresh-state upper bounds and complete observed-state rates

The [general upper families](../../lean/ThresholdHC/ContinuousObserved/Upper.lean)
and [uniform-gap specialization](../../lean/ThresholdHC/ContinuousObserved/UniformUpper.lean)
complete the observed-state complexity results together with the preceding
lower-bound and regularity audits. The proof checkpoint is
[d9146cc](https://github.com/davidiach/adaptive-threshold-estimation/commit/d9146cc9ac90783b10756dcd96223eff9b61438f).
Source and compiled-object identities are in [status.json](status.json).

## Audit scope

- Twenty-one independent exact-type checks and 42 transitive axiom reports passed.
- All 13 new modules compiled natively with the pinned Lean toolchain and empty compiler logs.
- The dependency closure contains 325 project modules. All 312 inherited objects match previously published hashes and every inherited source matches the base checkpoint.
- The audit identifies the conditional sign probability, parameter law and complete observable transcript.
- Actual expected work, squared risk, RMS risk and failure probabilities transfer exactly, including unbounded stopping and infinite risk.
- Universal selected-state families attain coefficients 512 for RMS and 8192 for confidence on the respective clipped moduli.
- For uniform gaps on \((0,1/4]\) and \(0<\varepsilon\le e^{-16}\), both guarantees use at most \(131072^2\varepsilon^{-2}\log^2(1/\varepsilon)\log16\) expected observations. The confidence failure probability is \(1/16\).

Complete source and object hashes, exact compiler inputs, compiler output
and audit reports are retained here. The allowed axiom set is `propext`, `Classical.choice`, and `Quot.sound`.

The [proof guide](../../docs/OBSERVED_UPPER.md) records the scope.
Run `python tools/verify_observed_upper.py` for a fresh audit.
[Appendix Z](../../paper/v6/appendix-observed-upper.tex) presents the proof.
The [published manuscript](../../paper/v6/builds/observed-state-upper-20261105.pdf)
has 154 pages. Its [build manifest](../../paper/v6/builds/observed-state-upper-20261105.json)
records byte-identical independent builds, source identities and visual checks.

CI on later publication commits is reported on
[PR #55](https://github.com/davidiach/adaptive-threshold-estimation/pull/55).
