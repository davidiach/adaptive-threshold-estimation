# Continuous-magnitude observed-state lower bounds

The [confidence theorem](../../lean/ThresholdHC/ContinuousObserved/UniformLower.lean),
[RMS theorem](../../lean/ThresholdHC/ContinuousObserved/UniformRMSLower.lean), and
[regularity theorem](../../lean/ThresholdHC/ContinuousObserved/Regularity.lean)
apply to the actual selected-state experiment with an exactly uniform gap law
on \((0,1/4]\). The proof checkpoint is
[10fc9a9](https://github.com/davidiach/adaptive-threshold-estimation/commit/10fc9a912ff5ecd9b1125bea47daa4821df6fd79).
Source and compiled-object identities are in [status.json](status.json).

## Audit scope

- Thirty-four independent exact-type checks and 87 transitive axiom reports passed.
- All 26 new modules compiled natively with the pinned Lean toolchain and empty compiler logs.
- The dependency closure contains 322 project modules. All 296 inherited objects match previously published hashes and every inherited source matches the base checkpoint.
- The lower bounds permit arbitrary measurable point queries, revisits, interleaving, private randomness and unbounded stopping.
- The complete transcript law is derived from the ordinary fresh Bernoulli rule at each selected state.
- The audit identifies actual work, the conditional mean, threshold target and exact gap law.
- The normalized conditional magnitude has an explicit density bounded by two. Every normalized conditional central moment of real order \(q\ge0\) is at most \(3^{q/2}\).
- The positive confidence coefficient on \(\varepsilon^{-2}\log^2(1/\varepsilon)\) is \(c=225\operatorname{kl}(7/8,1/8)/(128\cdot64^2)\). The RMS coefficient is \(c/64\).

Complete source and object hashes, exact compiler inputs, compiler output
and audit reports are retained here. The allowed axiom set is `propext`, `Classical.choice`, and `Quot.sound`.
The finite replication count uses the second-moment construction.

The [proof guide](../../docs/CONTINUOUS_OBSERVED.md) records the scope and module map.
Run `python tools/verify_continuous_observed.py` for a fresh audit.
[Appendix Y](../../paper/v6/appendix-continuous-observed.tex) presents the proof.
The [published manuscript](../../paper/v6/builds/continuous-observed-lower-20261105.pdf)
has 152 pages. Its [build manifest](../../paper/v6/builds/continuous-observed-lower-20261105.json)
records byte-identical independent builds, source identities and visual checks.

The matching upper rate retains its paper proof. Its formal continuation
transfers the existing population estimator to fresh uniform outer sampling.

CI on later publication commits is reported on
[PR #54](https://github.com/davidiach/adaptive-threshold-estimation/pull/54).
