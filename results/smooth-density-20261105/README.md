# Smooth-density robustness

The [full theorem](../../lean/ThresholdHC/SmoothDensity/Full.lean) proves both
expected-complexity bounds and the uniform unbiased impossibility in the
original randomized adaptive experiment.

The proof checkpoint is
[8e42a99](https://github.com/davidiach/adaptive-threshold-estimation/commit/8e42a99a49dcd4af8bdaaf17a6ea1c398f34b03b).
The source and compiled-object identities are in [status.json](status.json).

## Audit scope

- Fifteen independent exact-type checks and 46 transitive axiom reports passed.
- All 16 new modules compiled natively with the pinned Lean toolchain and empty compiler logs.
- The dependency closure contains 269 project modules. All 253 inherited compiled objects match previously published hashes.
- The full result uses the original observation law, expected physical flips, and threshold target.
- The upper family is selected before the density. The lower bound and unbiased impossibility allow arbitrary randomized adaptive policies.
- The smoothness bound is uniform through each fixed finite derivative order. The constructed densities are individually infinitely differentiable.

The complete source and object hashes, exact compiler inputs, compiler output,
and audit reports are retained here. The allowed axiom set is
`propext`, `Classical.choice`, and `Quot.sound`.

The [proof guide](../../docs/SMOOTH_DENSITY.md) records the module map.
Run `python tools/verify_smooth_density.py` for a fresh audit.
[Appendix W](../../paper/v6/appendix-smooth-density.tex) presents the argument.
The [published manuscript](../../paper/v6/builds/smooth-density-20261105.pdf)
has 149 pages. Its [build manifest](../../paper/v6/builds/smooth-density-20261105.json)
records byte-identical independent builds, source identities and visual checks.

CI on later publication commits is reported on
[PR #52](https://github.com/davidiach/adaptive-threshold-estimation/pull/52).
