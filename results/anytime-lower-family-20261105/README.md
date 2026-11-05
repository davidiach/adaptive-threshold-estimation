# Common prior families for time-uniform lower bounds

The proof checkpoint is [c9eda4a](https://github.com/davidiach/adaptive-threshold-estimation/commit/c9eda4a6f17a803a6bfff863e7a0a8afd9f16667).

The [native record](status.json) verifies 11 exact theorem statements and 11 transitive axiom reports. All three new compiler logs are empty. The dependency closure contains 331 project modules, including 328 reused dependencies with published matching object hashes. Source, direct dependency and object hashes were checked.

The [audit input](anytime_lower.lean) and [raw output](anytime_lower.log) cover information/work scaling along central prior segments, quarter-smoothing inversion, the physical prefix-work bound, admissibility and exact mean separation, and the quadratic KL bound for the original adaptive observable prefix.

The same family works at every prefix length and for every adaptive controller and independent private seed. All conclusions retain the original gap-law and conditional-sign model.

At the proof checkpoint, run `python tools/verify_anytime_lower.py` to reproduce these 11 statements. Later versions of that command add posterior-information statements.

This record covers the information bounds. The sequential testing argument and asymptotic lower bounds in the [research note](../../docs/TIME_UNIFORM_LOWER.md) have paper-proof status.
