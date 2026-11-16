# Conditional capped median and paid-stage coverage

[ReferenceBase.lean](../../lean/ThresholdHC/RobustContinuation/ReferenceBase.lean)
selects a clipped estimator from the reference law alone. For every probability
law `alpha` on `[0,1/2]`, `0 < rho <= 1/4` and `b > 0`, it has expected work
at most `b` and RMS risk at most `C_0 K_alpha(b)` under every CDF-dominated
true law and globally rare sign allocation. When the zero atom is at least
`rho`, `K_alpha = rho` and the constant `rho/2` supplies the fallback.
The choice is fixed before the true gap law and sign law.

[CappedMedian.lean](../../lean/ThresholdHC/RobustContinuation/CappedMedian.lean)
instantiates the existing physical-cap median with `2m+1` copies, per-copy
reservation `floor(B/(2m+1))`, and base budget `b = B/[8(2m+1)]`. The total
continuation cap is at most `floor(B)`, including zero reservations and
timed-out copies. Failure at radius `sqrt(8) C_0 K_alpha(b)` is at most
`(3/4)^m/2`; the radius is at most `6 C_0 K_alpha(b)`. The word reader is
identified with the actual capped-median output. A product of private seed
laws indexed by reference law supplies the correct selected seed law.

[PaidCoverage.lean](../../lean/ThresholdHC/RobustContinuation/PaidCoverage.lean)
identifies restrictions and normalized conditioning on the paid chronological
pilot prefix in the original hidden-gap experiment, jointly with both
reported endpoints. Restrictions cover null histories; normalized
conditioning requires positive probability. Integrating fixed-history
coverage bounds charges invalid envelopes at their actual probability.

[PaidMedian.lean](../../lean/ThresholdHC/RobustContinuation/PaidMedian.lean)
installs the concrete multi-depth pilot and median continuation. Its interval
has the selected capped-median law after conditioning on a valid pilot
prefix. For `0 < rho <= 1/4`, `B > 0`, `J >= 1`, `k > 0`, `epsilon > 0`,
`k >= 8 log(2J/epsilon)`, and `m = ceil(4 log(1/delta))` with `delta > 0`,
`paidMedianStage_at_level` proves failure at most `epsilon + delta` under
the original experiment. Both endpoints have the unconditional cap
`k * pilotSpan J + floor(B)`. The reported-radius identity holds on every
input, including failed pilot and continuation paths. The final stage
theorem assumes no base-risk or continuation-coverage oracle.

This advances [#82](https://github.com/davidiach/adaptive-threshold-estimation/issues/82).
It is a classical formal construction using exact reference-law functionals.
It does not compute finite-law numerical enclosures or verify Python execution
or its PRNG. The full all-budget controller, fresh stages, nested intervals,
simultaneous coverage and eventual oracle width remain separate obligations.
No numerical experiment was run for this record.

At [proof checkpoint 392d0ec](https://github.com/davidiach/adaptive-threshold-estimation/commit/392d0ecb88b6cb7449fbbb4f52ac9a4e803694a0),
all four modules built from source on Windows with pinned Lean `v4.36.0-rc1`
and Mathlib revision `9bdd0bc71aaae0fd83889f9aacd70c32fccd1bcd`.
Lake checked source hashes before reusing cached dependencies. All 711
pre-existing project sources in the 715-module union import closure are
byte-identical to base checkpoint `d2da59acc8c40e978c3b8387d72cafd9fd67aa0f`. Frozen specifications,
package manifests and published historical evidence are unchanged.

The [independent statements](paid_median.lean) and [axiom reports](paid_median.log)
check all 48 declarations: 13 definitions and 35 theorems. Only `propext`,
`Classical.choice` and `Quot.sound` occur. Run
`python tools/verify_paid_median.py` to build and repeat the audit. Its
registry rejects unregistered declarations, substituted restatements,
incomplete reports and disallowed axioms. All 10 verifier regression tests
passed, along with the shared audit, source-guard and project-audit regressions.

The [local project audit](project_closure.lean) and [output](project_closure.log)
cover 715 modules, 9,088 constants, 7,387 theorems and 80 exported instances.
There are no declared axioms, new orphan instances or disallowed transitive
axioms. Four of the six registered orphan instances occur in this closure.
All 1,621 covered definition fingerprints match the updated lock. The
canonical registration function appended 13 definitions; all 2,321 old
entries are unchanged, giving 2,334 in total. This is a scoped local audit.
The unchanged whole-project audit and main-theorem kernel replay run
separately in CI.

[status.json](status.json) binds the proof checkpoint, compiler, source
closure and reports. Both saved Lean inputs can be replayed by piping
their UTF-8 text to `lake env lean -j1 --stdin` from `lean/` after building
the four modules. The source guard, all 246 hashes in 10 frozen/published
manifests, generated status/manuscript checks and whitespace check passed
locally. CI claims for a later PR head belong to that head's checks.
