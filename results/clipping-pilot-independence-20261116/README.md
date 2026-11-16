# Clipping and independence from the paid pilot

[Clipping.lean](../../lean/ThresholdHC/RobustContinuation/Clipping.lean)
clips an adaptive estimator's output to `[0,M]` for `M >= 0`, while retaining
its private seed law, policy, original experiment, expected work and pathwise
caps. For a target in that interval, squared risk cannot increase, even if
the original risk is infinite. Clipping at `rho` therefore preserves the
named reference plan's budget and rare-prior RMS risk certificate. The CDF
planner also supplies one bounded-output estimator fixed before the true
law, with the same rate for every CDF-dominated true law. Rarity remains a
global bound on the positive fraction; no pointwise sign bound is added.

[PilotIndependence.lean](../../lean/ThresholdHC/RobustContinuation/PilotIndependence.lean)
proves the joint law of a finite adaptive pilot word on labels `Nat.pair 0 i`
and the complete production input on labels `Nat.pair 1 i`, including the
private seed. The pilot reader is deterministic given its flips and does
not inspect that seed. Each coin retains its entire persistent tape under
the original population law, including gap-dependent sign allocation.
Restricting to any pilot word multiplies the production input law by that
word's probability, including null histories. For a positive-probability
word, normalizing the restriction restores the original production law.

A family of private seeds indexed by possible pilot histories permits
different seed spaces and distributions for different histories. After
conditioning, the selected seed and fresh production stream have exactly
the selected product law. The continuation output can depend on the pilot
through its selected learned law; the input independence does not assert
that the selected output itself is independent of the pilot.

The installed multi-depth pilot satisfies the joint and conditional input
identities. The actual paid chronological pilot prefix is identified jointly
with both reported endpoints in the original hidden-gap experiment. For
each positive-probability pilot word, the conditional selected interval has
the law obtained by fixing that learned law and running the continuation
with its original independent seed and fresh production stream. No risk or
coverage premise is assumed for these execution identities.

Conditional coverage and the reported radius of a physical-cap median,
the concrete robust continuation's statistical connection to the paid
stage, finite-law enclosures and the complete all-budget controller remain
open. These results advance [#82](https://github.com/davidiach/adaptive-threshold-estimation/issues/82).
They do not verify Python execution or its PRNG, and no numerical experiment
was run for this record.

At [proof checkpoint 8c7cfd4](https://github.com/davidiach/adaptive-threshold-estimation/commit/8c7cfd429ca61c6fba72100696e1bced3b7a333b),
both modules built from source on Windows with pinned Lean `v4.36.0-rc1`
and Mathlib revision `9bdd0bc71aaae0fd83889f9aacd70c32fccd1bcd`.
Lake checked source hashes when reusing its dependency cache. All
709 pre-existing project sources in the 711-module union import
closure are byte-identical to base checkpoint `a85788c9e731d0237e8f06837545fbd78e4c61e3`.
Specifications, package manifests and historical evidence are unchanged.

The [independent exact statements](clipping_pilot.lean) passed with
[26 transitive axiom reports](clipping_pilot.log), covering the full new
estimator definition and all 25 theorems. Only `propext`, `Classical.choice`
and `Quot.sound` occur. Run
`python tools/verify_clipping_pilot_independence.py` to build and repeat
the audit. Its registry rejects unregistered declarations, substituted
restatements, incomplete reports and disallowed axioms. All 11 new verifier
regression tests passed.

The [local project audit input](project_closure.lean) and
[output](project_closure.log) cover exactly that 711-module closure:
9,017 constants, including 7,329 theorems, no declared axioms
and only the three allowed transitive axioms. Its 79 exported instances
have the required names, scope and priority. The closure includes
4 of the six registered orphan instances; the others' defining modules
are absent. All 1,608 covered definition fingerprints match the updated
lock. The canonical registration function added only
`ThresholdHC.RobustContinuation.clippedEstimator`; all 2,320 old entries
are unchanged, giving 2,321 in total. This is a scoped local audit. The
unchanged whole-project verifier and main-theorem kernel replay run
separately in CI.

[status.json](status.json) binds the proof checkpoint, compiler, source
closure and reports. Both saved Lean inputs can be replayed by piping
their UTF-8 text to `lake env lean -j1 --stdin` from `lean/` after building
the two modules. The source guard, all 246 hashes in 10 frozen/published
manifests, generated status/manuscript checks and whitespace check passed
locally. CI claims for a later PR head belong to that head's checks.
