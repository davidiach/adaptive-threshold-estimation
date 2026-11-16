# Robust continuation from CDF domination

This record supplies the coupling required by the
[robust reference-plan theorem](../robust-plan-20261114/README.md).
For a probability law `eta` on positive gaps, let
`alpha = z_0 delta_0 + (1 - z_0) eta`. If `0 <= z_0 <= 1` and
`F_mu <= F_alpha`,
[CDFBridge.lean](../../lean/ThresholdHC/RobustContinuation/CDFBridge.lean)
constructs an increasing finite coupling `pi` on positive gaps with first
marginal `(1 - z_0) eta`. Its second marginal and a remainder `mu_0` sum to
the true probability law `mu`, and the remainder has mass exactly `z_0`.
The construction works for arbitrary positive-part reference laws,
including finite learned laws and the endpoint cases `z_0 = 0, 1`.

The common-uniform CDF coupling is already checked. A bounded-density lift
selects its positive-reference part; pulling it back to `Gap x Gap` gives
`pi`, and measure subtraction gives `mu_0`. For every original measurable
sign law `q`, its integral through the two parts equals its original total
positive fraction. If that fraction is at most `rho`, the integral over
the coupled part is at most `rho`. The argument uses `q` at the true gap;
it does not construct a conditional reference-sign allocation.

The named enclosed and searched reference plans now satisfy their expected
budget and root-mean-square risk certificates directly under CDF
domination. Their unresolved-mass condition is
`zeta(univ) + z_0 <= E.unresolved`. The rate theorem has the quantifier
order: for each reference, `0 <= z_0 < rho <= 1/4` and `B > 0`, there is
one estimator such that for every CDF-dominated true law its expected work
is at most `B` and its root-mean-square risk is at most `C_0 K_alpha(B)`.
Here `C_0 = 1 + 4 max(4096, 8 sqrt(2) 28000)` and `K_alpha` is the checked
zero-atom selection functional. The estimator is fixed before the true
law is chosen. The existential rate statement retains its large constant;
the named plan certificates remain the bounds useful at smaller budgets.

This component does not prove clipping, independence from each finite
pilot history, conditional coverage of the physical-cap median, or the
connection to the observable paid stage. It does not compute finite-law
enclosures, verify the Python estimator or its PRNG, or prove the complete
all-budget controller. In particular, it advances rather than completes
[#82](https://github.com/davidiach/adaptive-threshold-estimation/issues/82).

At [proof checkpoint 7b00fe0](https://github.com/davidiach/adaptive-threshold-estimation/commit/7b00fe0094a72dfe34d050764762c849f2d1bccb),
the new module built from source on Windows with Lean `v4.36.0-rc1`, using
the pinned Mathlib revision and Lake's checked dependency cache. The
CDF-coupling and CDF-selection dependencies were also built natively.
All 363 pre-existing project modules in the 364-module import closure are
byte-identical to base checkpoint `7896d2b4a0bbe396301863b16e4884226457a782`.
No existing definition, specification lock, manifest or historical record
was changed.

The [independent exact statements](robust_cdf_bridge.lean) passed with
[12 transitive axiom reports](robust_cdf_bridge.log), using only `propext`,
`Classical.choice` and `Quot.sound`. Run
`python tools/verify_robust_cdf_bridge.py` to build and repeat this audit.
The verifier registers every declaration and rejects missing statements,
substituted theorem references, incomplete reports and disallowed axioms.
All 44 robust-continuation verifier regression tests passed, including the
9 new CDF-bridge tests.

The [local project audit input](project_closure.lean) and
[output](project_closure.log) cover exactly this 364-module import closure:
4,997 constants, including 4,039 theorems, no declared axioms, and only the
three allowed transitive axioms. Its 54 exported instances have the
required names, scope and priority. The closure contains three of the six
registered orphan instances; the other three defining modules are outside
the closure. All 911 covered definition fingerprints match the existing
2,320-entry lock, with no new definitions. This is a scoped local audit,
not a whole-project audit or an independent kernel replay. The unchanged
whole-project verifier and its full orphan registry run separately in CI.

[status.json](status.json) identifies the compiler, source hashes, closure
and reports. Both saved Lean inputs can be replayed by piping their UTF-8
text to `lake env lean -j1 --stdin` from `lean/` after building the module.
The source guard, all 246 hashes in 10 frozen/published manifests, generated
status/manuscript checks and whitespace check passed locally. CI claims
for a later PR head belong to that head's checks, not to this proof record.
