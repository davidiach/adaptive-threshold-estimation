# Finite-family law adaptation: native Lean component audit

Proof checkpoint: `507f0f5e5dea0ac53e5376f3d911b58ec3096c72`.
The [machine-readable record](status.json) binds the complete 636-source project
closure, six fresh native compilations with empty logs, and 630 unchanged
compiled dependencies whose hashes match previously published evidence.
There are no first-time inherited artifacts.

All 17 independently restated exact theorem types and transitive axiom reports
pass. Only the standard Lean axioms `propext`, `Classical.choice` and
`Quot.sound` occur. The [audit input](law_adaptation.lean) and
[reports](law_adaptation.log) are preserved alongside the six empty logs.

## Result and boundary

For an unknown gap law belonging to a supplied finite family, a sign-neutral
pilot followed by the known-law confidence controller attains the known-law
time-uniform rate after an explicit finite identification cost.
The [full theorem and proof](../../docs/FINITE_FAMILY_ADAPTATION.md) explain
the candidate-family premise and the deterministic pilot cap.

Lean checks these components:

- Finite-prefix parity means, removal of the latent sign by even powers,
  mixtures over signs, and the pathwise bound on the statistic.
- Hoeffding concentration for independent bounded observations.
- Identification from separated signatures, its union bound, exponential
  error bound and natural-log sample calibration.
- Transfer of simultaneous properties to a selected procedure without an
  extra union bound over candidates.
- Physical budget arithmetic for a paid pilot.
- A factor-two delayed-rate comparison with the actual entropy-tail selection
  functional after the total budget reaches twice the pilot cap.

The moment-determinacy argument, the concrete fresh-coin pilot realization,
and construction of the complete selected controller in the original
observable experiment remain paper proofs. The audit does not formally
verify the Python runtime. It does not establish adaptation over arbitrary
unknown laws or a family-uniform onset time. No independent specialist
review is claimed.

## Replay and additional checks

With the pinned Lean toolchain and Mathlib cache:
~~~sh
python tools/verify_law_adaptation.py
~~~

The publication compiles natively with `-j1`. Before artifact reuse it checks
source, direct-dependency and compiled-object hashes. The record includes the
compiler identity and unchanged dependency manifests.

All 225 toolkit tests passed, including seven new pilot tests for exact parity
identities, higher-moment identification, sample calibration, sign invariance,
physical flip accounting, insufficient authorization and tampered plans.
The three proof-escape guard tests, frozen-source verification, whitespace and
relative-link checks passed. These executable checks do not prove the
statistical theorem. CI status is separate and belongs to its exact commit.

