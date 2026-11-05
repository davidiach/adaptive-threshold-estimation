# Complete law-dependent time-uniform lower-bound audit

Proof checkpoint: a6c77f546604cb6df7df67802e0061d1345fa2ca.
Base checkpoint: ed885968cab32c1144fbd273117c5d99a95ae38e.

Native Lean 4.36.0-rc1 checks fourteen independently restated exact statements
and fourteen transitive axiom reports. All twenty newly compiled modules have
empty logs. The 609-source project closure contains 589 reused objects, all
matching previously published hashes. Source, direct dependency and object
hashes are checked.

The audit completes the finite-coefficient case, the dense and sparse
infinite-moment cases, and their combination for every probability law on
positive gaps. It includes the actual online experiment and an observable
interval consequence: for 0<ρ≤1/4 and 0<δ≤1/4, every nonnegative deterministic
half-width envelope satisfying joint simultaneous coverage and width control
under every rare sign prior is at least

    10^(−22) K_(μ,ρ)(n/[log(1/δ)+log log n])

at arbitrarily late integer budgets. Monotonicity of the envelope is not
required. This is not a lower bound at every budget or on every random width.

See the [proof and scope](../../docs/TIME_UNIFORM_LOWER.md),
[exact audit input](anytime_asymptotics.lean),
[transitive axiom reports](anytime_asymptotics.log), and
[manifest](status.json). The twenty numbered compiler logs are empty.
The earlier [sequential](../anytime-sequential-20261105/README.md) and
[tail-family](../anytime-tail-20261105/README.md) records retain their original
checkpoint identities and scopes.

Portable replay: python tools/verify_anytime_asymptotics.py.
This record is native evidence, not a claim about later CI runs.
