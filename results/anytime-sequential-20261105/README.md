# Observable sequential-testing audit

Proof checkpoint: f6ddbf0c07d8d7b6d0611fba3c44e20377784d68.
Base checkpoint: 43d9fba720332fe7f3b5dfbcfef137839e6cfef5 (merged PR #63).

The native Lean 4.36.0-rc1 audit checks eight independently restated exact
statements and eight transitive axiom reports. The reports contain only the
standard Lean axioms accepted by the repository's verifier. All five newly
compiled proof modules have empty compiler logs. The complete project closure
has 336 sources; the other 331 objects match previously published hashes.
The manifest also checks each source and direct dependency hash.

The statements cover the binary-event entropy inequality, an event-probability
lower bound from KL, finite first-crossing information budgets, summability,
infinitely many width violations under a nonsummable schedule, the explicit
half-log divergent schedule, and the transfer to the original observable
experiment with one adaptive policy and prefix-measurable estimates.

See [the explanation](../../docs/ANYTIME_SEQUENTIAL.md),
[exact compiler input](anytime_sequential.lean), [axiom reports](anytime_sequential.log),
and [hash manifest](status.json). The five numbered logs are empty.

This checkpoint does not formalize the infinite-moment prior construction or
the final law-dependent asymptotic comparison. It is not a CI claim.
Portable replay: python tools/verify_anytime_sequential.py.
