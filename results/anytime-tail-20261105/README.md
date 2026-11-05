# Infinite-moment tail-family audit

Proof checkpoint: 034db5c9382d37dafc31f6e91f50a5ec72382678.
Base checkpoint: 1ef16d9d5bf62f7da1cd225761a60fa804b15930.

The native Lean 4.36.0-rc1 audit checks fifteen independently restated exact
statements and fifteen transitive axiom reports. All ten newly compiled modules
have empty logs. The 351-source project closure contains 341 reused objects,
all matching published hashes. Source and direct dependency hashes are checked.

The audit covers capped inverse-gap profiles, positive and vanishing profile
masses, first quarter-drop minimality, finite adaptive transcript information,
the original observable-prefix KL transfer, separated prior means, an explicit
monotone unbounded integer schedule, and arbitrarily late radius violations.
The final statement constructs the small-gap region for every probability law
with nonintegrable inverse gap, rather than assuming the region exists.

The earlier [sequential-testing audit](../anytime-sequential-20261105/README.md)
provides the first-crossing argument. See [the construction](../../docs/ANYTIME_TAIL.md),
[exact input](anytime_tail.lean), [axiom reports](anytime_tail.log), and
[manifest](status.json). The ten numbered compiler logs are empty.

The final asymptotic comparison with the iterated-logarithm selection rate is
outside this checkpoint. This is native evidence, not a CI claim.
Portable replay: python tools/verify_anytime_tail.py.
