# Universal closed-quantile minimax law

The [native audit](status.json) checks the complete two-sided closed-quantile
rate in the original observable experiment for every probability law on
`(0,1/2]`, `0 < rho <= 1/4`, and every positive expected-flip budget.
Rarity is global, magnitudes and signs stay hidden, and fractional boundary
atoms are included. No inverse-moment or finite-support premise is added.

The proof combines the completed entropy-tail lower bound with
`Q <= (1 + 2 sqrt(2)) K`; its upper half reuses the checked bound
`R <= 30001 Q`. The target asserts positive universal comparison constants.
It does not prove the paper's explicit lower constant or its separate direct
finite-law argument.

This is a new corollary specification and lock introduced alongside the
proof, not an independently frozen pre-proof target. The imported experiment
and quantile functionals keep their earlier frozen definitions. The complete
source hashes in the status file identify this change following parent
`e65e05b5cdd180da1c5b4a2d3562ff0296e647a7`.

The audit rebuilt both registered modules, checked the exact full target and
both declaration roots, and completed all three native commands with exit 0.
Only `propext`, `Classical.choice`, and `Quot.sound` occur in the transitive
axioms. It verified source, generated-audit, and reused-artifact stability.

This was an explicit cached-dependency run, not a full dependency rebuild.
The 504-module local closure reuses 502 dependencies: 57 lower-support
modules and 10 canonical modules rebuilt by the preceding
[entropy-tail completion audits](../entropy-tail-complete-20261101/README.md),
and 435 unchanged local dependency sources matching the integration cache.
Every reused native artifact is hashed in the status record. The toolchain
is Lean `v4.36.0-rc1`, with Mathlib
`9bdd0bc71aaae0fd83889f9aacd70c32fccd1bcd`.

The eight new verifier guards, frozen-source verification, and proof-escape
scan of all 731 project Lean sources passed. Documentation links and
whitespace checks passed. This record does not claim a GitHub CI pass.

Reproduce from the repository root:

```sh
python tools/verify_closed_quantile.py
python -m unittest discover -s tools -p 'test_closed_quantile.py' -v
```

The default rebuilds the full local closure. Add `--cached-dependencies` to
reproduce the narrower recorded mode with populated artifacts, and use
`--lake PATH` if needed. New logs go under `.runtime/closed-quantile/`.
