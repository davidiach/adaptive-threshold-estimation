# Complete rare-event proof audit, excluding the entropy-tail lower bound

The full kernel audit passed in [GitHub Actions run 41182963514](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/41182963514) for proof commit `2036bd111432dd020003c29c31f6dd41c960de55`.

All **518 local dependency modules** were rebuilt successfully. The final
audit checked **111 exact types** and the transitive axioms of **1,789
declarations in 276 target modules**. Only `propext`, `Classical.choice`, and
`Quot.sound` occur. `status.json` records every source hash and command;
`ExactAudit.lean` contains the independent exact assertions and axiom requests.
The first 518 logs are compilations; log 519 is the exact-type/axiom audit.
All recorded source hashes were checked against the publication checkout.

The scope includes the observable entropy-tail and closed-quantile upper
bounds; atom-aware deterministic quantile comparison; stopping programs,
attained duality, statistical realization, cap identification and finite
risk certificates; the infinite-cap dual; and the genie brackets, posterior
convergence, regularization, finite conic formulation and counterexample.
The canonical frozen entropy-tail upper statement is checked through a
proved equality of both selection functionals. The five deterministic
canonical targets are checked as well.

The statistical entropy-tail lower bound is excluded. This record does not
claim the two-sided minimax quantile law, the separate direct finite-law lower
argument, or the remaining unrelated paper-only regimes.

`namespace-port.json` checks all 263 copied modules against original proof
checkpoint `4e116018f0c1651382452aa9317fecc971edaec7`: 38 change only the identifier
`EntropyTail` to `EntropyTailQuantile`, including short qualified references.
The original pre-proof lock is byte-identical, and main's independently frozen
model, specification and lock are unchanged. Earlier component evidence is
preserved with its original checkpoint scope.

Earlier local full-audit attempts failed or were interrupted and are not
used as successful full-rebuild evidence. The final local regression suite
passed 94 tests; the 668-source proof-escape scan, frozen-source check, v6
assembly checks and 12 manuscript-assembly tests also passed.

Reproduce from the repository root with the pinned toolchain:

```sh
python tools/verify_rare_event_completion.py --jobs 2
```

For one Lake environment initialization, from `lean/`:

```sh
lake env python ../tools/verify_rare_event_completion.py --lean lean --jobs 2
```

Fresh output goes under `.runtime/`; published evidence is never overwritten.
The explicit `--cached-dependencies` option has a narrower rebuild scope and
was **not** used for this record.
