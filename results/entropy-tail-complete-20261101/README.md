# Complete entropy-tail lower bound and two-sided law

These native Lean audits complete all eight original frozen entropy-tail
targets, including `entropy_tail_lower` and `entropy_tail_law`, in the
unchanged observable experiment. They cover every probability law on
`(0,1/2]`, `0 < rho <= 1/4`, and every positive expected-flip budget, with
global rarity and hidden magnitudes/signs. The proof constructs conservative
universal constants; it does not assert the paper's sharper explicit lower
constant or a separate closed-quantile minimax theorem.

The source identity is the complete `source_sha256` mapping in each status
file. This is the completion change following parent commit
`df6ff67654b225efe5d086d1c7c3e4a3b23cad1e` on PR #38. No prior published
record, frozen specification, or dependency lock was rewritten.

| Audit | Registered modules | Declaration roots | Exact types | Native commands |
|---|---:|---:|---:|---:|
| [Finite-certificate lower proof](support/status.json) | 57 | 368 | 89 | 58, all exit 0 |
| [Canonical entropy-tail targets](canonical/status.json) | 15 | 92 | 8 | 16, all exit 0 |

The generated exact-type sources and every compiler log are preserved beside
the status files. The generated support audit retains its exact compiled bytes,
including diagnostic formatting, under a narrow whitespace-check exemption.
Only `propext`, `Classical.choice`, and `Quot.sound` occur
in the reported transitive axioms. Both audits check protected source
stability, generated audit stability, and reused artifact stability before
recording success. The support audit deliberately leaves the canonical
lower/law completion flags false: those belong to the separate successful
eight-target canonical audit, whose `entropy_tail_law_verified` is true.

## Dependency scope

Both runs use explicit cached-dependency mode. They rebuild every registered
module with pinned Lean `v4.36.0-rc1`, one native compiler process at a time,
against Mathlib `9bdd0bc71aaae0fd83889f9aacd70c32fccd1bcd`. They are **not
full local dependency rebuilds**. Reused native `.olean*` artifacts are hashed
in the status files; each audit checks their stability during its own run.
Later canonical recompilation may replace an artifact recorded by the earlier
support audit; the records describe their respective executions.

- The support closure has 443 local modules and reuses 386 dependencies.
  Of those sources, 385 match the `entropy-tail-integrated` cache checkout
  byte for byte. The remaining source, the current canonical
  `EntropyTail/Bridge.lean`, was rebuilt successfully with the pinned native
  compiler immediately before the combined draft check. That bridge differs
  from the older integration branch's bridge.
- The canonical closure has 507 local modules and reuses 492 dependencies:
  all 57 lower-support modules rebuilt by the preceding successful audit,
  plus 435 local dependency sources matching the integration cache checkout
  byte for byte.

The independently scoped earlier integration rebuild is preserved in
[rare-event-full-20261031](../rare-event-full-20261031/README.md). Its different
bridge and checkpoint must not be described as this completion audit.

## Reproduction and additional checks

From the repository root, with the pinned toolchain and Mathlib cache:

```sh
python tools/verify_entropy_tail_lower_components.py
python tools/verify_entropy_tail.py --sequential --require-complete
```

The first command defaults to rebuilding the entire local support closure.
To reproduce the narrower recorded runs with already populated local
artifacts, add `--cached-dependencies` to both commands. `--lake PATH` selects
the Lake executable. Fresh evidence is written under `.runtime/`, never here.

The 14 canonical verifier guards and nine lower-component guards passed.
The frozen-source check, proof-escape scan of all 729 project Lean sources,
documentation links, and whitespace checks passed. GitHub CI has a separate
commit identity and status; this local record does not claim a CI pass.

See the [proof map](../../docs/ENTROPY_TAIL_LOWER_PROGRESS.md) and
[remaining project work](../../docs/WORKPLAN.md#current-priorities).
