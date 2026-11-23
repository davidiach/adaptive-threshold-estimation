# Whole-row kernel evaluation of the stopping-update certificate

The one-stopping-update separation of
[`StoppingUpdate`](../../lean/ThresholdHC/StoppingUpdate/Full.lean) rests on
the certificate `certified (j : Fin 19) : rowCheck j = true`, one row for
each pilot count (see [the original record](../stopping-update-20261121/README.md)).
The research build of one row ran out of memory above 13.5 GB, so the library
split each row into 27 pieces, 513 kernel checks in eleven row modules. In
the from-scratch run on `main` at `b03c5a2`
([run 44958526343](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/44958526343)),
the `stopping-program` step that builds and replays these modules took 30 of
the job's 71 minutes. This change keeps every statement and every existing
definition and checks each row whole, about 30 times faster. The runs below
were made at commit
[`34d0235`](https://github.com/davidiach/adaptive-threshold-estimation/commit/34d023555deeddf3d98c6c1658c51a0ec1ee307d).

## What changed

Only proofs, and new definitions with their lemmas.

- `rowCheck` holds its weights as functions `Fin 4 → ℕ`. Along different
  paths of `unused`, `tailCost` and `suffix` the kernel meets equal weights
  as different terms, such as the same advances in another order, so its
  cache cannot reuse their values and it evaluates them again.
- [`StoppingPieces.lean`](../../lean/ThresholdHC/StoppingUpdate/StoppingPieces.lean)
  adds `fastRowCheck`. Its weights are a `Quad` of numbers; `force` reduces
  each number to a literal before passing it on, so equal weights, counts and
  positions are equal terms. `fastSuffix` computes `suffix leaf` of
  `canonical h t f` by recursion on the three counts. `rowCheck_eq_fast`
  proves `rowCheck j = fastRowCheck j` for every `j`, through one lemma per
  step (`fastSuffix_eq`, `fastTail_eq`, `fastUnused_eq` and the others).
- The eleven row modules keep their names and now prove
  `fastRowCheck j = true` with one `decide +kernel` per row (`rows_0_4`,
  `row_5` to `row_13`, `rows_14_18`), in place of the 27 piece checks of
  `pieces_0_4` to `pieces_14_18`.
- [`StoppingCertificate.lean`](../../lean/ThresholdHC/StoppingUpdate/StoppingCertificate.lean)
  keeps `certified` and `total` with the same statements; `certified` now
  rewrites with `rowCheck_eq_fast` instead of applying `row_of_pieces`.
- `pieceCheck`, `modeOf` and `row_of_pieces` remain in `StoppingPieces.lean`,
  unused; the definition lock pins the first two.

A Python model of row 9 shows the scale of the reuse: evaluated as written,
the row visits 11,104,128 leaves; with equal states shared it needs 540
distinct leaves, 5,148 suffix states, 714 tail costs and 7,026 nodes of
`unused`. The row's minimum equals its floor exactly, so the certificate has
no slack; the new form computes the same numbers. A check of row 9 with its
floor raised by one fails in the kernel, as it must.

## Timings

Each module elaborated with `lake env lean` and replayed with `leanchecker`,
on one core each, three modules at a time on a four-core Intel Xeon at
2.10 GHz, Lean 4.36.0-rc1, with every import already built. "Before" is the
source of commit
[`faf484f`](https://github.com/davidiach/adaptive-threshold-estimation/commit/faf484f208c2154d11d46d3ef6bcf82d6df920e1).
Times are CPU seconds and include about 3 s of import per module; memory is
the elaboration peak, of which the import alone accounts for about 3.2 GB.

| Module | Elaborate before | Elaborate after | Replay before | Replay after | Peak memory before | Peak memory after |
|---|---|---|---|---|---|---|
| `StoppingRows0to4` | 271 s | 9.6 s | 328 s | 10.9 s | 3.76 GB | 3.43 GB |
| `StoppingRow5` | 135 s | 5.8 s | 144 s | 6.5 s | 3.83 GB | 3.48 GB |
| `StoppingRow6` | 169 s | 7.3 s | 184 s | 8.1 s | 3.99 GB | 3.55 GB |
| `StoppingRow7` | 255 s | 7.3 s | 246 s | 9.4 s | 4.13 GB | 3.57 GB |
| `StoppingRow8` | 257 s | 7.7 s | 247 s | 7.3 s | 4.13 GB | 3.57 GB |
| `StoppingRow9` | 245 s | 6.8 s | 273 s | 7.1 s | 4.12 GB | 3.57 GB |
| `StoppingRow10` | 276 s | 6.5 s | 248 s | 8.2 s | 4.12 GB | 3.57 GB |
| `StoppingRow11` | 272 s | 7.1 s | 254 s | 8.8 s | 4.13 GB | 3.57 GB |
| `StoppingRow12` | 224 s | 6.6 s | 232 s | 7.6 s | 4.03 GB | 3.56 GB |
| `StoppingRow13` | 185 s | 6.1 s | 176 s | 6.9 s | 3.88 GB | 3.50 GB |
| `StoppingRows14to18` | 320 s | 9.2 s | 319 s | 9.7 s | 3.79 GB | 3.45 GB |
| **Eleven row modules** | **2,610 s** | **80 s** | **2,652 s** | **90.5 s** | | |

`StoppingPieces` now takes 3.7 s and `StoppingCertificate` 3.4 s (2.3 s
before; `total` is unchanged). `lake build` of the whole group, with the
other `StoppingUpdate` modules already built, took 30 s of wall time on four
cores; the original record gives 13 min 45 s for the group.

These are local measurements. The CI job durations on the commit under
review, not these, are the evidence for CI.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_stopping_update.py --replay --jobs 3` | 5 exact statements (the 2 targets and 3 components) and 74 transitive axiom reports over the 20 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`; `certified` uses all three, as before, and `total` and each row theorem `propext` alone. All 20 modules replayed through the independent kernel checker, which re-evaluates every row; the run took 57 s. The original record gives 22 minutes with two jobs. | [stopping-update-audit.log](stopping-update-audit.log) |
| `python tools/verify_project_axioms.py` | 21,557 constants (17,335 theorems) in 1,785 modules, same axioms. 165 exported instances, the new one the generated `SizeOf` instance of `Quad`; 6 registered orphans, unchanged. 4,058 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python -m unittest discover -s tools -p 'test_stopping_update.py'` | 11 guard tests pass. | |
| `python tools/verify_lean_sources.py` | 1,786 Lean sources, no proof escapes. | |
| `python tools/verify_locks.py` | 246 locked hashes in 10 manifests pass. | |

The 74 reports are the 53 of the original record, with the 11 piece theorems
replaced by the 11 row theorems, and 21 new public declarations of
`StoppingPieces.lean`. The project has 451 fewer constants than before,
mostly the auxiliary lemmas of the 513 piece checks. The whole-project audit
was first run with `--add-definitions`, which added 25 entries to
`tools/definition_lock.json`: `Quad` with the declarations Lean generates for
it, `Quad.toWeights` and the ten other new definitions. No existing entry
changed. The run recorded here is a later one without that flag.

## Scope

The statements and their meaning are those of the
[original record](../stopping-update-20261121/README.md); this change alters
how the kernel checks the certificate, not what is checked. That record
describes its own checkpoint. The research package is unchanged. The
two-update package of the work plan stays outside the library; whether the
same evaluation makes its certificate feasible has not been tried.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
