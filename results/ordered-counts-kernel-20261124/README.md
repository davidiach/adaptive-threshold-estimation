# Literal-weight kernel evaluation of the precommitted pilot-feedback certificate

The precommitted lower bound of
[`PilotFeedback`](../../lean/ThresholdHC/PilotFeedback/Full.lean) rests on
`Ordered.certified`: for every pilot count `j` and legal allocation `(h,t)`,
`pilotBound j ≤ suffix leaf (canonical h t (7-h-t)) (pilotWeights 18 j)`
(see [the original record](../pilot-feedback-20261120/README.md)). The
research module and the library checked it by one kernel evaluation with the
weights as functions `Fin 4 → ℕ`. This change keeps every statement, every
existing definition and the axioms of `certified`, and checks it about four
times faster in CPU time with about 40% less peak memory. The runs below were made
at commit
[`6137801`](https://github.com/davidiach/adaptive-threshold-estimation/commit/61378016e17b9a3fe4169b3a7d082c190fb6aa1a).

## What changed

Only proofs, and new definitions with their lemmas, all in
[`OrderedCounts.lean`](../../lean/ThresholdHC/PilotFeedback/OrderedCounts.lean).

- The module adds the literal evaluation of the
  [one-update](../pilot-feedback-kernel-20261123/README.md) and
  [stopping-update](../stopping-update-kernel-20261123/README.md)
  certificates: a `Literal.Quad` of numbers, `Literal.force`, which reduces
  each number to a literal before passing it on, `Literal.advanceK`,
  `Literal.suffix` by recursion on the three counts, `Literal.leaf` on the four
  numbers and `Literal.pilot`. The names carry the prefix `Literal` because
  `Scheduled` and `StoppingUpdate` open this namespace and define copies of
  the same evaluation under the plain names.
- `Literal.certified` states the bounds in that form and is proved with one
  `decide +kernel`. `certified` keeps its statement and derives it through
  `Literal.suffix_eq`.
- The bridge compares the four numbers pointwise (`Literal.Agrees`) instead of
  equating the weight functions. An equation between functions needs `funext`
  and `fin_cases`, which would add `Quot.sound` and `Classical.choice`; with
  the pointwise form `certified` depends on `propext` alone, as it did before.

A Python model gives row 9's exact minimum, 529,010,860 above its bound. The
kernel check of row 9 holds with the bound raised by that amount and fails
with it raised by one more, as it must.

## Timings

The module elaborated with `lake env lean` and replayed with `leanchecker`,
alone, on a four-core Intel Xeon at 2.10 GHz, Lean 4.36.0-rc1, with every
import already built. "Before" is the source of commit
[`64ffb78`](https://github.com/davidiach/adaptive-threshold-estimation/commit/64ffb78a639771b533c2f9b8bc2914c34ed58e21).

| `OrderedCounts` | Before | After |
|---|---|---|
| Elaborate: CPU, wall | 24.4 s, 186 s | 4.9 s, 4.6 s |
| Replay: CPU, wall | 24.4 s, 33 s | 5.6 s, 5.6 s |
| Peak memory: elaborate, replay | 5.84 GB, 5.50 GB | 3.55 GB, 3.18 GB |

The times include about 3 s of import. The elaboration before took 186 s of
wall time for 24 s of CPU on this machine; the gap is waiting, not
computation, and did not occur with the smaller footprint after. The whole
pilot-feedback audit with replay took 58 s, against 74 s after the one-update
change and about six minutes in the original record.

These are local measurements. The CI job durations on the commit under
review, not these, are the evidence for CI.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_pilot_feedback.py --replay --jobs 3` | 14 exact statements and 157 transitive axiom reports over the 18 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`; `Ordered.certified`, `Literal.certified` and `Ordered.total` depend on `propext` alone. All 18 modules replayed through the independent kernel checker in 58 s. | [pilot-feedback-audit.log](pilot-feedback-audit.log) |
| `python tools/verify_project_axioms.py` | 21,626 constants (17,357 theorems) in 1,785 modules, same axioms. 167 exported instances, the new one the generated `SizeOf` instance of `Ordered.Literal.Quad`; 6 registered orphans, unchanged. 4,101 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python tools/verify_stopping_update.py --replay --jobs 3` | Passes; its modules open `Ordered` and build unchanged. | |
| `python -m unittest discover -s tools -p 'test_pilot_feedback.py'` | 11 guard tests pass. | |
| `python tools/check_trust_anchors.py --base origin/main --head HEAD` | No changed trust anchor: the lock gains entries and no checked statement or checker line changes. | |
| `python tools/verify_lean_sources.py` | 1,786 Lean sources, no proof escapes. | |
| `python tools/verify_locks.py` | 246 locked hashes in 10 manifests pass. | |

The 157 reports are the 144 of the previous record and 13 new public
declarations of `OrderedCounts.lean`. The whole-project audit was first run
with `--add-definitions`, which added 20 entries to
`tools/definition_lock.json`: `Literal.Quad` with the declarations Lean
generates for it, `Literal.Agrees` and the five other new definitions. No
existing entry changed. The run recorded here is a later one without that
flag.

## Scope

The statements and their meaning are those of the
[original record](../pilot-feedback-20261120/README.md); this change alters
how the kernel checks the precommitted certificate, not what is checked.
`OrderedCounts.lean` now differs from its research copy by the section
described above. The research packages are unchanged. The other
precommitted certificate, `all_rows` of `FeedbackTable` (about 9 s), is
unchanged.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
