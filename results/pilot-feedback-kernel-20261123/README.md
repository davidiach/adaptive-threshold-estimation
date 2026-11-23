# Literal-weight kernel evaluation of the one-update pilot-feedback certificate

The one-update lower bound of
[`PilotFeedback`](../../lean/ThresholdHC/PilotFeedback/Full.lean) rests on the
integer certificate `Scheduled.certified (j : Fin 19) : Row j`, which the
research module and the first library version checked by kernel evaluation
of the `Decidable` instance of each row (see
[the original record](../pilot-feedback-20261120/README.md)). In the
from-scratch runs on `main` at `b03c5a2` and `faf484f`
([run 44958526343](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/44958526343),
[run 45202811088](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/45202811088)),
the `lean-kernel` step that builds and replays the pilot-feedback modules took
9.5 and 10.8 minutes. This change keeps every statement and every existing
definition and checks the rows about ten times faster. The runs below were
made at commit
[`d59588c`](https://github.com/davidiach/adaptive-threshold-estimation/commit/d59588cff2939aac67119677a89f53dc680d7bf0).

## What changed

Only proofs, and new definitions with their lemmas, all in
[`ScheduledCertificate.lean`](../../lean/ThresholdHC/PilotFeedback/ScheduledCertificate.lean).

- `Row j` holds the weights as functions `Fin 4 → ℕ`. Along different paths of
  `suffix` and `tailCost` the kernel meets equal weights as different terms,
  so its cache cannot reuse their values and it evaluates them again.
- The module adds the evaluation that the
  [stopping-update certificate](../stopping-update-kernel-20261123/README.md)
  uses: the weights are a `Quad` of numbers, `force` reduces each number to a
  literal before passing it on, `fastSuffix` computes `suffix` of
  `canonical h t f` with any terminal by recursion on the three counts, and
  `fastTail` computes `tailCost`. The definitions are copies under the
  namespace `Scheduled`: `StoppingUpdate` imports this package, so this
  package cannot use the stopping-update definitions, and the definition lock
  pins those where they are.
- `fastRows j` states each row in that form and is proved with one
  `decide +kernel` per pilot count. `certified` keeps its statement and now
  derives `Row j` from `fastRows j` through `fastSuffix_eq`, `fastTail_eq` and
  `fastPilot_toWeights`. `certificate_total` is unchanged.

A Python model of row 9 visits 101,376 leaves and 7,423 tail costs when the
row is evaluated as written. The kernel computes the row's exact minimum: with
the floor of row 9 raised by 3,264,708 the fast check still holds, and raised
by 3,264,709 it fails, as the model predicts.

The precommitted certificate `all_rows` of `FeedbackTable` (about 9 s) and
`Ordered.certified` of `OrderedCounts` (about 25 s, peak 5.8 GB) are
unchanged; `OrderedCounts` defines the weights the faster form needs, so the
same evaluation would have to be placed inside it.

## Timings

Each module elaborated with `lake env lean` and replayed with `leanchecker`,
on one core each, on a four-core Intel Xeon at 2.10 GHz, Lean 4.36.0-rc1,
with every import already built. "Before" is the source of commit
[`fd50b41`](https://github.com/davidiach/adaptive-threshold-estimation/commit/fd50b413710afe2cbee911a7cd85febeda73a4f8),
measured three modules at a time; their wall times are inflated by memory
pressure, so the table gives CPU time.

| Module | Elaborate before | Elaborate after | Replay before | Replay after | Peak memory before | Peak memory after |
|---|---|---|---|---|---|---|
| `ScheduledCertificate` | 281 s | 29 s | 293 s | 30 s | 6.01 GB | 3.50 GB |
| `OrderedCounts` (unchanged) | 25.5 s | | 24.6 s | | 5.81 GB | |
| `FeedbackTable` (unchanged) | 9.4 s | | 10.6 s | | 2.32 GB | |

The times include about 3 s of import per module. `lake build` of
`ScheduledCertificate` took 28 s.

These are local measurements. The CI job durations on the commit under
review, not these, are the evidence for CI.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_pilot_feedback.py --replay --jobs 3` | 14 exact statements (4 targets and 10 components) and 144 transitive axiom reports over the 18 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`; `certified` uses all three and `certificate_total` `propext` alone, as before. All 18 modules replayed through the independent kernel checker; the run took 74 s with the modules built. The original record gives about six minutes. | [pilot-feedback-audit.log](pilot-feedback-audit.log) |
| `python tools/verify_project_axioms.py` | 21,595 constants (17,348 theorems) in 1,785 modules, same axioms. 166 exported instances, the new one the generated `SizeOf` instance of `Scheduled.Quad`; 6 registered orphans, unchanged. 4,081 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python -m unittest discover -s tools -p 'test_pilot_feedback.py'` | 11 guard tests pass. | |
| `python tools/verify_lean_sources.py` | 1,786 Lean sources, no proof escapes. | |
| `python tools/verify_locks.py` | 246 locked hashes in 10 manifests pass. | |

The 144 reports are the 126 of the original record and 18 new public
declarations of `ScheduledCertificate.lean`. The whole-project audit was first
run with `--add-definitions`, which added 23 entries to
`tools/definition_lock.json`: `Scheduled.Quad` with the declarations Lean
generates for it, `Quad.toWeights` and the eight other new definitions. No
existing entry changed. The run recorded here is a later one without that
flag.

## Scope

The statements and their meaning are those of the
[original record](../pilot-feedback-20261120/README.md); this change alters
how the kernel checks the one-update certificate, not what is checked. That
record describes its own checkpoint, at which the proof modules were copies
of the research modules up to imports, namespace and three instance names;
`ScheduledCertificate.lean` now differs further, as described above. The
research packages are unchanged.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
