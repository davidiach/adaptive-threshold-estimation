# Faster kernel evaluation of the sharp RMS window certificate

For intermediate budgets the sharp RMS lower bound of
[`SharpRMS`](../../lean/ThresholdHC/SharpRMS/Full.lean) rests on 140 integer
comparisons, one for each bias interval of the window $[2/5,39/40]$, which
the Lean kernel evaluates (`checked_window`; see
[the integer certificate](../sharp-rms-20261117/README.md#the-integer-certificate)
in the original record). CI builds them in three jobs: `lean-kernel`,
`entropy-tail-upper` (through `PaperCorollaries` and `CreationCharge`) and
`lean-all-modules`. In the from-scratch run on `main` at `b03c5a2`
([run 44958526343](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/44958526343)),
the `lean-kernel` step that builds and replays the `SharpRMS` modules took
21 of the job's 99 minutes, the longest step of the job. This change keeps
every statement and every existing definition and makes the kernel evaluate
the comparisons about four times faster. The runs below were
made at commit
[`476621c`](https://github.com/davidiach/adaptive-threshold-estimation/commit/476621c9a20792fc674171aca87e1522d214a1e3).

## What changed

Only proofs, and new definitions with their lemmas.

- [`WindowBound.lean`](../../lean/ThresholdHC/SharpRMS/WindowBound.lean)
  adds `fastBound lo hi : Bool`. It computes the upper sum of
  `gridBound lo hi` with the primitive `Nat` operations (`Nat.mul`,
  `Nat.div`, `Nat.ble` and the others) and the recursors `Nat.rec`,
  `List.rec` and `Bool.rec`, over the same barrier list. `fastSum_eq`
  proves `fastSum u = upperSum u` for every `u`, and
  `gridBound_of_fastBound` proves `fastBound lo hi = true → gridBound lo hi`.
- The 140 theorems `interval001` to `interval140` in `WindowPart1` to
  `WindowPart7` keep their names, statements `gridBound lo hi`, bounds and
  order. Each proof changes from `by decide +kernel` to
  `gridBound_of_fastBound (by decide +kernel)`.

The original definitions reach the kernel through the type-class instances
of `*`, `^` (Mathlib's `Monoid.npow`), `max` and `min` and through the
compiled structural recursion of `List.foldl`. In test runs most of the
kernel's time went to those unfoldings rather than to the arithmetic, which
it performs with GMP on literals in both forms.

`checked_window` and each interval theorem still depend on `propext`
alone. The proof of `fastSum_eq` avoids `List.foldl_append`, which would
add `Quot.sound`.

## Timings

One module, `WindowPart1` (20 comparisons), on one core of a four-core
Intel Xeon at 2.10 GHz, Lean 4.36.0-rc1, with every import already built.
"Before" is the source of commit
[`b03c5a2`](https://github.com/davidiach/adaptive-threshold-estimation/commit/b03c5a29085c9d5f4cea0b17f6a2561add9cbcd9).

| Measurement | Before | After |
|---|---|---|
| `lake build ThresholdHC.SharpRMS.WindowPart1` | 209 s and 227 s (two runs) | 48 s |
| `lake env lean` on the module: wall time, peak memory | 217 s, 4.94 GB | 45 s, 4.07 GB |
| `leanchecker ThresholdHC.SharpRMS.WindowPart1` (the kernel replay) | 219 s | 43 s and 53 s (two runs) |

Of the peak memory, 3.40 GB is the import alone (a file with only the import
line), so the comparisons take about 1.54 GB above it before and 0.67 GB
after.

After the change the seven window modules build in 48 to 54 s each, about
6 CPU minutes for the 140 comparisons and 110 s of wall time for the seven
on four cores. Only `WindowPart1` was timed before the change; the original
record gives about 22 minutes to compile the 140 comparisons as one research
file and about 20 more to replay them.

These are local measurements. A CI run on this branch rebuilds the changed
modules on the runner; the job durations of that run, not these, are the
evidence for CI.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_sharp_rms.py --replay --jobs 3` | 38 exact statements and 361 transitive axiom reports over the 54 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`; `checked_window`, `fastSum_eq` and `gridBound_of_fastBound` depend on `propext` alone. All 54 modules replayed through the independent kernel checker. 244 s on four cores with the modules already built; the original record gives about 10 minutes. | [sharp-rms-audit.log](sharp-rms-audit.log) |
| `python tools/verify_project_axioms.py` | 22,008 constants (17,813 theorems) in 1,785 modules, same axioms. 164 exported instances. 4,033 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python tools/verify_sharp_strict.py --replay --jobs 3` and `python tools/verify_restricted_rms.py --replay --jobs 3`, whose proofs use `checked_window` or `SharpRMS.Full` | 9 exact statements and 29 axiom reports; 7 exact statements and 16 axiom reports. Their modules replayed. | |
| `python -m unittest discover -s tools -p 'test_sharp_rms.py'`, and the same for `test_sharp_strict.py`, `test_large_budget_rms.py`, `test_restricted_rms.py` and `test_project_axioms.py` | 11, 11, 11, 11 and 12 guard tests pass. | |
| `python tools/verify_lean_sources.py` | 1,786 Lean sources, no proof escapes. | |
| `python tools/verify_locks.py` | 246 locked hashes in 10 manifests pass. | |

The 18 new reports of the sharp RMS audit are the new public declarations of
`WindowBound.lean`: ten definitions and eight theorems. The whole-project
audit was first run with `--add-definitions`, which built every module (49
minutes on four cores) and added ten entries to
`tools/definition_lock.json`, one for each new definition. No existing entry
changed. The run recorded here is a later one without that flag.

## Scope

The statements and their meaning are those of the
[original record](../sharp-rms-20261117/README.md); this change alters how
the kernel checks them, not what is checked. That record and its
[provenance map](../sharp-rms-20261117/provenance.json) describe commit
`f142500`, at which the window modules matched the research checkpoint up to
the split into seven modules. Since this change `WindowBound.lean` and the
seven window modules differ from it as described above. The research package
is unchanged.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
