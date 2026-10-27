# Research process and history

These documents record the workflow and historical verification checkpoints. For mathematical claims, start with the [repository README](../../README.md) and [results guide](../RESULTS.md).

| Document | Purpose |
|---|---|
| [BRIEF.md](../../BRIEF.md) | Original research instructions and acceptance rules. |
| [TIER2.md](TIER2.md) | Approved extension of frozen targets and scorer. |
| [TRACK_B.md](TRACK_B.md) | Constant search, candidate selection, and bias audit. |
| [TRACK_C.md](TRACK_C.md) | Benchmark development, costs, and held-out comparison. |
| [TRACK_D.md](TRACK_D.md) | Source audit, upper-bracket diagnostics, and adaptation obstruction. |
| [RUNLOG.md](RUNLOG.md) | Chronological attempts and verification records. |
| [REPORT.md](REPORT.md) | Research report, proof scopes, and remaining questions. |
| [PROVENANCE.md](PROVENANCE.md) | Input provenance and verification policy. |
| [FREEZE_LOG.md](../../FREEZE_LOG.md) | Approval history for frozen targets and tools. |
| [Independent argument review](../../proposals/RESEARCH_REVIEW.md) | Agent review of the 713 argument, bias counterexample, and adaptation obstruction. |

`BRIEF.md` and `FREEZE_LOG.md` remain at the root because the frozen [freeze tool](../../tools/freeze.py) names them in instructions and diagnostics; the [Lean setup script](../../lean/setup.sh) also names `FREEZE_LOG.md`. The other process documents were relocated after checking tools, tests, and CI for dependencies on their original paths. Paths inside commands remain relative to the repository root unless stated otherwise.
