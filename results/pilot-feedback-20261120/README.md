# Pilot feedback: library audit

At the gap $d=1/5$ with budget $B=25$, an 18-flip pilot is followed by seven
follow-ups, each a fresh coin, the $k$th pilot head or the $k$th pilot tail.
Two research packages proved in Lean that committing the follow-ups early
costs RMS risk against the adaptive witness:
[pilot feedback](../../research/2026-11-18-pilot-feedback/README.md) and
[one scheduled update](../../research/2026-11-18-scheduled-update/README.md).
Their proofs are now in the audited library, in
[`lean/ThresholdHC/PilotFeedback`](../../lean/ThresholdHC/PilotFeedback/Full.lean).
The research packages are unchanged. The audit runs below were made at commit
[`cde1779a8554aef1e2b8a8891f7e631f3939dbf8`](https://github.com/davidiach/adaptive-threshold-estimation/commit/cde1779a8554aef1e2b8a8891f7e631f3939dbf8).

## Statements

[`Specification.lean`](../../lean/ThresholdHC/PilotFeedback/Specification.lean)
states four targets about the worst RMS risk over all measurable sign laws in
the original population experiment at $\delta_{1/5}$. An unavailable revisit
falls back to a fresh coin.

| Target | Statement |
|---|---|
| `precommitted_rms_lower` | Every algorithm that fixes all seven follow-up actions after the pilot, before any follow-up answer, has worst RMS risk at least $0.18735887$. |
| `precommitted_rms_separation` | The adaptive witness has strictly smaller worst RMS risk than every such algorithm. |
| `one_update_rms_lower` | Every algorithm that chooses after the pilot a split $m\in\{0,\dots,7\}$ and the first $m$ actions, and the remaining $7-m$ after the first $m$ answers, has worst RMS risk at least $0.186960371$. |
| `one_update_rms_separation` | The adaptive witness has strictly smaller worst RMS risk than every such algorithm. |

In both classes the seed may choose the plan, the plan may depend on the
whole ordered pilot word (the second batch also on the first-batch answers),
and the output may use the seed and the whole tape. The adaptive witness reads
only the number of pilot heads. The
adaptive witness is
[`SharpRMS.Pilot.pilotEstimator`](../../lean/ThresholdHC/LargeBudgetRMS/PilotWitness.lean),
whose worst RMS risk is below $0.186752$
([large-budget record](../large-budget-rms-20261118/README.md)).

## What changed from the research packages

The 16 proof modules (10 from pilot feedback, 6 from the scheduled update) are
copies with three kinds of change: imports point to library modules, the
namespace `PilotFeedback` becomes `ThresholdHC.PilotFeedback`, and three
anonymous `Decidable` instances get names, as the project audit requires.
Comments are copied verbatim, so one still says that a proof "below" checks
bounds that `ScheduledCertificate` checks. The
pilot-feedback package stated its bounds in squared-risk form; `Full.lean`
takes square roots to state them in RMS form, and the one-update targets are
the scheduled-update package's own RMS theorems.

The packages for [one update at a stopping time](../../research/2026-11-18-stopping-update/README.md)
and [two updates](../../research/2026-11-18-two-stopping-updates/README.md)
are not promoted. In their integer certificates a single row needs more than
13.5 GB of memory in the kernel, which exceeds the 15 GB available here and the
memory of a CI runner. Moving them into the library needs certificates split
into smaller declarations.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_pilot_feedback.py --replay --jobs 3` | 14 exact statements (4 targets and 10 components) and 126 transitive axiom reports over the 18 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 18 modules replayed through the independent kernel checker, about six minutes locally. | [pilot-feedback-audit.log](pilot-feedback-audit.log) |
| `python tools/verify_project_axioms.py` | 16,987 constants (13,639 theorems) in 1,449 modules, same axioms. 147 exported instances. 3,208 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python -m unittest discover -s tools -p 'test_pilot_feedback.py'` | 11 guard tests pass. | |
| `python tools/verify_lean_sources.py` | 1,450 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added 152
entries to `tools/definition_lock.json`: the four statement definitions and the
definitions of the promoted modules, among them the policy classes the
statements use. No existing entry changed. The run recorded here is a later one
without that flag. `ScheduledCertificate` alone takes about four minutes and
4.2 GB to compile.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The specification was written after the proofs; it is pinned by
hash from this audit onward. The lower bounds concern this fixed pilot, menu
and gap; the exact restricted minimax risks and the sharp large-budget
coefficient stay open. The integer certificates are evaluated by the kernel
(`decide +kernel`) and re-evaluated by the independent checker.

## Review

Before the specification was pinned, two reviewers that had not written it
compared the four statements with the research packages and diffed the 16
copies against their originals. Neither found a blocking problem. After
normalizing imports, namespaces and the three instance names, the copies are
byte-identical to the originals, every name resolves to the intended constant,
and `decide +kernel` is the only computation shortcut. One point was rated
important: the specification hash does not cover the policy classes, which are
defined in proof modules; the definition-lock entries above now fix them. The
minor points (the split's range and letter, the dependence on the ordered pilot
word, the fallback to a fresh coin, the RMS forms added in `Full.lean`, and the
hypotheses written out in two component restatements) were applied. This was
a review by AI agents, not a specialist referee report.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
