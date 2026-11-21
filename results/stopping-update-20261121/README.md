# One schedule replacement at a stopping time: library audit

The research package
[`research/2026-11-18-stopping-update`](../../research/2026-11-18-stopping-update/README.md)
proves that at gap $1/5$ with a budget of 25 flips, every algorithm that
flips 18 pilot coins once and may replace its seven-action follow-up schedule
once, at a stopping time of the observed answers, has worst RMS risk at least
$0.186844275$. The fully adaptive witness has worst RMS risk at most
$0.186752$, so it is strictly better. The package carries its own Lean proof
and replay record, but it stayed outside the CI-audited library: the research
certificate checks each of 19 pilot-count rows in one kernel evaluation, and
its build ran out of memory above 13.5 GB
([record](../pilot-feedback-20261120/README.md)). That build used `lean -j2`,
so two rows may have been resident at once. Lean now checks the package in
the library, in
[`lean/ThresholdHC/StoppingUpdate`](../../lean/ThresholdHC/StoppingUpdate/Full.lean),
with the certificate split. The research package is unchanged. The audit runs
below were made at commit
[`b7d413f`](https://github.com/davidiach/adaptive-threshold-estimation/commit/b7d413f).

## Statements

[`Specification.lean`](../../lean/ThresholdHC/StoppingUpdate/Specification.lean)
holds the research definitions the statements use: a `Plan` (an initial
schedule read from the ordered pilot word, a trigger on observed prefixes and
a replacement schedule), the first triggering prefix, the schedule in force,
the requested label and the policy stopped after 25 flips.

| Target | Statement |
|---|---|
| `one_stopping_update_rms_lower` | Every adaptive estimator whose seed selects a one-stopping-update plan has worst RMS risk at least $0.186844275$ at the point mass on the gap $1/5$. |
| `one_stopping_update_rms_separation` | The adaptive witness `SharpRMS.Pilot.pilotEstimator` has strictly smaller worst RMS risk than every such estimator. |

The statements are those of the research package's
[public statements](../../research/2026-11-18-stopping-update/AuditStopping.lean).
The seed may choose the plan, and the output may use the seed and the whole
tape. A component, `scheduled_embeds`, shows that every plan of the
`PilotFeedback` one-update class, whose replacement time is fixed after the
pilot, is a one-stopping-update plan, so this class contains that one.

## How the proofs go

The proof modules are the research modules `StoppingPolicy`, `StoppingBounds`,
`StoppingBayes` and `StoppingPopulation`, with the namespace renamed, the
imports reduced and the definitions the statements use moved into the
specification. The certificate is new:

- [`StoppingPieces.lean`](../../lean/ThresholdHC/StoppingUpdate/StoppingPieces.lean)
  splits the check of row $j$ by the first three initial actions into 27
  pieces, of which 427 of the 513 do real work; a piece with an illegal prefix
  reduces to `true`. `row_of_pieces` reassembles the research statement
  `rowCheck j = true`.
- Eleven row modules, from
  [`StoppingRows0to4.lean`](../../lean/ThresholdHC/StoppingUpdate/StoppingRows0to4.lean)
  to [`StoppingRows14to18.lean`](../../lean/ThresholdHC/StoppingUpdate/StoppingRows14to18.lean),
  each hold one theorem whose single tactic block runs its pieces one after
  another with `decide +kernel`.
- [`StoppingCertificate.lean`](../../lean/ThresholdHC/StoppingUpdate/StoppingCertificate.lean)
  keeps the research types `certified (j : Fin 19) : rowCheck j = true` and
  `total`.

Measured by the implementing agent with `lean -j1`: each row module takes at
most about 5.5 minutes and peaks at about 4.2 GiB resident, of which about
1.1 GiB is its own memory and the rest mapped `.olean` files. The eleven row
modules take 2,766 s, about 46 minutes, of kernel time in sequence; they are
independent of each other and build in parallel. The library build of the
group on this 4-core machine took 13 min 45 s of wall time.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_stopping_update.py --replay --jobs 2` | 5 exact statements (the 2 targets and 3 components) and 53 transitive axiom reports over the 20 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 20 modules replayed through the independent kernel checker, which re-evaluates every certificate piece; the run took 22 minutes with two parallel jobs on this 4-core machine. | [stopping-update-audit.log](stopping-update-audit.log) |
| `python -m unittest discover -s tools -p 'test_stopping_update.py'` | 11 guard tests pass. | |
| `python tools/verify_project_axioms.py` | 21,109 constants (17,130 theorems) in 1,722 modules, same axioms. 156 exported instances, the new one the generated `SizeOf` instance of `Plan`; 6 registered orphans, unchanged. 3,826 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python tools/verify_lean_sources.py` | 1,723 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added 54
entries to `tools/definition_lock.json`: the two statements, the plan and its
policy, the certificate recursion and pieces, and the copied research
definitions and their private helpers. No existing entry changed. The new
exported instance is the `SizeOf` instance Lean generates for the structure
`Plan`. The run recorded here is a later one without that flag.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The specification was written before the proofs, reviewed, and
pinned by hash from this audit onward. The rational calculation of the
research package is not rerun here; CI reruns it in the research-evidence job.

## Review

The item was planned by one agent and criticized by a second, which checked
the cited names, questioned the memory model behind the plan and asked for a
measured gate before the pieces were written. A third agent measured the
largest piece first (12.8 s, about 1.1 GiB of its own memory), then wrote the
split. Before the specification was pinned, a fourth agent that had not
written them:
- rebuilt the modules and printed the axioms of the targets, the certificate and every piece;
- compared the statements and the copied modules with the research package;
- checked non-vacuity with a concrete estimator in the class whose trigger changes the action and whose worst RMS risk is at most one.

It found no defect in the Lean. Its minor points concerned two docstrings,
corrected before the pin (one stated the 13.5 GB figure as a per-row fact, and
two said "below" where Lean proves "at most"), and the location of the
implementer's report. These were reviews by AI agents, not a specialist
referee report.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
