# The literal forms of the robust-continuation planner: library audit

The subsubsection Robust use of the known-law estimator of the v6
arbitrary-law adaptation appendix
([`paper/v6/arbitrary-law-adaptation.tex`](../../paper/v6/arbitrary-law-adaptation.tex),
the same text in [`docs/ARBITRARY_LAW_ADAPTATION.md`](../../docs/ARBITRARY_LAW_ADAPTATION.md))
reuses the known-law estimator of a reference law $\alpha\preceq\mu$ for the
actual law $\mu$. Its Lean form left three of its literal steps out, as the
closing note of issue 82 records: the robust planner rate is existential in
the estimator, no induced reference sign allocation is constructed, and the
bound (A15) with correct-sign crossing times is not stated. Lean now states
all three, in
[`lean/ThresholdHC/RobustContinuationForms`](../../lean/ThresholdHC/RobustContinuationForms/Full.lean).
The paper is unchanged. The audit runs below were made at commit
[`1043a34`](https://github.com/davidiach/adaptive-threshold-estimation/commit/1043a34).

## Statements

[`Specification.lean`](../../lean/ThresholdHC/RobustContinuationForms/Specification.lean)
names the robust planner's plan-branch estimator, the zero-atom quantile split
built from the reference law, the rarity and the budget (core, upper and lower
tail, number of bands, the exact enclosure and its optimal weights), the
induced sign measure and law, and the correct-sign crossing times of the race.

| Target | Statement |
|---|---|
| `robust_tight_planner_output` | For the zero-atom split, a tight enclosure and weights within a factor two of the optimal ones, $0\le z_0<\rho\le1/4$ and $B>0$: if the plan runs, the named estimator has `RareBudget` $B$ and rare risk at most $C_0K_\alpha$ under every coupled true law; otherwise the constant $\rho/2$ does. |
| `cdf_robust_tight_planner_output` | The same for every probability law of positive gaps whose CDF is below that of the reference. |
| `robust_exact_planner_output` | The same with the split, the enclosure and the weights named, so the statement uses only $\eta$, $z_0$, $\rho$ and $B$. |
| `robust_large_atom_output` | For $\rho\le z_0$, the constant $\rho/2$ meets the same bound under every law. |
| `induced_sign_allocation` | Under a coupling with first marginal $(1-z_0)\eta$ and $\mu=\pi_2+\mu_0$: $\int q(z_2)F(z_1)\,d\pi=(1-z_0)\int q_0F\,d\eta$ for every measurable $F$, with $q_0$ the induced sign law; the positive fraction is preserved, and a rare prior gives $(1-z_0)\theta_\eta(q_0)+\int q\,d\mu_0\le\rho$ and $q_0$ rare at $\rho/(1-z_0)$. |
| `correct_time_race_bound` | The race cost is at most twice the minimum of the correct-sign bank crossing time and the correct ordinary crossing time. |
| `correct_time_antitone` | Both times decrease under the sign-directed order of tapes, for a downward negative and an upward positive test. |
| `coupled_correct_time_work` | (A15) in parameter form: for success parameters $p_0,p$ ordered in the sign's direction, on common uniform tapes. |
| `coupled_gap_correct_time_work` | (A15) at the gap coupling $d_0\le d$. |
| `coupled_zero_atom_correct_time_work` | (A15) at the reference zero atom, a fair coin. |
| `reference_race_correct_time_work` | (A15) for the reference level race, with the robust family's cost on the left. |

The planner forms keep the two-branch output (the plan or the constant, with
different seed types), as in the known-law planner's named form; they do not
give one estimator object. The named definitions take the proof arguments
their seed types need. No instance where the plan branch actually runs is
exhibited; both branches are covered and both bounds are finite. The induced
allocation is a truncated Radon–Nikodym density, unique only almost
everywhere, and lives on $\eta$; the zero atom enters through $\int q\,d\mu_0$.
The correct-time statements are pathwise: the integrated bound on
$\mathbb E_dT_{\rm ord}^s$, the bank-work bounds on correct crossing times and
the recovery of the level-work certificate by integrating (A15) are not
restated.

## How the proofs go

- [`NamedPlanner.lean`](../../lean/ThresholdHC/RobustContinuationForms/NamedPlanner.lean):
  the named estimator is definitionally the plan estimator of the audited
  robust planner proofs, so the planner forms follow from them, with the
  constant estimator on the other branch.
- [`InducedSign.lean`](../../lean/ThresholdHC/RobustContinuationForms/InducedSign.lean):
  the induced measure lies below the first marginal, and its truncated
  density gives the integral identity and the admissibility.
- [`CorrectTimes.lean`](../../lean/ThresholdHC/RobustContinuationForms/CorrectTimes.lean):
  the race stops by the time either correct boundary is crossed, and the
  correct crossing times are antitone in the sign-ordered tapes.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_robust_continuation_forms.py --replay --jobs 2` | 14 exact statements (the 11 targets and 3 components) and 69 transitive axiom reports over the 5 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 5 modules replayed through the independent kernel checker. | [robust-continuation-forms-audit.log](robust-continuation-forms-audit.log) |
| `python -m unittest discover -s tools -p 'test_robust_continuation_forms.py'` | 11 guard tests pass. | |
| `python tools/verify_project_axioms.py` | 21,371 constants (17,347 theorems) in 1,743 modules, same axioms. 159 exported instances, the three new ones the named, global, Prop-valued finite-measure instances of the split; 6 registered orphans, unchanged. 3,870 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python tools/verify_lean_sources.py` | 1,744 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added 28
entries to `tools/definition_lock.json`: the eleven statements and the named
definitions above. No existing entry changed. The run recorded here is a
later one without that flag.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The specification was written before the proofs, reviewed, and
pinned by hash from this audit onward.

## Review

The item was planned by one agent and criticized by a second, which required
every statement written out in full, the named split as the default, the
sharp admissibility clause, and (A15) in parameter form so that the reference
zero atom is covered. A third agent wrote the proofs. Before the
specification was pinned, a fourth agent that had not written them:
- rebuilt the modules and printed the axioms of the targets;
- checked by `rfl` that the named estimator is the audited plan estimator, and that the exact form implies the existential form of the CDF-robust planner rate;
- checked the race conventions of the correct-time statements against the race.

It found no defect in the Lean. Its one minor point concerned the location of
the implementer's report. These were reviews by AI agents, not a specialist
referee report.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
