# The two-sided time-uniform order in one model: library audit

The time-uniform confidence row of the results guide
([`docs/RESULTS.md`](../../docs/RESULTS.md#time-uniform-confidence)) and
Appendix `app:anytime` of the v6 manuscript
([`paper/v6/appendix-anytime.tex`](../../paper/v6/appendix-anytime.tex)) give
an upper theorem and a matching lower bound (TU1) for the half-width of a
time-uniform interval, and say that they match up to constants. Both halves
were Lean-checked, but in different models. The upper theorem
`ThresholdHC.Anytime.known_anytime`
([record](../anytime-confidence-20261105/README.md)) is stated for a
budget-indexed family of stage controllers under its own stream law. The
lower theorem `ThresholdHC.AnytimeLower.law_dependent_interval_lower`
([record](../anytime-asymptotic-20261105/README.md)) is stated for one online
policy in the original observable hidden-gap experiment. No Lean theorem
composed the two. Lean now does, in
[`lean/ThresholdHC/TimeUniformTwoSided`](../../lean/ThresholdHC/TimeUniformTwoSided/Full.lean).
The audit runs below were made at commit
[`482d340`](https://github.com/davidiach/adaptive-threshold-estimation/commit/482d340).

## Statements

[`Specification.lean`](../../lean/ThresholdHC/TimeUniformTwoSided/Specification.lean)
uses the lower theorem's model. A procedure is one adaptive estimator with a
private seed, together with interval maps $L_n,U_n$ that at every integer
budget $n$ read the seed and the first $n$ physical observations. Joint
coverage and width control are expressed by
`ThresholdHC.AnytimeLower.OnlineIntervalCoverage`. Below,
$\Lambda(n,\delta)=\log(1/\delta)+2\log(2+\log(1+n)/\log2)$ is the upper
theorem's inflation, $\lambda(n)=\log(1/\delta)+\log\log n$ the lower
theorem's, and $\mathcal K$ the selection functional. Both statements assume
a probability law of gaps, $0<\rho\le1/4$ and $0<\delta\le1/4$.

| Target | Statement |
|---|---|
| `online_upper` | Some procedure with measurable endpoints and a nonnegative envelope $t$ has joint coverage and width control, with $t_n\le1500002\,\mathcal K(n/\Lambda(n,\delta))$ for every $n\ge1$ and $t_n\le3000004\,\mathcal K(n/\lambda(n))$ for every $n\ge3$. |
| `time_uniform_two_sided` | Some such procedure has $t_n\le3000004\,\mathcal K(n/\lambda(n))$ for $n\ge3$ and $t_n\ge10^{-22}\mathcal K(n/\lambda(n))$ at arbitrarily late budgets; and every procedure with measurable endpoints and a nonnegative envelope satisfying the coverage property obeys the same lower bound. |

The source claims only that the two halves match up to constants. The joint
constants $3000004$ and $10^{-22}$ are the ones proved here: the first uses
$\Lambda(n,\delta)\le4\lambda(n)$ for $n\ge3$ and $0<\delta\le1/4$. Validity at
a data-dependent stopping budget is not a separate conjunct; it follows from
the single joint coverage event. Not restated: the nesting of the intervals,
real budgets $B\ge0$ (only integer budgets appear), and the per-budget flip
cap of the stage controllers. The cap is replaced by the typing of the
interval maps, which at budget $n$ read only the first $n$ observations. The
constructed policy never stops, and neither statement imposes a work or
budget hypothesis on the policy.

## How the proofs go

- [`Online.lean`](../../lean/ThresholdHC/TimeUniformTwoSided/Online.lean):
  the limit policy reads the stage plan with a reservation longer than the
  history. Before the reservation of stage $k$ is exhausted it makes the same
  choices as the stage-$k$ endpoint controller, so the two paths share their
  first $\mathrm{paid}(k)$ symbols. The interval at budget $n$ is the
  stage-indexed interval at stage `stageCount n`, read from the first $n$
  observations; it equals the stage interval pathwise because
  $\mathrm{paid}(\mathrm{stageCount}\,n)\le n$. The two experiments have the
  same seed-and-table law, so the coverage event of the stage family transfers.
- [`Scale.lean`](../../lean/ThresholdHC/TimeUniformTwoSided/Scale.lean):
  $\Lambda(n,\delta)\le4\lambda(n)$ for $n\ge3$, so the selection functional at
  $n/\Lambda(n,\delta)$ is at most twice its value at $n/\lambda(n)$.
- [`Full.lean`](../../lean/ThresholdHC/TimeUniformTwoSided/Full.lean): the
  envelope is $\rho/2$ at budget $0$ and $1500002\,\mathcal K(n/\Lambda(n,\delta))$
  for $n\ge1$; the lower half is `law_dependent_interval_lower` applied to the
  constructed procedure and to every other one.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_time_uniform_two_sided.py --replay --jobs 2` | 5 exact statements (the 2 targets and 3 components) and 17 transitive axiom reports over the 4 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 4 modules replayed through the independent kernel checker. | [time-uniform-two-sided-audit.log](time-uniform-two-sided-audit.log) |
| `python -m unittest discover -s tools -p 'test_time_uniform_two_sided.py'` | 11 guard tests pass. | |
| `python tools/verify_project_axioms.py` | 20,072 constants (16,188 theorems) in 1,676 modules, same axioms. 155 exported instances; 6 registered orphans, unchanged. 3,738 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python tools/verify_lean_sources.py` | 1,677 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added 5
entries to `tools/definition_lock.json`: the two statements, the limit policy,
the limit estimator and the online interval. No existing entry changed. The
run recorded here is a later one without that flag.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The specification was written before the proofs, reviewed, and
pinned by hash from this audit onward.

## Review

The item was planned by one agent and criticized by a second, which required
no mathematical correction and asked for the docstring to list what is not
restated. A third agent wrote the proofs. Before the specification was
pinned, a fourth agent that had not written them:
- rebuilt the modules and printed the axioms;
- checked by `rfl` that the inline $\Lambda$ is the upper theorem's inflation and that the statements unfold to joint coverage in the original experiment;
- instantiated the target at $\mu=\delta_{1/4}$, $\rho=\delta=1/4$ to confirm that no denominator vanishes and that the trivial interval $[0,\rho]$ cannot meet the upper envelope.

It found no defect in the Lean. Its two minor points concerned a docstring
that dropped the coverage, measurability and nonnegativity hypotheses of the
lower half, corrected before the pin, and the location of the implementer's
report. These were reviews by AI agents, not a specialist referee report.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
