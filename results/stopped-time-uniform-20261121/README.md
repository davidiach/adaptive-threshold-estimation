# Stopped time-uniform remark: library audit

The [results guide](../../docs/RESULTS.md#confidence-rates-and-sequential-stopping)
adds a paper-level remark to the time-uniform lower bound: stopping a
time-uniform procedure at budget $n$ gives a fixed-budget interval, so the
fixed-budget coefficient $10^{-17}$ already implies display (TU1) at every $n$
with $\log\log n\le(10^{10}-1)\log(1/\delta)$. The checked time-uniform
theorem, [`law_dependent_interval_lower`](../../lean/ThresholdHC/AnytimeLower/Intervals.lean),
gives (TU1) only at arbitrarily late budgets. Lean now checks the remark, in
[`lean/ThresholdHC/StoppedTimeUniform`](../../lean/ThresholdHC/StoppedTimeUniform/Full.lean).
The audit runs below were made at commit
[`703d353`](https://github.com/davidiach/adaptive-threshold-estimation/commit/703d353).

## Statements

[`Specification.lean`](../../lean/ThresholdHC/StoppedTimeUniform/Specification.lean)
states three targets, for $0<\rho\le1/4$ and $0<\delta\le1/4$. Write
$\ell=\log(1/\delta)$, $\Lambda_n=\ell+\log\log n$ and $\mathcal K$ for the
selection functional.

| Target | Statement |
|---|---|
| `prefix_confidence` | An estimate formed from the private seed and the first $n\ge1$ physical observations of an adaptive population experiment, with failure probability at most $\delta$ at radius $\varepsilon\ge0$ under every rare sign law, has $\varepsilon\ge10^{-17}\mathcal K(n/\ell)$. |
| `stopped_fixed_budget` | A time-uniform interval procedure with joint coverage at level $1-\delta$ and half-width envelope $t\ge0$ has $t_n\ge10^{-17}\mathcal K(n/\ell)$ at every $n\ge1$. |
| `stopped_time_uniform` | The same procedure has $t_n\ge10^{-22}\mathcal K(n/\Lambda_n)$, display (TU1), at every $n\ge2$ with $\log\log n\le(10^{10}-1)\ell$. |

The model is that of the time-uniform lower bound: the original observable
hidden-gap experiment, in which the estimate at budget $n$ sees the seed and
the observed prefix of length $n$. The procedure hypotheses are those of
`law_dependent_interval_lower`, and $t$ is its deterministic half-width
envelope. Display (TU1) is stated for $n\ge3$; the target also covers $n=2$,
where $\log\log2<0$.

## How the proofs go

The proofs are in [`Prefix.lean`](../../lean/ThresholdHC/StoppedTimeUniform/Prefix.lean).
The fixed-budget theorem
[`estimator_confidence_lower_explicit`](../../lean/ThresholdHC/ConfidenceEntropy/Full.lean)
is stated for the terminal output of an algorithm with an expected budget, so
the proof reruns its chain for prefix estimates.

- **Testing step** (`prefix_pair_work`). For two rare priors whose means
  differ by more than $4\varepsilon$, a uniformly confident prefix estimate
  separates their quarter-smoothed versions, so the KL divergence of the two
  prefix laws is at least $\ell/4$. That divergence is at most $(8/3)\kappa$
  times the expected work of the prefix
  ([`observable_reference_work_kl`](../../lean/ThresholdHC/ConfidenceTransfer/Observable.lean)),
  and the work is at most $n$
  ([`prefix_expected_work_le`](../../lean/ThresholdHC/AnytimeLower/Embedding.lean)).
  This replaces the expected-budget step of
  [`pair_reference_confidence_work`](../../lean/ThresholdHC/ConfidenceTransfer/Testing.lean).
- **Program and constants.** `prefix_quartet_confidence` is
  [`quartet_confidence`](../../lean/ThresholdHC/ConfidenceProgram/Lower.lean)
  with that step and $B=n$. The four-prior duality, the closed-quantile
  program bound and the comparison of the selection functional with the
  closed quantile value then give $10^{-17}\mathcal K(n/\ell)\le\varepsilon$,
  as for the fixed-budget theorem.
- **Intervals.** Joint coverage bounds the failure probability of the
  midpoint at each budget (`coverage_prefix_failure`).
- **The remark** (`inflation_selection`). The hypothesis gives
  $\Lambda_n\le10^{10}\ell$. If $\Lambda_n\ge\ell$, the selection functional
  grows at most like the square root of the budget ratio
  ([`selection_budget_scale`](../../lean/ThresholdHC/HardBudget/SelectionScale.lean)),
  so $\mathcal K(n/\Lambda_n)\le10^5\mathcal K(n/\ell)$. At $n=2$,
  $0<\Lambda_2<\ell$, because $\log\log2>-1$ and $\ell\ge\log4>1$, and the
  functional is antitone in the budget
  ([`selection_antitone`](../../lean/ThresholdHC/Anytime/Width.lean)). Either
  way $10^{-22}\mathcal K(n/\Lambda_n)\le10^{-17}\mathcal K(n/\ell)\le t_n$.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_stopped_time_uniform.py --replay --jobs 3` | 6 exact statements (the 3 targets and 3 components) and 12 transitive axiom reports over the 3 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 3 modules replayed through the independent kernel checker. | [stopped-time-uniform-audit.log](stopped-time-uniform-audit.log) |
| `python -m unittest discover -s tools -p 'test_stopped_time_uniform.py'` | 11 guard tests pass. | |
| `python tools/verify_project_axioms.py` | 17,098 constants (13,731 theorems) in 1,469 modules, same axioms. 147 exported instances. 3,227 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python tools/verify_lean_sources.py` | 1,470 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added seven
entries to `tools/definition_lock.json`: the three statements of
`StoppedTimeUniform`, the statement of `LatentThreshold`, the two statements of
`ZeroAtomSplit` and the statement of `CapIdentificationEstimate`. No existing
entry changed. The run recorded here is a later one without that flag; it
covers all four groups.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The specification was written after the proofs; it is pinned by
hash from this audit onward.

- The remark is stated for $n\ge2$, where $\log\log n$ is defined; at $n=1$
  it would rest on Lean's convention $\log0=0$.
- The interval targets assume joint coverage over all budgets, as the
  time-uniform theorem does; the proof uses only coverage at the budget $n$,
  and `prefix_confidence` already covers any single estimate from the first
  $n$ observations. The bound is on the deterministic envelope $t_n$, not on
  the random width.
- The fixed-budget coefficient is proved again for prefix estimates, by the
  chain of the fixed-budget theorem with a prefix testing step; it is not
  obtained by applying `estimator_confidence_lower_explicit`, which concerns
  terminal outputs under an expected budget.
- The closing sentence of the remark, that the iterated logarithm is forced
  only beyond that range, is not a target. The upper time-uniform theorem and
  this lower bound are not composed.

## Review

Before the specification was pinned, two reviewers that had not written the
proofs read the statements and the proofs. One compared the statements with
the remark and display (TU1): it found them faithful and not vacuous, checked
that an immediate estimator with the interval $[0,\rho]$ meets the hypotheses,
and showed that the bound also holds at $n=2$, after which the target was
extended from $n\ge3$ to $n\ge2$. The other compared the prefix quartet with
the fixed-budget one line by line and found that only the testing step
changes. Neither found a blocking problem; their wording fixes and an extra
guard test were applied. These were reviews by AI agents, not a specialist
referee report.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
