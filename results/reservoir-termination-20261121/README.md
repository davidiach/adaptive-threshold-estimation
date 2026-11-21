# The countable-reservoir termination counterexample: library audit

The minimax audit's stopping-bridge note
([`stopping_bridge.tex`](../../research/2026-10-27-minimax-audit/formal/stopping_bridge.tex),
Proposition *One-law finite work does not transfer termination* and the
remark after its proof) takes fresh iid coins with deterministic gap $D$ and
sign prior $5/8$ under $P$ and $3/8$ under $Q$, queries each coin once, and
stops at $T=\inf\{n\ge1:\sum_{i\le n}(2X_i-1)=1\}$, where $X_i$ is the observed
bit. At $D=1/2$ it proves $P(T<\infty)=1$, $\mathbb E_PT=4$ and
$Q(T=\infty)=2/5$; at $D=1/4$, $\mathbb E_PT=8$ and $Q(T=\infty)=2/9$. The
checked two-law stopping theorem `Tier3.unbounded_stopping`, which derives
termination under both hypotheses from finite work under one, is for a fixed
finite coin family; the example shows it does not extend to a countable
reservoir. The note calls this a paper proof, not Lean-checked. Lean now
checks it, in
[`lean/ThresholdHC/ReservoirTermination`](../../lean/ThresholdHC/ReservoirTermination/Full.lean).
The research package and the `Tier3`, `Tier5` and `Tier6` groups are
unchanged. The audit runs below were made at commit
[`5b863a6`](https://github.com/davidiach/adaptive-threshold-estimation/commit/5b863a6).

## Statements

[`Specification.lean`](../../lean/ThresholdHC/ReservoirTermination/Specification.lean)
defines the walk policy (query the never-used label equal to the number of
observations, stop once successes minus failures is one), the event
`RunsForever` ($T=\infty$) and the same policy as a Tier 6 estimator. Work
is the lower integral of the total process work.

| Target | Statement |
|---|---|
| `walk_first_passage` | For every realization of the Tier 5 creation model's prefix laws, gap $0<d\le1/2$ and $0<\eta<1/2$: under the prior $1/2+\eta$ the walk stops almost surely with work $1/(4d\eta)$; under $1/2-\eta$ it runs forever with probability $8d\eta/(1+4d\eta)$ and has infinite work. |
| `half_gap_counterexample` | At $D=1/2$ with priors $5/8$ and $3/8$: $P(T=\infty)=0$, $\mathbb E_PT=4$, $Q(T=\infty)=2/5$. |
| `quarter_gap_counterexample` | At $D=1/4$: $P(T=\infty)=0$, $\mathbb E_PT=8$, $Q(T=\infty)=2/9$. |
| `naive_bridge_fails` | The analogue of `Tier3.UnboundedStoppingStatement` with created natural-number labels, seed-independent magnitudes and prior offsets and every Tier 5 regularity hypothesis, is false. |
| `reservoir_counterexample` | The proposition as an existence claim: a realization of both laws with $P(T=\infty)=0$, $\mathbb E_PT=4$, $Q(T<\infty)=3/5$, $Q(T=\infty)=2/5$ and $\mathbb E_QT=\infty$. |
| `original_experiment` | The same numbers in the original Tier 6 experiment at the point masses $\delta_{1/2}$ and $\delta_{1/4}$, and the walk estimator meets no uniform budget at $\delta_{1/2}$. |

Every realization of the creation model is covered; the iid structure of the
observed bits is derived from the prefix laws, not assumed. The case
$\eta=1/2$ of the general law is not stated. The note's further remark that
the example has finite full-transcript relative entropy $\log(5/3)$ is not a
target.

## How the proofs go

- [`FirstPassage.lean`](../../lean/ThresholdHC/ReservoirTermination/FirstPassage.lean)
  works with the absorbed walk acting on functions of the history. Exact
  identities for $1-$walk and its square bound the expected survival
  summably, which gives absorption and the work limit $1/(2r-1)$ at bit
  parameter $r>1/2$; the minus law follows by the likelihood-ratio tilt
  $((1-r)/r)^{\mathrm{walk}}$. The note uses the Catalan generating function
  instead.
- [`WalkLaw.lean`](../../lean/ThresholdHC/ReservoirTermination/WalkLaw.lean)
  and [`Realized.lean`](../../lean/ThresholdHC/ReservoirTermination/Realized.lean)
  identify the creation model's prefix laws with the absorbed walk at bit
  parameter $1/2\pm2d\eta$.
- [`Examples.lean`](../../lean/ThresholdHC/ReservoirTermination/Examples.lean)
  and [`Full.lean`](../../lean/ThresholdHC/ReservoirTermination/Full.lean)
  instantiate the numbers, build a realization and assemble the targets.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_reservoir_termination.py --replay --jobs 3` | 9 exact statements (the 6 targets and 3 components) and 80 transitive axiom reports over the 6 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 6 modules replayed through the independent kernel checker. | [reservoir-termination-audit.log](reservoir-termination-audit.log) |
| `python -m unittest discover -s tools -p 'test_reservoir_termination.py'` | 11 guard tests pass. | |
| `python tools/verify_project_axioms.py` | 18,744 constants (15,112 theorems) in 1,580 modules, same axioms. 151 exported instances; 6 registered orphans, unchanged. 3,489 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python tools/verify_lean_sources.py` | 1,581 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added 18
entries to `tools/definition_lock.json`: the walk, its policy and estimator,
the gaps and constant sign law, the absorbed-walk operator and the statements.
No existing entry changed. The run recorded here is a later one without that
flag.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The specification was written after the proofs; it is pinned by
hash from this audit onward. The finite-family theorem `Tier3.unbounded_stopping`
is unchanged and not contradicted. The research note, which calls the
proposition a paper proof, describes its own checkpoint and is unchanged.

## Review

The item was planned by one agent, criticized by a second, which made the
refuted bridge seed-independent and added the explicit existence statement,
and written by a third. Before the specification was pinned, a fourth agent
that had not written the proofs rebuilt the modules, checked each theorem
against its statement, printed the axioms of all 80 public declarations, ran
the audit's scans, checked by `rfl` that the refuted statement is the
created-label analogue of the Tier 3 statement, and probed non-vacuity
through the checked realization of the creation model. It found two minor
points: the specification called the walk's increments observed signs
rather than observed bits, and it asserted the case $\eta=1/2$ without a
status. Both were reworded before this audit. These were reviews by AI
agents, not a specialist referee report.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
