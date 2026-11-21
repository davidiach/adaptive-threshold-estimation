# The power-margin rows through the closed quantile form: library audit

The rare-event section of the v6 manuscript
([`paper/v6/rare-events.tex`](../../paper/v6/rare-events.tex), subsection The
power-margin regimes) tabulates the RMS orders for the exact power law
$F(d)=(d/a)^\alpha$ on $(0,a]$. With $x=(a\sqrt B)^{-1}$ the rows are
$\min\{\rho,x^\alpha\}$ for $0<\alpha<1$, $\min\{\rho,x[1+\log_+(\rho/x)]\}$ for
$\alpha=1$, $\min\{\rho,\rho^{1-1/\alpha}x\}$ for $1<\alpha<2$,
$\min\{\rho,\sqrt{\rho L(1+\log L)/B}\}$ for $\alpha=2$ at $a=1/4$, and
$\min\{\rho,\sqrt\rho\,x\}$ for $\alpha>2$. Remark `rem:power-quantile` says
that each row also follows, with constants depending on $\alpha$, from the
comparison of the minimax risk with the closed quantile functional
$\mathcal Q$. The rows themselves were Lean-checked through their own
theorems; the remark's route was not. Lean now checks it, in
[`lean/ThresholdHC/PowerQuantileRows`](../../lean/ThresholdHC/PowerQuantileRows/Full.lean).
The paper is unchanged. The audit runs below were made at commit
[`395166a`](https://github.com/davidiach/adaptive-threshold-estimation/commit/395166a).

## Statements

[`Specification.lean`](../../lean/ThresholdHC/PowerQuantileRows/Specification.lean)
defines `powerRow α x ρ`, the table row with its formula written inline. The
$\alpha=2$ row is written as $\min\{\rho,x\sqrt{\rho LH}\}$ for every scale $a$.

| Target | Statement |
|---|---|
| `power_row_rate` | For every $\alpha>0$ there are $c,C>0$ with $c\cdot$`powerRow` $\le$ the uniform rate (W7) $\le C\cdot$`powerRow` for all $0<\rho\le1/4$ and $x>0$. |
| `power_row_quantile` | For every $\alpha>0$ there are $c,C>0$ with the closed quantile functional of every exact power law ($0<a\le1/2$, $0<\rho\le1/4$, $B>0$) between $c$ and $C$ times the row at $x=(a\sqrt B)^{-1}$. |
| `power_row_risk` | The same for the rare-event minimax risk. |
| `quadratic_row_form` | At $a=1/4$ the $\alpha=2$ row is the table entry with the term inside the minimum multiplied by four. |

The constants are existential and depend only on $\alpha$. The domains are
supersets of the paper's ($a\le1/2$ for every row, $B>0$). For $\alpha>4$ the
quantile and risk statements rest on `power_quantile_all`, a copy of
`PowerWindow.power_quantile` without its hypothesis $\alpha\le4$: this is a
Lean-only extension of Theorem 14.13, whose paper statement covers
$0<\alpha\le4$, and is not reported as that theorem. Only the remark's
conclusion is formalized; the core entropy is evaluated through the uniform
bounds of `PowerWindow`, not through the remark's per-regime sketch.

## How the proofs go

- [`AllExponents.lean`](../../lean/ThresholdHC/PowerQuantileRows/AllExponents.lean):
  the core and quantile comparisons of `PowerWindow` for every $\alpha>0$.
- [`Bounds.lean`](../../lean/ThresholdHC/PowerQuantileRows/Bounds.lean) and
  [`Rows.lean`](../../lean/ThresholdHC/PowerQuantileRows/Rows.lean): the tail,
  $\Phi$ and entropy-factor bounds in each regime, and one row lemma per
  regime; at $\alpha=2$ the constants are $1/2$ and $3$.
- [`Bridges.lean`](../../lean/ThresholdHC/PowerQuantileRows/Bridges.lean): the
  inline rows agree with the rate definitions of the separately checked row
  theorems, which no proof here uses.
- [`Full.lean`](../../lean/ThresholdHC/PowerQuantileRows/Full.lean): the rate
  statement, then $\mathcal Q$ through the comparison, then the risk through
  the closed-quantile lower and upper bounds with $10^{-17}$ and $30001$.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_power_quantile_rows.py --replay --jobs 2` | 7 exact statements (the 4 targets and 3 components) and 48 transitive axiom reports over the 6 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 6 modules replayed through the independent kernel checker. | [power-quantile-rows-audit.log](power-quantile-rows-audit.log) |
| `python -m unittest discover -s tools -p 'test_power_quantile_rows.py'` | 11 guard tests pass. | |
| `python tools/verify_project_axioms.py` | 21,166 constants (17,182 theorems) in 1,728 modules, same axioms. 156 exported instances; 6 registered orphans, unchanged. 3,831 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python tools/verify_lean_sources.py` | 1,729 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added 5
entries to `tools/definition_lock.json`: `powerRow` and the four statements.
No existing entry changed. The run recorded here is a later one without that
flag.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The specification was written before the proofs, reviewed, and
pinned by hash from this audit onward.

## Review

The item was planned by one agent and criticized by a second, which kept the
specification free of the row theorems' imports, asked for bridge lemmas to
the separately checked rate definitions, and required the dependence on
$\alpha>4$ to be labelled a Lean-only extension. A third agent wrote the
proofs. Before the specification was pinned, a fourth agent that had not
written them:
- rebuilt the modules and printed the axioms;
- checked each row branch against the table;
- confirmed by a transitive scan that no proof uses the separately checked row theorems, and instantiated the risk statement at $\alpha=5$, $a=1/2$.

It found no defect in the Lean. Its two minor points concerned the
specification's docstrings: a wrong section number and a description of the
rate (W7) as equal to $\mathcal Q$ where it is only within the factors $1/\sqrt2$
and $2$. Both were corrected before the pin. These were reviews by AI
agents, not a specialist referee report.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
