# Sharpness of the magnitude-oracle coefficient one half: library audit

The second review of the rms-constants package
([`adaptive-threshold-second-review.tex`](../../research/2026-11-17-rms-constants/adaptive-threshold-second-review.tex),
section "Sharpness and an unbiased one-flip estimator", paragraph "Sharp upper
coefficient for the oracles") states that for every gap law and every budget
$B\ge1$ both magnitude-oracle minimax risks are at most $\omega_\mu(B^{-1/2})/2$,
and that the coefficient $1/2$ cannot be lowered: at a fixed $B\ge1$, point
masses at gaps $d\to0$ have oracle risk with liminf at least $1/2$ while
$\omega(B^{-1/2})=1$. Lean had only lower bounds and the equality $1/6$ at
$\mu=\delta_{1/2}$, $B=4$ for the oracles. Lean now checks the sharpness half,
in [`lean/ThresholdHC/OracleSharpness`](../../lean/ThresholdHC/OracleSharpness/Full.lean).
The upper bound $R\le\omega/2$ is a separate, larger item and is not stated
here. The audit runs below were made at commit
[`4a16775`](https://github.com/davidiach/adaptive-threshold-estimation/commit/4a16775).

## Statements

[`Specification.lean`](../../lean/ThresholdHC/OracleSharpness/Specification.lean)
states two targets, against the existing `revealedMinimaxRisk`,
`selectedMinimaxRisk`, `minimaxRisk` and `modulus`.

| Target | Statement |
|---|---|
| `oracle_upper_sharpness` | For every $B\ge1$ and every $c<1/2$ there is $g_0>0$ such that every point mass $\delta_g$ with $g\le g_0$ has both oracle minimax risks strictly above $c\,\omega_{\delta_g}(B^{-1/2})$. |
| `small_gap_sign_lower` | Auxiliary, not a claim of the source: for a point mass at $g$ with $s=2g<1$, $B\ge0$ and $c\ge0$, the ordinary minimax risk is at least $c$ whenever $s\,\mathrm{artanh}(s)\,B\le1-4c^2$. |

The first target is the source's liminf in eventual form. The modulus is one
at gaps below $B^{-1/2}$, so it says
$\liminf_{g\to0}R^{\mathrm{oracle}}_{\delta_g}(B)\ge1/2$ for both oracles; it is
not a bare existential. With the upper bound it would give the
exact coefficient $1/2$.

## How the proofs go

- [`SignTest.lean`](../../lean/ThresholdHC/OracleSharpness/SignTest.lean):
  under the two deterministic sign laws at a gap with flip bias $s$, the
  transcript laws differ by the factor $e^{2\,\mathrm{artanh}(s)N}$, with $N$
  the net observed sign, and the Wald identity gives $\mathbb E_\pm N=\pm s\,\mathbb E_\pm T$.
  A two-point bound for each word, with the triangular discrimination below
  half the symmetric log-likelihood term, gives
  $2\le\mathbb E_+(X-1)^2+\mathbb E_-(X+1)^2+s\,\mathrm{artanh}(s)(\mathbb E_+T+\mathbb E_-T)$
  at every bounded horizon. No KL divergence is used.
- [`SignPopulation.lean`](../../lean/ThresholdHC/OracleSharpness/SignPopulation.lean)
  extends this to unbounded stopping with the prefix limit of `SharpRMS` and
  proves `small_gap_sign_lower`.
- [`Sharpness.lean`](../../lean/ThresholdHC/OracleSharpness/Sharpness.lean)
  transfers the bound to both oracles with the checked single-gap reduction
  `oracle_gap_reduction` at $\mu=\delta_g$, where the modulus is one, and
  gives $g_0=\min\{1/5,(1-4c'^2)/(5B)\}$ with $c'=(\max\{c,0\}+1/2)/2$, using
  $\mathrm{artanh}\,s\le(11/10)s$ for $s\le2/5$.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_oracle_sharpness.py --replay --jobs 3` | 4 exact statements (the 2 targets and 2 components) and 9 transitive axiom reports over the 5 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 5 modules replayed through the independent kernel checker. | [oracle-sharpness-audit.log](oracle-sharpness-audit.log) |
| `python -m unittest discover -s tools -p 'test_oracle_sharpness.py'` | 11 guard tests pass. | |
| `python tools/verify_project_axioms.py` | 17,686 constants (14,232 theorems) in 1,514 modules, same axioms. 147 exported instances. 3,314 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python tools/verify_lean_sources.py` | 1,515 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added
eight entries to `tools/definition_lock.json`: the two statements, the
group's two private helpers and four compiler-generated auxiliary
definitions. No existing entry changed. The run recorded here is a later one
without that flag.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The specification was written after the proofs; it is pinned by
hash from this audit onward. The oracle upper bound $R\le\omega_\mu(B^{-1/2})/2$,
its finite-budget forms and the statement that $1/2$ is the exact
coefficient are not targets of this group. The research package, which
calls these claims paper proofs, is unchanged.

## Review

The item was planned by one agent and criticized by a second, which
recommended splitting the sharpness half from the upper half, the eventual
form of the limit and the single-gap reduction used here. A third agent wrote
this half. Before the specification was pinned, a fourth agent that had not
written the proofs rebuilt the modules (byte-identical outputs), replayed
them through the kernel checker, checked that the statements unfold to the
intended qualified definitions, printed the axioms, ran the audit's scans and
probed non-vacuity: gaps below $g_0$ exist, both oracle risks lie strictly
between $c$ and $1$ at small gaps, and the auxiliary bound gives
$R\ge1/4$ at $\delta_{1/10}$ with $B=1$. It found one defect: the docstring of
the auxiliary statement omitted the hypothesis $B\ge0$, without which its
prose claim is false. The docstrings were reworded before this audit. These
were reviews by AI agents, not a specialist referee report.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
