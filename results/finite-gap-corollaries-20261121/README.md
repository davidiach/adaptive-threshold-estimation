# Finite-gap corollaries: library audit

Section 6 of the [finite-gap manuscript](../../paper/finite-gap-rare-events/README.md)
has two corollaries with paper proofs: the one-gap specialization
`cor:one-gap` and the mean-square form `cor:mse`, which has two displays.
Lean now checks the first corollary and both displays of the second, in
[`lean/ThresholdHC/FiniteGapCorollaries`](../../lean/ThresholdHC/FiniteGapCorollaries/Full.lean).
The manuscript and its hash-listed files are unchanged; their guides still
describe the corollaries as paper proofs, as they were at that checkpoint.
The audit runs below were made at commit
[`5953749`](https://github.com/davidiach/adaptive-threshold-estimation/commit/5953749).

## Statements

[`Specification.lean`](../../lean/ThresholdHC/FiniteGapCorollaries/Specification.lean)
states three targets, for $0<\rho\le1/4$ and $B>0$. Write $h=B^{-1/2}$, $\nu$
for the quantile tail (the smallest-gap mass $\rho$, with a fraction of the
boundary atom), $\kappa=\mu-\nu$, $T_h=\int\min\{1,h/d\}\,\nu(dd)$,
$\Gamma_\kappa$ for the cost entropy of $\kappa$ and $J_\nu=\int d^{-1}\,\nu(dd)$.

| Target | Statement | Before |
|---|---|---|
| `one_gap_rate` | For every gap $0<d\le1/2$: $10^{-17}\min\{\rho,\sqrt\rho/(d\sqrt B)\}\le R_{\delta_d,\rho}(B)\le28000\min\{\rho,\sqrt\rho/(d\sqrt B)\}$. | Paper proof of `cor:one-gap`, which asserts the order with universal constants. |
| `mean_square_form` | For every finitely supported law: $c_0^2\min\{\rho^2,T_h^2+\rho\Gamma_\kappa/B\}\le R^2\le2C_0^2\min\{\rho^2,T_h^2+\rho\Gamma_\kappa/B\}$ with $c_0=10^{-20}$, $C_0=30001$. | Paper proof of the first display of `cor:mse`. |
| `large_budget_mean_square_form` | If moreover $B\ge d^{-2}$ at every atom $d$: the same with $\min\{\rho^2,(J_\nu^2+\rho\Gamma_\kappa)/B\}$. | Paper proof of the second display of `cor:mse`. |

The risk is the rare-event minimax risk of the
[rare-event model](../../lean/ThresholdHC/RareAboveTwo/Model.lean), the
same model as the finite-law theorem of the
[direct finite-quantile record](../direct-finite-quantile-20261104/README.md).
The hypothesis $B\ge d^{-2}$ at every atom is the manuscript's $B\ge d_1^{-2}$,
since $d_1$ is the smallest atom.

## How the proofs go

The proofs are in [`Corollaries.lean`](../../lean/ThresholdHC/FiniteGapCorollaries/Corollaries.lean).

- **One gap.** At a point mass the selection functional is the single-gap
  rate ([`EntropyTail.single_atom`](../../lean/ThresholdHC/EntropyTail/SingleAtom.lean)),
  so the explicit entropy–tail law of
  [`EntropyTailSharp`](../../lean/ThresholdHC/EntropyTailSharp/Full.lean)
  gives the constants $10^{-17}$ and $28000$. The manuscript's proof goes
  through its Theorem 1.1 and the bracket between $(\sqrt3/2)\sqrt\rho$ and
  $(3/2)\sqrt\rho$, which gives weaker constants.
- **Mean square.** The closed quantile value is $\min\{\rho,x+y\}$ with
  $x=T_h$ and $y^2=\rho\Gamma_\kappa/B$. In $[0,\infty]$,
  $x^2+y^2\le(x+y)^2\le2(x^2+y^2)$ and squaring commutes with the minimum, so
  squaring the finite-law bounds of
  [`FiniteQuantile.direct_finite_law`](../../lean/ThresholdHC/FiniteQuantile/Full.lean)
  gives the first display.
- **Large budget.** The quantile tail is absolutely continuous with respect to
  the law, so it is carried by the support. If $h\le d$ on the support,
  $\min\{1,h/d\}=h/d$ there, so $T_h=hJ_\nu$ (`tail_linear`) and
  $T_h^2=J_\nu^2/B$.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_finite_gap_corollaries.py --replay --jobs 3` | 6 exact statements (the 3 targets and 3 components) and 15 transitive axiom reports over the 3 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 3 modules replayed through the independent kernel checker. | [finite-gap-corollaries-audit.log](finite-gap-corollaries-audit.log) |
| `python -m unittest discover -s tools -p 'test_finite_gap_corollaries.py'` | 11 guard tests pass. | |
| `python tools/verify_project_axioms.py` | 17,042 constants (13,682 theorems) in 1,457 modules, same axioms. 147 exported instances. 3,220 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python tools/verify_lean_sources.py` | 1,458 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added three
entries to `tools/definition_lock.json`, the three statements of
`FiniteGapCorollaries`. No existing entry changed. The run recorded here is a
later one without that flag.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The specification was written after the proofs; it is pinned by
hash from this audit onward.

- The one-gap target holds the entropy–tail constants, not the constants
  $c_0$ and $C_0$ of the finite-gap theorem, and its proof does not go
  through that theorem.
- Both mean-square targets inherit the finite-law hypotheses: finite support,
  a known law and a uniform expected observation budget. They are squared
  forms of the finite-law theorem and add no estimate of their own.
- $J_\nu$ is a Bochner integral. For a finitely supported law the integrand
  is bounded on the support, so it is the integral of the manuscript.

## Review

Before the specification was pinned, two reviewers that had not written the
proofs compared the statements with the manuscript and read the proofs. The
first found both corollaries faithful and not vacuous, and noted that the first
draft stated only the first display of `cor:mse`; the second display was then
added as `large_budget_mean_square_form`. The second reviewer checked that
target: the support of a finitely supported law is its set of atoms, so the
hypothesis is the manuscript's $B\ge d_1^{-2}$; $J_\nu$ is the integral of the
manuscript; and a point mass at $1/2$ with $\rho=1/4$, $B=4$ is an instance.
Neither found a blocking problem, and their wording fixes were applied. These
were reviews by AI agents, not a specialist referee report.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
