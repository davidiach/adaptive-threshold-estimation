# The explicit quantile formula for finite laws: library audit

Section 14.2 of the v6 manuscript
([`paper/v6/finite-model.tex`](../../paper/v6/finite-model.tex), displays
(67)-(69): `fg:eq:quantile-split`, `fg:eq:core-entropy` and
`fg:eq:closed-functional`) gives the closed quantile functional of a finite
law explicitly. For gaps $d_1<\dots<d_n$ with weights $w_i$, the quantile tail
puts mass $\tau_i=\min\{w_i,(\rho-\sum_{\ell<i}w_\ell)_+\}$ on $d_i$ and the
core the rest, and
$Q(B)=\min\{\rho,\,T+h\sqrt{\rho\,\Gamma}\}$ with $h=B^{-1/2}$, the tail sum
$T=\sum_i\tau_i\min\{1,h/d_i\}$ and the core entropy $\Gamma$ of the band costs.
Lean checked the general-law definition of $Q$ and the direct finite-law bounds
at it ([record](../direct-finite-quantile-20261104/README.md)); the
model-fidelity guide noted that the finite formula itself was not restated
([`docs/MODEL_FIDELITY.md`](../../docs/MODEL_FIDELITY.md)). Lean now checks it,
in [`lean/ThresholdHC/FiniteQuantileFormula`](../../lean/ThresholdHC/FiniteQuantileFormula/Full.lean).
The paper is unchanged. The audit runs below were made at commit
[`5bb1e51`](https://github.com/davidiach/adaptive-threshold-estimation/commit/5bb1e51).

## Statements

[`Specification.lean`](../../lean/ThresholdHC/FiniteQuantileFormula/Specification.lean)
defines the tail weights $\tau_i$, the core cost of each band, the core entropy
$\Gamma$ over the first $N$ bands, the tail sum and `finiteQuantile d w ρ B N`.
The law is $\mu=\sum_iw_i\delta_{d_i}$ with $d$ strictly increasing, $w>0$ and
$\sum_iw_i=1$; $N$ is any band count with every atom above `bandEdge N`.

| Target | Statement |
|---|---|
| `finite_formula` | For $0<\rho\le1/4$ and $B>0$: `quantileTail μ ρ` $=\sum_i\tau_i\delta_{d_i}$, `quantileCore μ ρ` $=\sum_i(w_i-\tau_i)\delta_{d_i}$, and `closedQuantileValue μ ρ B` equals `finiteQuantile`. |
| `explicit_finite_law` | Under the same hypotheses, $10^{-20}Q\le R\le30001\,Q$ for the rare-event minimax risk with $Q$ the formula; one estimator with budget $B$ attains the upper bound; every estimator with budget $B$ has risk at least $10^{-20}Q$. |

The paper sums the core entropy over the bands with positive cost; summing over
the first $N$ bands is the same, because no other band holds an atom and a zero
cost contributes nothing. The formula itself holds for $\rho\le1$ and every
$B$ (a helper lemma); $\rho\le1/4$ is kept as in the paper. The lower halves of
the second target come from the direct finite-law theorem; the upper halves
from the general-law route through the constant 28000, not from the direct
finite construction of the finite-upper appendix. The constant bookkeeping of
Appendix E ($c_{\rm ann}$, $c_E$, 24576, 104, 27000) is a later part of the
scoped item and is not stated here.

## How the proofs go

- [`Atoms.lean`](../../lean/ThresholdHC/FiniteQuantileFormula/Atoms.lean):
  restriction, evaluation and integrals of finite atomic measures.
- [`Split.lean`](../../lean/ThresholdHC/FiniteQuantileFormula/Split.lean): the
  quantile threshold and boundary mass of a finite law, so the library's
  quantile tail and core are the explicit atoms.
- [`Formula.lean`](../../lean/ThresholdHC/FiniteQuantileFormula/Formula.lean):
  the tail modulus and band costs of those atoms, and $\Gamma$ as the cost
  entropy of the first $N$ bands.
- [`Full.lean`](../../lean/ThresholdHC/FiniteQuantileFormula/Full.lean): the
  formula, then `FiniteQuantile.direct_finite_law`,
  `EntropyTailExecution.closed_quantile_upper_30001` and the finite-law
  observable estimator at it.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_finite_quantile_formula.py --replay --jobs 2` | 5 exact statements (the 2 targets and 3 components) and 32 transitive axiom reports over the 5 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 5 modules replayed through the independent kernel checker. | [finite-quantile-formula-audit.log](finite-quantile-formula-audit.log) |
| `python -m unittest discover -s tools -p 'test_finite_quantile_formula.py'` | 11 guard tests pass. | |
| `python tools/verify_project_axioms.py` | 21,412 constants (17,381 theorems) in 1,748 modules, same axioms. 159 exported instances; 6 registered orphans, unchanged. 3,877 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python tools/verify_lean_sources.py` | 1,749 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added 7
entries to `tools/definition_lock.json`: the two statements and the five
definitions above. No existing entry changed. The run recorded here is a
later one without that flag.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The specification was written before the proofs, reviewed, and
pinned by hash from this audit onward.

## Review

The item was planned by one agent and criticized by a second, which found
that the specification would not elaborate as written (a missing decidability
instance), renamed the core cost, required the docstring to name the route of
the upper half, and split off the Appendix E constants, whose proposed
statements it judged not faithful to the source. A third agent wrote
the proofs. Before the specification was pinned, a fourth agent that had not
written them:
- rebuilt the modules and printed the axioms;
- checked the displays against the release build and the definitions against the paper;
- checked non-vacuity with a one-atom law and its own two-atom law ($d=(1/8,1/2)$, $w=(1/10,9/10)$, $\rho=1/4$), where the second atom is split with $\tau=(1/10,3/20)$.

It found no defect. These were reviews by AI agents, not a specialist referee
report.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
