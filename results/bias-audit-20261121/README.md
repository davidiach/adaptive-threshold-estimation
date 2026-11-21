# The bias audit of the constant search: library audit

[`proposals/constants/BIAS_AUDIT.md`](../../proposals/constants/BIAS_AUDIT.md)
makes two claims about the threshold $t(n,N)=\sqrt{(k_1+k_2\log(N/n))/n}$ of
the early-stopping classifier, each proved on paper with exact-arithmetic
checks in `bias_audit.py` and marked there as not Lean-checked:

- **The finite-grid winner violates the uniform bias theorem** (lines 49–69).
  For $(k_1,k_2)=(1/4,1/2)$, positive sign, $d=1/10$ and cap $N=2^{97}$, the
  misclassification probability is at least $(2/5)^{128}$, more than 2907
  times the v4 envelope $(Nd^2)^{-2}=10000/2^{194}$. The v6 verification
  appendix cites this as the reason a finite grid does not give a universal
  constant ([`paper/v6/verification.tex`](../../paper/v6/verification.tex)).
- **A smaller threshold preserves the v4 bias theorem** (lines 6–41). For
  $k_1\ge0$ and $k_2\ge1$, with $x=Nd^2$,
  $e_N\le e^{-2x}+\tfrac23e^{-2k_1}x^{-2}$ and $e_N\le\min(1,x^{-2})$.

Lean now checks both, in
[`lean/ThresholdHC/BiasAudit`](../../lean/ThresholdHC/BiasAudit/Full.lean).
The note, which `paper/v5/sources.json` pins by hash, is unchanged and still
says "Not Lean-checked". The audit runs below were made at commit
[`c796f72`](https://github.com/davidiach/adaptive-threshold-estimation/commit/c796f72).

## Statements

The note's $e_N$ is the frozen `errProbK k1 k2 L d S` of
[`Statements2.lean`](../../lean/ThresholdHC/Statements2.lean): the error of
the cap-$2^L$ classifier `classifyK` on an iid stream with success probability
$1/2\pm d$. It is the model of the frozen evaluator `constants/evaluator.py`:
early stops only before the cap, a strict comparison with the threshold, and
a tie at the cap counted as negative. At $k_1=k_2=1$ the envelope is the frozen
target `Targets.lemma6_error`.
[`Specification.lean`](../../lean/ThresholdHC/BiasAudit/Specification.lean)
states:

| Target | Statement |
|---|---|
| `grid_winner_counterexample` | $(2/5)^{128}\le e_N$ at $(1/4,1/2)$, $L=97$, $d=1/10$, positive sign, and $2907\min\{1,(2^{97}/100)^{-2}\}<(2/5)^{128}$. |
| `grid_winner_fails_envelope` | Added reading: $(1/4,1/2)$ does not satisfy the form of `Targets.lemma6_error`, $e_N\le\min\{1,(2^Ld^2)^{-2}\}$ for every $L$, $0<d\le1/2$ and sign. |
| `smaller_threshold_error` | For $k_1\ge0$, $k_2\ge1$, every $L$, $0<d\le1/2$ and either sign, with $x=2^Ld^2$: $e_N\le e^{-2x}+\tfrac23e^{-2k_1}x^{-2}$ and $e_N\le\min\{1,x^{-2}\}$. |

The exact ratio of the first target is $2^{318}/5^{132}\approx2907.35$. The
note proves $\log2<7/10$ by five Taylor terms; Lean uses Mathlib's bound on
$\log 2$. The note's side remark that lowering $k_1$ cannot increase the
stopping time is not stated.

## How the proofs go

- [`Measure.lean`](../../lean/ThresholdHC/BiasAudit/Measure.lean): `errProbK`
  at any coefficients is the tape probability of a wrong first-crossing
  decision, the coefficient-generic form of `Tier2.errProbK_eq_measure`.
- [`Counterexample.lean`](../../lean/ThresholdHC/BiasAudit/Counterexample.lean):
  on the cylinder of 128 leading tails every dyadic mean is zero and the
  threshold at $n=2^7$ is below $1/2$, so the classifier has stopped
  negatively; the cylinder has probability $(2/5)^{128}$.
- [`SmallerThreshold.lean`](../../lean/ThresholdHC/BiasAudit/SmallerThreshold.lean):
  the coefficient-generic form of the Tier 2 argument, a union bound over the
  early stops and the cap decision with Hoeffding tails,
  $(d+t)^2\ge d^2+t^2$, $(n/N)^{2k_2}\le(n/N)^2$ and the dyadic sum
  $\sum n^2e^{-bn}\le8/(3b^2)$.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_bias_audit.py --replay --jobs 2` | 6 exact statements (the 3 targets and 3 components) and 33 transitive axiom reports over the 5 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 5 modules replayed through the independent kernel checker. | [bias-audit-audit.log](bias-audit-audit.log) |
| `python -m unittest discover -s tools -p 'test_bias_audit.py'` | 11 guard tests pass. | |
| `python tools/verify_project_axioms.py` | 19,002 constants (15,308 theorems) in 1,601 modules, same axioms. 151 exported instances; 6 registered orphans, unchanged. 3,551 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python tools/verify_lean_sources.py` | 1,602 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added 5
entries to `tools/definition_lock.json`: the three statements,
`tailsCylinder` and the union-bound sum `errorUnionBoundK`. No existing entry
changed. The run recorded here is a later one without that flag.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The specification was written before the proofs, reviewed, and
pinned by hash from this audit onward. `bias_audit.py` is unchanged and
remains an independent exact-arithmetic check.

## Review

The item was planned by one agent and criticized by a second, which found
the statements faithful and asked for a coefficient-generic measure lemma
before any evaluation at $L=97$. A third agent wrote the proofs. Before the
specification was pinned, a fourth agent that had not written them rebuilt
the modules, replayed them through the kernel checker, printed the axioms,
restated each target by `Iff.rfl`, checked the ratio $2^{318}/5^{132}$
exactly, and checked that `smaller_threshold_error` at $k_1=k_2=1$ yields
the frozen `Targets.lemma6_error`, so the refuted envelope is one that holds
at $(1,1)$. It found no defect in the Lean; its one minor point, a docstring
that overstated a lemma, was corrected before the pin. These were reviews by
AI agents, not a specialist referee report.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
