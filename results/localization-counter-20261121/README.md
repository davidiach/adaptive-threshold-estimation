# Two auxiliary results of the localization appendix: library audit

The v6 appendix on localized rare-event scales
([`paper/v6/appendix-localization.tex`](../../paper/v6/appendix-localization.tex))
contains, besides the $\Psi$ lower bound (Theorem A.5, Lean-checked since
9 November 2026, [record](../psi-selection-20261109/README.md)), two
auxiliary results with paper proofs only:

- **Theorem `loc:thm:counter`**, a counterexample to the proposed rescaling.
  With $0<\rho\le1/4$, $d=\rho^2$, $\mu_\rho=\rho\delta_d+(1-\rho)\delta_{1/4}$
  and $B=\rho^{-4}$, the rare minimax RMS risk is at least $\rho/100$, while
  the heuristic $H_{\mu,\rho}(h)=\rho\,\omega_\mu(h/\sqrt\rho)$ of
  `loc:eq:heuristic` equals $\rho^2+4(1-\rho)\rho^{5/2}=O(\rho^2)$ at
  $h=B^{-1/2}$, so it can underestimate the minimax error by an unbounded
  factor.
- **Proposition `loc:prop:noise`**, why the original unmodified variance is
  not rarity-scaled: at one fixed negative coin of magnitude $d<1/2$, the
  level-0 term of the geometric single-term estimator alone forces
  $\mathbb EY^2\ge(1/2-d)/(1-2^{-1/2})$.

Lean now checks both, in
[`lean/ThresholdHC/LocalizationCounter`](../../lean/ThresholdHC/LocalizationCounter/Full.lean).
The paper is unchanged. The audit runs below were made at commit
[`8e9e9f6`](https://github.com/davidiach/adaptive-threshold-estimation/commit/8e9e9f6).

## Statements

[`Specification.lean`](../../lean/ThresholdHC/LocalizationCounter/Specification.lean)
defines the law `counterLaw ρ d`, the heuristic `heuristic μ ρ h`, the
magnitude $1/4$ and the all-negative sign law. The minimax risk is
`rareMinimaxRisk` of the unchanged observable rare-event experiment.

| Target | Statement |
|---|---|
| `counter_law_probability` | `counterLaw ρ d` is a probability law for $0\le\rho\le1$. |
| `counterexample` | `loc:thm:counter` with $B=1/\rho^4$: $\rho/100\le R\le\rho/2$, $H(B^{-1/2})=\rho^2+4(1-\rho)\rho^2\sqrt\rho$ and $H\le3\rho^2$. |
| `counter_unbounded` | The theorem's last sentence: for every $K>0$, small enough $\rho$ make $R>K\cdot H$. |
| `observable713_noise_floor` | `loc:prop:noise` in variance form, in the observable experiment at $\delta_d$ with every coin negative, for the 713-threshold estimator `Observable713.observableEstimator`: square-integrable output, mean $0$, and variance at least $(1/2-d)/(1-2^{-1/2})>0$. |
| `original_second_moment_floor` | The same floor on the extended second moment of the paper's original ($k_1=k_2=1$) untruncated estimator, in the single-coin sampling model. |
| `truncated_noise_floor` | The truncated form at level $L$ with the original thresholds, in the frozen finite model of `Statements2`; its second conjunct is the telescoped restatement of the first. |

"Of order $\rho$" is read as $\rho/100\le R\le\rho/2$ and $O(\rho^2)$ as
$\le3\rho^2$. The variance form uses the 713-threshold estimator, whose
thresholds are $\sqrt{(1/4+\log(N/n))/n}$ rather than the paper's
$\sqrt{(1+\log(n/k))/k}$, because its unbiasedness is proved for every gap
law with integrable $1/d$. For the paper's original untruncated estimator
neither unbiasedness nor square integrability is claimed; its floor bounds a
possibly infinite extended second moment, so it does not give the paper's
variance bound for that estimator. The appendix's fixed uniform-law failure,
Proposition `loc:prop:Gamma` and Proposition `loc:prop:generalupper` are not
formalized.

## How the proofs go

- [`Information.lean`](../../lean/ThresholdHC/LocalizationCounter/Information.lean):
  a transcript information bound for sign laws whose prior ratio is bounded,
  through the stopped KL chain of the creation model.
- [`CounterLaw.lean`](../../lean/ThresholdHC/LocalizationCounter/CounterLaw.lean):
  integrals under the two-atom law and the heuristic algebra.
- [`Counter.lean`](../../lean/ThresholdHC/LocalizationCounter/Counter.lean):
  two rare sign laws that differ only at the small atom, with prior $\rho/4$
  at the atom $1/4$ under both and a tilt of size $\eta=1/20$; KL at most
  $1/8$ under the budget and the two-point testing bound give $R\ge\rho/40$,
  which implies $\rho/100$. The upper bound is the constant estimator $\rho/2$.
- [`Noise.lean`](../../lean/ThresholdHC/LocalizationCounter/Noise.lean): at
  level $0$ the first decision reads one observation, which is a head with
  probability $1/2-d$ under the negative sign, weighted by $1/(1-2^{-1/2})$.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_localization_counter.py --replay --jobs 2` | 9 exact statements (the 6 targets and 3 components) and 42 transitive axiom reports over the 6 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 6 modules replayed through the independent kernel checker. | [localization-counter-audit.log](localization-counter-audit.log) |
| `python -m unittest discover -s tools -p 'test_localization_counter.py'` | 11 guard tests pass. | |
| `python tools/verify_project_axioms.py` | 19,317 constants (15,568 theorems) in 1,632 modules, same axioms. 151 exported instances; 6 registered orphans, unchanged. 3,603 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python tools/verify_lean_sources.py` | 1,633 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added 12
entries to `tools/definition_lock.json`: the six statements, `counterLaw`,
`heuristic`, `quarterGap`, `negativeSign`, and the tilted sign function and
law of the proof. No existing entry changed. The run recorded here is a later
one without that flag.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The specification was written before the proofs, reviewed, and
pinned by hash from this audit onward. As the scoping critic noted,
`counter_unbounded` also follows qualitatively from the checked $\Psi$ lower
bound with the allocation $\mathbf 1_{\{\rho^2\}}$; the explicit $\rho/100$ is
what the new proof adds.

## Review

The item was planned by one agent and criticized by a second, which renamed
the variance target to the 713 variant, added the floor for the original
estimator and asked for the second truncated conjunct to be labelled as a
restatement. A third agent wrote the proofs. Before the specification was
pinned, a fourth agent that had not written them rebuilt the modules, printed
the axioms of all 42 public declarations, checked the statements against the
appendix, and instantiated the counterexample at $\rho=1/4$. It found no defect
in the Lean; its two minor points concerned docstrings (an overstated
uniqueness claim for the 713 estimator, and the unproved square integrability
of the original estimator), which were corrected before the pin. These were
reviews by AI agents, not a specialist referee report.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
