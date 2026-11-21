# Decimals and remarks of the upper-12 appendix: library audit

The appendix on the upper constant 12 of the RMS law
([`paper/v6/appendix-upper-constant.tex`](../../paper/v6/appendix-upper-constant.tex),
`app:upper-12`) uses decimal intermediate bounds whose rational versions are
Lean-checked ($26/5$, $41/100$, $13/2$;
[record](../upper-scale-20261119/README.md)), and closes with three remarks
comparing upper-bound routes that the theorem does not use. Its verification
paragraph lists both as not checked by Lean: the approximate values $5.182$,
$5.185$, $1.762$ and $12.5$, the bounds $5.19$, $0.401$ and $6.49$, and the
remarks. Lean now checks the bounds and the remarks, in
[`lean/ThresholdHC/UpperTwelveNumerics`](../../lean/ThresholdHC/UpperTwelveNumerics/Full.lean).
The paper and the `UpperScale` group are unchanged. The audit runs below were
made at commit
[`06d0997`](https://github.com/davidiach/adaptive-threshold-estimation/commit/06d0997).

## Statements

[`Specification.lean`](../../lean/ThresholdHC/UpperTwelveNumerics/Specification.lean)
defines the call-cost series term `callCostTerm`, with offsets $89/20$,
$17/4$, then $399/100$, and the wrong-side constant. Unlike the other
upper-constant specifications it names definitions beyond the experiment
model: the one-coin second moment `secondMomentK`, `pLevel` and `rLevel`,
the early-stopping error `UpperDisagreement.stopError`, the families
`UpperMixture.budgetMixture` and `BlindUpper.budgetEstimator`, the level
`BlindUpper.budgetLevel` and the level-$L$ call. All are fingerprinted in
`tools/definition_lock.json`.

| Target | Statement |
|---|---|
| `call_cost_decimal` | The series $(1-r)\sum_{j\ge1}r^jC_j\sqrt{v_j}$ converges and is below $5.19$. |
| `wrong_side_decimal` | The wrong-side constant $(1+\sqrt2)\frac{(2+\sqrt2)^2}{4\cdot13/10}e^{-2}\frac{\sqrt2}{4-\sqrt2}$ is below $0.401$, and bounds $d$ times the level sum of the early-stopping error terms for every $L$ and $d>0$. |
| `second_moment_decimal` | $(2+\sqrt2)\tfrac{89}{50}+\tfrac{41}{100}<6.49$, and it bounds $d\,\mathbb E[Y_L^2]$ for every $L$, sign and $0<d\le1/2$. |
| `mixture_remark` | $12.51<\sqrt{(9/2)\cdot174/5}<12.52$, and for $B\ge1$ the two-level mixture keeps the budget $B$ with RMS risk at most $\sqrt{(9/2)\cdot174/5}\,\omega_\mu(B^{-1/2})$. |
| `dyadic_batch` | $B/2^L<8$ for $B\ge4$ with supremum $8$, and for $B\ge1$ the dyadic batch keeps the budget $B$ with RMS risk at most $\sqrt{8\cdot174/5}\,\omega_\mu(B^{-1/2})$, about $16.69$. |
| `scale_four_bias` | For $B\ge4$, with $\lambda=B/(4\cdot2^L)$: $1\le\lambda<2$, the squared bias of the level-$L$ call is at most $\lambda\,\omega_\mu((B/4)^{-1/2})^2$, and $\omega_\mu((B/4)^{-1/2})^2\le4\,\omega_\mu(B^{-1/2})^2$. |

The bound $5.19$ is stated on the series, not on $d\,\mathbb E[C_L\mid d,S]$;
the proof gives at most $5.185$, from the certificate of the checked $26/5$.
The second-moment bound holds for every $0<d\le1/2$, more than the paper's
regime $Nd^2>1$. The remarks are stated for the specific families, since
existence forms would follow from the constant 12; "pays the factor 8 in the
worst case" is an upper bound with supremum 8, and no lower bound on any risk
is stated. The values $5.182$, $5.185$ and $1.762$ are not stated.

## How the proofs go

- [`CallCost.lean`](../../lean/ThresholdHC/UpperTwelveNumerics/CallCost.lean):
  the certificate of `UpperCallCost.callCost_constant_le`, reused for every
  partial sum, gives $5185/1000$, so the series converges below $5.19$.
- [`WrongSide.lean`](../../lean/ThresholdHC/UpperTwelveNumerics/WrongSide.lean):
  a finer bound on $e^{-2}$ and the level-sum shift of
  `UpperDisagreement.stopError_levelSum_le`.
- [`SecondMoment.lean`](../../lean/ThresholdHC/UpperTwelveNumerics/SecondMoment.lean):
  the level-sum and second-moment steps of `UpperQuarter`, kept at the
  decimal constant.
- [`Remarks.lean`](../../lean/ThresholdHC/UpperTwelveNumerics/Remarks.lean):
  the mixture through `budgetMixture_risk_of_batch` with the batch bound
  $174/5$, the dyadic batch through `modulus_sq_scale`, and the call bias
  through the cutoff bias bounds.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_upper_twelve_numerics.py --replay --jobs 2` | 9 exact statements (the 6 targets and 3 components) and 34 transitive axiom reports over the 6 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 6 modules replayed through the independent kernel checker. No `decide` is used. | [upper-twelve-numerics-audit.log](upper-twelve-numerics-audit.log) |
| `python -m unittest discover -s tools -p 'test_upper_twelve_numerics.py'` | 11 guard tests pass. | |
| `python tools/verify_project_axioms.py` | 19,855 constants (16,007 theorems) in 1,663 modules, same axioms. 155 exported instances; 6 registered orphans, unchanged. 3,702 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python tools/verify_lean_sources.py` | 1,664 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added 9
entries to `tools/definition_lock.json`: the six statements, `callOffset`,
`callCostTerm` and `wrongSideConstant`. No existing entry changed. The run
recorded here is a later one without that flag.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The specification was written before the proofs, reviewed, and
pinned by hash from this audit onward. The appendix's list of values Lean
does not check is unchanged in the paper; it changes with the next manuscript
update, and should then keep $5.182$, $5.185$ and $1.762$.

## Review

The item was planned by one agent and criticized by a second, which judged
its value low, dropped the series and certificate brackets and the offset
maximum as costly or redundant, and asked for the remarks to name the
families. A third agent wrote the proofs. Before the specification was
pinned, a fourth agent that had not written them rebuilt the modules, printed
the axioms, checked the definitions against the appendix, and confirmed the
margins in Python ($0.400583<0.401$, $6.4873<6.49$, $12.514\in(12.51,12.52)$,
certificate $5.18483<5.185$). It found no defect in the Lean; its four minor
points concerned docstrings (a misattributed paragraph, an incomplete
dependency note, a numbering mismatch and an omitted conjunct), corrected
before the pin. These were reviews by AI agents, not a specialist referee
report.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
