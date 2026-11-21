# The Poisson case of the RMS affine comparison lemma: library audit

Lemma `lem:comparison` of the full critical note
([`affine_comparison.tex`](../../research/2026-10-27-nonlinear-critical/affine_comparison.tex),
section An RMS comparison for finite convex experiments) compares an arbitrary
estimator with the best additive one in a finite convex experiment, with the
constant $12$, in two cases: categorical observations and independent Poisson
counts. The note's checkpoint records that it has no Lean verification. The
categorical case is Lean-checked with the constant $6$ and the note's $12$
([record](../affine-comparison-20261121/README.md)); the Poisson case was not.
Lean now checks it, in
[`lean/ThresholdHC/PoissonComparison`](../../lean/ThresholdHC/PoissonComparison/Full.lean).
The formal critical route does not use the lemma in either case. The note is
unchanged. The audit runs below were made at commit
[`580a79c`](https://github.com/davidiach/adaptive-threshold-estimation/commit/580a79c).

## Statements

[`Specification.lean`](../../lean/ThresholdHC/PoissonComparison/Specification.lean)
defines `poissonVectorLaw w`, the product of Mathlib's Poisson laws with
intensities $w_j$ (entered through `Real.toNNReal`, which is exact for
nonnegative intensities), and `PoissonComparisonStatement C`: let $X$ be a
nonempty compact convex subset of a finite-dimensional real normed space,
$\ell$ an affine functional, and $v$ an affine map to intensity vectors indexed
by a finite type, strictly positive on $X$. If an estimator $G$ has squared
risk at most $r^2$ at every $x\in X$, then for every $\eta>0$ some additive
estimator $c+\sum_j\beta_jz_j$ has squared risk at most $(Cr+\eta)^2$ at every
$x\in X$.

| Target | Statement |
|---|---|
| `poisson_comparison_6` | `PoissonComparisonStatement 6`. |
| `poisson_comparison_12` | `PoissonComparisonStatement 12`, the note's constant, as a corollary. |

The five components pin the law and the bound:

| Component | Statement |
|---|---|
| `poissonVectorLaw_isProbabilityMeasure` | The law is a probability measure (a global, Prop-valued instance). |
| `poissonVectorLaw_exp_integral` | For $w\ge0$: $\int e^{b+\sum_j\beta_jz_j}\,dP_w=e^{b+\sum_jw_j(e^{\beta_j}-1)}$. |
| `poissonVectorLaw_exp_integrable` | That exponential is integrable, for every $w$. |
| `poissonVectorLaw_affinity` | For $w,w'>0$ the Hellinger affinity is $e^{-\sum_j(\sqrt{w_j}-\sqrt{w'_j})^2/2}$. |
| `poisson_comparison_not_half` | The statement fails for $C=1/2$. |

The constant $6$ comes from the Lean route of the categorical group, not from
the note: the note's total-variation testing step is replaced by the direct
affinity testing bound, and its tail integral by an exponential-moment bound.
The deviations from the note are generalisations: an arbitrary bound $r\ge0$
replaces the supremum of the RMS risks, $\ell$ is affine rather than linear,
the index set is any finite type, and $G$ is arbitrary (every function on the
countable count space is measurable). The witness of the $C=1/2$ statement has
no Poisson count; the components are what show that the law is genuine.

## How the proofs go

- [`Law.lean`](../../lean/ThresholdHC/PoissonComparison/Law.lean): singleton
  masses of the product law, and the exponential moments by a product of
  Poisson moment series.
- [`LogMoment.lean`](../../lean/ThresholdHC/PoissonComparison/LogMoment.lean):
  the log-moment $\Lambda_x(\beta)=\sum_jv_j(x)(e^{\beta_j}-1)$ is affine in
  $x$ and convex in $\beta$, the inputs of the categorical group's saddle-point
  certificate.
- [`Affinity.lean`](../../lean/ThresholdHC/PoissonComparison/Affinity.lean):
  $P_{w'}$ is $P_w$ with the density $e^{2L}$ for an affine $L$, so the
  affinity is an exponential moment. This route replaces the plan's
  marginalization step, which the critic had found incomplete.
- [`Full.lean`](../../lean/ThresholdHC/PoissonComparison/Full.lean): the
  categorical group's abstract additive certificate, its exponential risk
  bound and its affinity testing bound, reused by import.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_poisson_comparison.py --replay --jobs 2` | 7 exact statements (the 2 targets and 5 components) and 26 transitive axiom reports over the 5 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 5 modules replayed through the independent kernel checker. | [poisson-comparison-audit.log](poisson-comparison-audit.log) |
| `python -m unittest discover -s tools -p 'test_poisson_comparison.py'` | 11 guard tests pass. | |
| `python tools/verify_project_axioms.py` | 21,990 constants (17,805 theorems) in 1,785 modules, same axioms. 164 exported instances, the new one the global, Prop-valued probability instance of the Poisson vector law; 6 registered orphans, unchanged. 4,023 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python tools/verify_lean_sources.py` | 1,786 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added 4
entries to `tools/definition_lock.json`: the statement, the law, the
log-moment and the half log-ratio of the affinity step. No existing entry
changed. The run recorded here is a later one without that flag.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The specification was written before the proofs, reviewed, and
pinned by hash from this audit onward.

## Review

The item was planned by one agent and criticized by a second, which found the
statement faithful, found a gap in the planned marginalization step of the
affinity, required the probability instance and the integrability lemma as
pinned components and the CI routing entry, and judged the value low because
the formal route does not need the Poisson case. A third agent wrote the
proofs. Before the specification was pinned, a fourth agent that had not
written them:
- rebuilt the modules, replayed them through the kernel checker and printed the axioms of all 26 public declarations;
- restated both targets, with the product law unfolded, and the components;
- instantiated the main theorem with a real Poisson law and probed the law: the moment $e^3$ at $\beta=\log2$, $w=3$, and the affinity $e^{-1/2}$ between $\mathrm{Po}(1)$ and $\mathrm{Po}(4)$.

It found no defect in the Lean. Its minor points concerned module docstrings
that omitted the nonnegative-intensity condition of the moment formula and
called a value an infimum without proving minimality (both corrected; these
modules are not pinned), the location of the implementer's report, and two
inaccurate packaging notes. These were reviews by AI agents, not a specialist
referee report.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
