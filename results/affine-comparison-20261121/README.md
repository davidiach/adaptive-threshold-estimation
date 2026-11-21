# The categorical affine comparison lemma: library audit

Lemma `lem:comparison` of the full critical note
([`research/2026-10-27-nonlinear-critical/affine_comparison.tex`](../../research/2026-10-27-nonlinear-critical/affine_comparison.tex),
section `An RMS comparison for finite convex experiments`) is an RMS
comparison for finite convex experiments. In its first case, $k$ independent
finite categorical observations have probability vectors $p_i(x)$ affine in a
parameter $x$ that ranges over a nonempty compact convex set $X$, and the
target $\ell(x)$ is affine. If some estimator $G$ has RMS risk at most $r_G$
at every $x\in X$, then for every $\eta>0$ an additive estimator
$c+\sum_i\phi_i(z_i)$ has RMS risk at most $12r_G+\eta$ at every $x\in X$.
The note's
[checkpoint](../../research/2026-10-27-nonlinear-critical/CHECKPOINT.md)
records that the note has no Lean verification. The critical minimax theorem
in the audited library does not use the lemma: it goes through the
repeated-observation special case `finite_convex_rms_comparison`.

Lean now checks the categorical case, in
[`lean/ThresholdHC/AffineComparison`](../../lean/ThresholdHC/AffineComparison/Full.lean),
with the constant $6$ and the source's $12$ as a corollary. The research
package is unchanged. The audit runs below were made at commit
[`ae9a210`](https://github.com/davidiach/adaptive-threshold-estimation/commit/ae9a210).

## Statements

[`Specification.lean`](../../lean/ThresholdHC/AffineComparison/Specification.lean)
defines the categorical law `categoricalLaw q` (a finite sum of Dirac masses),
the product law `categoricalProductLaw` of independent coordinates, and
`CategoricalComparisonStatement C`: for every finite-dimensional real normed
space, nonempty compact convex $X$, affine $p_i$ strictly positive with unit
sums on $X$, affine $\ell$, estimator $G$ and $r\ge0$ with squared risk at most
$r^2$ at every $x\in X$, and every $\eta>0$, some $c$ and $\phi_i$ give squared
risk at most $(Cr+\eta)^2$ at every $x\in X$. Risks are `Tier6.squaredRisk`,
lower integrals in $[0,\infty]$, so nothing is assumed about the
integrability of $G$.

| Target | Statement |
|---|---|
| `categorical_comparison_6` | `CategoricalComparisonStatement 6`, a sharpening that comes only from the Lean route and is not a claim of the source. |
| `categorical_comparison_12` | `CategoricalComparisonStatement 12`, the source's constant, as a corollary. |

The improvement from $12$ to $6$ comes from the testing step: the source's
total-variation threshold test (its display (4), factor
$\sqrt{2/(1-\sqrt3/2)}$) is replaced by the direct affinity bound $S\le2r$.
The tail step uses the exponential-moment bound with the factor $3$, slightly
coarser than the source's display (5), about $2.84$. The affine maps are
defined on all of $E$, and positivity and normalization are assumed only on
$X$. The Poisson case of the lemma, and the minimax equality (3) of its
proof, are not stated; only the direction the proof needs is proved.

## How the proofs go

- [`Saddle.lean`](../../lean/ThresholdHC/AffineComparison/Saddle.lean): a
  uniform saddle point and its centering for an abstract log-moment
  $\Lambda(x,u)$ over a real normed score space, through Sion's theorem and
  perspective convexity, re-proved because the existing finite saddle lemmas
  fix the repeated-observation form.
- [`Categorical.lean`](../../lean/ThresholdHC/AffineComparison/Categorical.lean):
  the categorical log-moment $\sum_i\log\sum_ap_i(x)_ae^{u_{ia}}$, its
  continuity, concavity in $x$, convexity in $u$ and attainment, and the
  product affinity as a product of coordinate affinities.
- [`Testing.lean`](../../lean/ThresholdHC/AffineComparison/Testing.lean): an
  estimator with squared risk at most $r^2$ under two laws of affinity at
  least $1/2$ has targets with $a-b\le4r$.
- [`Moments.lean`](../../lean/ThresholdHC/AffineComparison/Moments.lean): the
  squared-risk bound from two-sided exponential moments.
- [`Full.lean`](../../lean/ThresholdHC/AffineComparison/Full.lean): the
  certificate below $2R$ for $R=2r+\eta/3$ and the bound $(6r+\eta)^2$.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_affine_comparison.py --replay --jobs 2` | 5 exact statements (the 2 targets and 3 components) and 36 transitive axiom reports over the 6 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 6 modules replayed through the independent kernel checker. | [affine-comparison-audit.log](affine-comparison-audit.log) |
| `python -m unittest discover -s tools -p 'test_affine_comparison.py'` | 11 guard tests pass. | |
| `python tools/verify_project_axioms.py` | 19,375 constants (15,621 theorems) in 1,638 modules, same axioms. 153 exported instances (the two new ones above); 6 registered orphans, unchanged. 3,608 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python tools/verify_lean_sources.py` | 1,639 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added 5
entries to `tools/definition_lock.json`: the statement, the two laws, the
categorical log-moment and the saddle objective `pairObjective`. No existing
entry changed. The group adds two exported instances,
`categoricalLaw_isFiniteMeasure` and `categoricalProductLaw_isFiniteMeasure`,
both named, global and Prop-valued. The run recorded here is a later one
without that flag.

The audit tool was generated from the shared template and extended by one
map, `TARGET_ARGS`, because both targets restate the same parametrized
statement at different constants.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The specification was written before the proofs, reviewed, and
pinned by hash from this audit onward. The record must not be read as
attributing the constant $6$ to the source, which proves $12$.

## Review

The item was planned by one agent and criticized by a second, which split off
the Poisson case, pointed to the product-affinity and Hellinger lemmas the
proof could reuse, and required the constant $6$ to be attributed to the Lean
route only. A third agent wrote the proofs. Before the specification was
pinned, a fourth agent that had not written them rebuilt the modules, printed
the axioms, checked the statement against the note, and proved that
`CategoricalComparisonStatement (1/2)` is false (with $k=0$, $X=[0,1]$,
$\ell=\mathrm{id}$ and the constant estimator $1/2$), so the target is not
trivially true. It found no defect in the Lean; its two minor points concerned
docstrings (the moment step's factor compared with the source's, and a
one-sided bound described as two-sided), which were corrected before the pin.
These were reviews by AI agents, not a specialist referee report.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
