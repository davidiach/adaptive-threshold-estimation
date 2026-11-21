# The margin-class corollaries: library audit

Section `sec:model` of the v6 manuscript
([`paper/v6/core.tex`](../../paper/v6/core.tex)) states two corollaries of
the stochastic-envelope theorems for natural classes of laws. Corollary
`cor:gap` concerns the gap class
$\mathcal G_\Delta=\{G:P_G(|P-1/2|<\Delta)=0\}$. Corollary `cor:power` concerns
the polynomial margin class
$\mathcal G_{\alpha,C}=\{G:P_G(|P-1/2|\le t)\le Ct^\alpha,\ 0<t\le1/2\}$ with
$C\ge2^\alpha$. Both give the smallest uniform expected work of an
$(\varepsilon,\delta)$-valid estimator up to constants, and `cor:power` adds an
unbiased dichotomy and a common estimator. Lean checked the envelope bounds
at a fixed reference law
([record](../stochastic-envelope-20261105/README.md)) but not their inversion
into work over these classes. Lean now checks the corollaries, except the
critical row $\alpha=1$, in
[`lean/ThresholdHC/MarginClasses`](../../lean/ThresholdHC/MarginClasses/Full.lean).
The paper is unchanged. The audit runs below were made at commit
[`4b0f856`](https://github.com/davidiach/adaptive-threshold-estimation/commit/4b0f856).

## Statements

[`Specification.lean`](../../lean/ThresholdHC/MarginClasses/Specification.lean)
defines `classWork P ε δ`, the infimum of the real budgets $B$ for which one
estimator is $(\varepsilon,\delta)$-valid (`UniformConfidence`, under every
measurable sign law) with uniform expected work at most $B$ (`UniformBudget`)
at every law in the class $P$; and the classes `GapClass Δ` and
`PowerClass α C`. All statements assume $0<\varepsilon\le1/25$ and
$0<\delta\le1/4$, in place of the source's "sufficiently small $\varepsilon$".

| Target | Statement |
|---|---|
| `gap_class` | `cor:gap`: for $0<\Delta\le1/2$, $\frac{225}{131072}\frac{\log(1/\delta)}{\varepsilon^2\Delta^2}\le$ `classWork (GapClass Δ)` $\le8192^2\frac{\log(1/\delta)}{\varepsilon^2\Delta^2}$. |
| `sublinear_class` | `cor:power`, $0<\alpha<1$: $\left(\frac{15C}{256\sqrt2}\right)^{2/\alpha}\log(1/\delta)\,\varepsilon^{-2/\alpha}\le$ `classWork` $\le\left(\frac{8192C}{1-\alpha}\right)^{2/\alpha}\log(1/\delta)\,\varepsilon^{-2/\alpha}$. |
| `superlinear_class` | `cor:power`, $\alpha>1$: $\frac{225}{32768}\frac{\log(1/\delta)}{\varepsilon^2}\le$ `classWork` $\le\left(\frac{8192\,\alpha C^{1/\alpha}}{\alpha-1}\right)^2\frac{\log(1/\delta)}{\varepsilon^2}$. |
| `power_unbiased` | For $\alpha>0$, an estimator unbiased with finite uniform variance and work on all of $\mathcal G_{\alpha,C}$ exists if and only if $\alpha>1$. |
| `common_unbiased` | One estimator, chosen before $\alpha$ and $C$, is unbiased with variance at most $23J$ and work at most $31J$ on every $\mathcal G_{\alpha,C}$ with $\alpha>1$, where $J=\alpha C^{1/\alpha}/(\alpha-1)$. |
| `common_confidence` | One budget-indexed family, chosen before $\Delta$, $\alpha$, $C$ and $\varepsilon$, attains the three upper budgets above with `UniformBudget` and `UniformConfidence`. |

$J$ bounds the inverse moment $\int d^{-1}$; it is not its exact value. The
budget fed to the common family still depends on the class parameters,
$\varepsilon$ and $\delta$, as in the source. Gap laws live on $(0,1/2]$, so
$D=0$ is excluded; both classes already put no mass there. Not stated: the
critical row $\alpha=1$ ($\varepsilon^{-2}\log^2(1/\varepsilon)$), the proof's
remark that the universal estimator is integrable and unbiased for
$\alpha\le1$, the logarithmic classes of `cor:log` and the rate table.

## How the proofs go

- [`Basic.lean`](../../lean/ThresholdHC/MarginClasses/Basic.lean): every
  valid estimator at accuracy $\varepsilon\le1/25$ has budget at least one,
  because $1/25<15/(256\sqrt2)$; reference laws in each class; the modulus of a
  point mass; and the common rule.
- [`Gap.lean`](../../lean/ThresholdHC/MarginClasses/Gap.lean): the lower
  bound evaluates a valid witness at $\delta_\Delta$ with
  `OracleLower.hidden_confidence_lower`; the upper bound runs the common
  family at confidence scale $\varepsilon\Delta/8192$.
- [`Power.lean`](../../lean/ThresholdHC/MarginClasses/Power.lean): for
  $\alpha<1$ the exact reference power law and `SubcriticalPower.sublinear_modulus`;
  for $\alpha>1$ the point mass at $1/2$ below and the inverse-moment bound above.
- [`Unbiased.lean`](../../lean/ThresholdHC/MarginClasses/Unbiased.lean): the
  713 estimator for $\alpha>1$, and for $\alpha\le1$ the linear law in the
  class, whose inverse moment diverges, with `unbiased_converse`.
- [`Full.lean`](../../lean/ThresholdHC/MarginClasses/Full.lean): the three
  upper halves of `classWork` follow from `common_confidence` by `sInf_le`.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_margin_classes.py --replay --jobs 2` | 9 exact statements (the 6 targets and 3 components) and 50 transitive axiom reports over the 6 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 6 modules replayed through the independent kernel checker. | [margin-classes-audit.log](margin-classes-audit.log) |
| `python -m unittest discover -s tools -p 'test_margin_classes.py'` | 11 guard tests pass. | |
| `python tools/verify_project_axioms.py` | 20,427 constants (16,509 theorems) in 1,702 modules, same axioms. 155 exported instances; 6 registered orphans, unchanged. 3,772 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python tools/verify_lean_sources.py` | 1,703 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added 9
entries to `tools/definition_lock.json`: the six statements, `classWork`,
`GapClass` and `PowerClass`. No existing entry changed. The run recorded here
is a later one without that flag.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The specification was written before the proofs, reviewed, and
pinned by hash from this audit onward.

## Review

The item was planned by one agent and criticized by a second, which asked
for the public confidence lower bound to be reused rather than copied, for
the point mass at $1/2$ as the lower-bound law for $\alpha>1$, for the common
budget-indexed family as its own statement, and for the partial coverage of
`cor:power` to be reported. A third agent wrote the proofs. Before the
specification was pinned, a fourth agent that had not written them:
- rebuilt the modules and printed the axioms;
- checked the classes against the source and re-derived the constants;
- checked that each class contains a probability law and that each lower bound is paired with a finite upper bound, so no infimum is that of an empty set.

It found no defect in the Lean. Its two minor points concerned helper
docstrings that left out the accuracy cutoff and stated an equality where the
lemma proves an inequality; both were corrected. These were reviews by AI
agents, not a specialist referee report.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
