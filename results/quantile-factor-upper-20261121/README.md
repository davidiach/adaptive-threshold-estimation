# The upper end of the sharp quantile factor: library audit

Theorem `thm:sharp-quantile-factor` of the v6 paper
([`paper/v6/appendix-optimal-factor.tex`](../../paper/v6/appendix-optimal-factor.tex);
also [`docs/OPTIMAL_QUANTILE_FACTOR.md`](../../docs/OPTIMAL_QUANTILE_FACTOR.md))
states that exactly one $k\in[\sqrt2,31/20]$ satisfies
$\max_{1\le u\le31/20}F(k,u)=1$, that it is the sharp comparison factor $c_*$
for general and for finite laws, and that

$$1.462554551279<c_*<1.462554551280.$$

The scalar characterization, the all-law comparison, finite-law sharpness
([record](../quantile-optimality-20261105/README.md)) and the lower end
([record](../paper-statements-20261120/README.md)) were Lean-checked. The
upper end rested on the exact-arithmetic verifier
`tools/verify_optimal_quantile_factor.py` alone. Lean now checks it and
states the whole theorem, in
[`lean/ThresholdHC/QuantileFactorUpper`](../../lean/ThresholdHC/QuantileFactorUpper/Full.lean).
The `OptimalQuantile`, `QuantileOptimality` and `PaperStatements` groups and
the paper are unchanged. The audit runs below were made at commit
[`174f503`](https://github.com/davidiach/adaptive-threshold-estimation/commit/174f503).

## Statements

[`Specification.lean`](../../lean/ThresholdHC/QuantileFactorUpper/Specification.lean)
states four targets against the existing `partitionSeries` ($F$),
`scalarPeak` (its maximum over $[1,31/20]$), `scalarRoot`, `UniversalFactor`
and `FiniteUniversalFactor`.

| Target | Statement |
|---|---|
| `peak_upper` | `scalarPeak` at $k=1.462554551280$ is below one. |
| `root_upper` | $c_*<1.462554551280$. |
| `root_bracket` | $1.462554551279<c_*<1.462554551280$. |
| `sharp_quantile_factor` | The theorem in full: some $c\in[\sqrt2,31/20]$ has $\max_uF(c,u)=1$ attained, it is the only such $k$ in $[\sqrt2,31/20]$, $k$ is a comparison factor for general laws, and for finite laws, exactly when $c\le k$, and $c$ lies strictly inside the bracket. |

As in `QuantileOptimality`, $c_*$ is the least $k$ with $Q\le k\mathcal K$ for
$0<\rho\le1/4$ and $B>0$, over all positive-gap laws and over finite laws.
The statements have no hypotheses, and `peak_upper` goes through the attained
maximum rather than a conventional supremum value.

## How the proofs go

- [`Truncation.lean`](../../lean/ThresholdHC/QuantileFactorUpper/Truncation.lean):
  $F$ is its first five terms (weights $1,2,4,8,16$) plus a tail at most
  $2^{-62}$, since the price is at least two.
- [`Convexity.lean`](../../lean/ThresholdHC/QuantileFactorUpper/Convexity.lean):
  the five-term sum plus $25u^2/2$ is convex on $[1,31/20]$ for
  $\sqrt2\le k\le31/20$, by explicit second derivatives, so on each cell
  $[l,r]$ the sum is at most its larger endpoint value plus $25(r-l)^2/8$.
  The paper proves $F_{uu}\ge-25$ for the whole series; here the bound is
  proved for the five terms and the tail is handled by the uniform $2^{-62}$.
- [`Checker.lean`](../../lean/ThresholdHC/QuantileFactorUpper/Checker.lean)
  and [`ExpEnclosure.lean`](../../lean/ThresholdHC/QuantileFactorUpper/ExpEnclosure.lean):
  a natural-number checker at scale $2^{100}$ bounds each $e^{-x}$ from
  above, as the rounded-up reciprocal of a rounded-down 22-term Taylor sum
  of $e^{x/2^s}$ followed by $s$ upward-rounded squarings, and is proved
  sound.
- [`Cover.lean`](../../lean/ThresholdHC/QuantileFactorUpper/Cover.lean) and
  [`Certificate.lean`](../../lean/ThresholdHC/QuantileFactorUpper/Certificate.lean):
  a self-bisecting checker on the grid $u=a/(20\cdot2^{24})$ is proved sound
  and is evaluated by `decide +kernel` in four quarters. Its tree has 85
  accepted cells of depth at most 21, as in the paper and the Python
  verifier. No native code is used.
- [`Full.lean`](../../lean/ThresholdHC/QuantileFactorUpper/Full.lean)
  combines the cover with the checked lower end, uniqueness and the
  least-factor equivalences.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_quantile_factor_upper.py --replay --jobs 3` | 7 exact statements (the 4 targets and 3 components) and 82 transitive axiom reports over the 8 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 8 modules replayed through the independent kernel checker, which re-evaluates the four certificate quarters. | [quantile-factor-upper-audit.log](quantile-factor-upper-audit.log) |
| `python -m unittest discover -s tools -p 'test_quantile_factor_upper.py'` | 11 guard tests pass. | |
| `python tools/verify_project_axioms.py` | 18,905 constants (15,229 theorems) in 1,588 modules, same axioms. 151 exported instances; 6 registered orphans, unchanged. 3,533 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python tools/verify_lean_sources.py` | 1,589 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added 44
entries to `tools/definition_lock.json`: the four statements, the checker,
its exponential enclosure and grid, and the exponent and convexity helpers.
No existing entry changed. The run recorded here is a later one without that
flag.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The specification was written after the proofs; it is pinned by
hash from this audit onward. Each certificate quarter checks in about
1.4 seconds of kernel time; the certificate module peaks at about 1.6 GB, and
the specification and assembly modules at about 6.7 GB of mapped library
files. The Python verifier is unchanged and remains an independent
exact-arithmetic check.

## Review

The item was planned by one agent, criticized by a second, which corrected
the soundness statement of the cell test and the chord bound for a
degenerate cell, and written by a third under a memory budget for the kernel
certificate. Before the specification was pinned, a fourth agent that had
not written the proofs rebuilt the modules, restated each target by
`Iff.rfl`, printed the axioms, ran the audit's scans, replicated the checker
in Python (85 cells, depth 21, minimum slack about $7.5\cdot10^{-14}$),
profiled the four kernel checks, and probed non-vacuity: the cover fails at
fuel zero, and the least-factor equivalences pin $c$ down because universal
factors fail below the root. It found no defect in the Lean; its two minor
points concerned the implementer's notes. These were reviews by AI agents,
not a specialist referee report.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
