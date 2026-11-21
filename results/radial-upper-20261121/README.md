# The calibrated radial upper bound: library audit

Corollary `pop:radial-upper` of the population-step lower note
([`research/2026-10-27-population-step/lower/population_information.tex`](../../research/2026-10-27-population-step/lower/population_information.tex))
works on a known radial submodel of the exact quadratic law. The gap law
has density $32d$ on $(0,1/4]$. For a cutoff $b$ the radial profile is
$w_b(d)=\min(1,b^2/d^2)$, and the submodel is
$q_\eta=(1+\eta)w_b/2$ with $|\eta|\le1/2$, where $b$ is calibrated by
$\mathbb E\,w_b(D)=\rho$. With $L=1+\log(1/\rho)$ and exact calibration
integrals, an observable estimator with expected work at most $B$ has RMS
error at most $\min(\rho/4,\sqrt{160\rho L/B})$ on the submodel. It uses one
random-walk call per fresh coin that is unbiased for $\theta(q_\eta)$, with
variance at most $(11/2)\rho L$ and expected flips below $29$. The
secondary-claims guide retained this as a paper proof
([`docs/SECONDARY_CLAIMS.md`](../../docs/SECONDARY_CLAIMS.md#4-population-step-auxiliary-claims)).
Lean now checks it, in
[`lean/ThresholdHC/RadialUpper`](../../lean/ThresholdHC/RadialUpper/Full.lean).
The research package is unchanged. The audit runs below were made at commit
[`69e4ed5`](https://github.com/davidiach/adaptive-threshold-estimation/commit/69e4ed5).

## Statements

[`Specification.lean`](../../lean/ThresholdHC/RadialUpper/Specification.lean)
defines the radial profile, the index set $|\eta|\le1/2$, the sign laws
`radialSign b η`, the factor $L$, the calibration predicate
`RadialCalibrated ρ b` ($0<b<1/4$ and $\mathbb E\,w_b(D)=\rho$ under
`criticalPositiveLaw`), and the submodel minimax risk `radialMinimaxRisk`.

| Target | Statement |
|---|---|
| `radial_cutoff` | For $0<\rho\le1/4$ exactly one $b$ is calibrated, so the other statements are not vacuous. |
| `radial_call` | For every calibrated $b$ one bounded, capped observable call on a fresh coin has, for every $\eta$, expected flips below $29$, mean $\theta(q_\eta)$ and variance at most $(11/2)\rho L$, under the original one-coin tape law. |
| `radial_upper` | For every calibrated $b$ and $B>0$, some estimator has expected work at most $B$ and RMS error at most $\min(\rho/4,\sqrt{160\rho L/B})$ for every $q_\eta$. |
| `radial_minimax_upper` | The same bound for `radialMinimaxRisk b B`. |

The statements quantify over every calibrated cutoff rather than a chosen
one, and the call is chosen before $\eta$. The guarantee holds only on the
submodel, as in the source: it is not an upper bound for arbitrary sign laws.
The source's walk is uncapped; the Lean walk is capped at
$N=\lceil50/b^2\rceil$ inside the construction, and unbiasedness stays exact.
The approximate-calibration perturbation bound of the source and Proposition
`pop:radial-information` are not part of this group.

## How the proofs go

- [`Walk.lean`](../../lean/ThresholdHC/RadialUpper/Walk.lean) and
  [`Ruin.lean`](../../lean/ThresholdHC/RadialUpper/Ruin.lean): the capped walk
  as a finite sum over words, with finite-cap gambler's-ruin bounds. Under
  upward drift the hit probability is at least $1-r$ minus $\mathbb E[\text{steps}]/N$,
  and the expected steps are at most $2K$. Under downward drift the hit
  probability is at most $r^{K-1}$ and the expected steps at most $1/(2d)$.
- [`Cutoff.lean`](../../lean/ThresholdHC/RadialUpper/Cutoff.lean) and
  [`GapIntegrals.lean`](../../lean/ThresholdHC/RadialUpper/GapIntegrals.lean):
  existence and uniqueness of the calibrated cutoff, and the integrals under
  the density $32x$. The unbounded $1/(2d)$ is handled through a continuous
  bound.
- [`Call.lean`](../../lean/ThresholdHC/RadialUpper/Call.lean),
  [`Moments.lean`](../../lean/ThresholdHC/RadialUpper/Moments.lean) and
  [`Calibration.lean`](../../lean/ThresholdHC/RadialUpper/Calibration.lean):
  the call's value is affine in the hit indicator. Its mean is
  $F+(1+\eta)d_0$ with $F\le(9/8)b^2$ and $d_0\ge4b^2$. Its variance is at
  most $(11/3)\rho L$ and its expected flips at most $115/4$.
- [`Full.lean`](../../lean/ThresholdHC/RadialUpper/Full.lean): the constant
  estimator $\rho/2$, or the known-law planner with one call at rate $B/29$
  shifted by $\rho/2$, and $29((11/2)\rho L+\rho^2/16)\le160\rho L$.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_radial_upper.py --replay --jobs 2` | 7 exact statements (the 4 targets and 3 components) and 118 transitive axiom reports over the 9 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 9 modules replayed through the independent kernel checker. | [radial-upper-audit.log](radial-upper-audit.log) |
| `python -m unittest discover -s tools -p 'test_radial_upper.py'` | 11 guard tests pass. | |
| `python tools/verify_project_axioms.py` | 20,041 constants (16,162 theorems) in 1,672 modules, same axioms. 155 exported instances; 6 registered orphans, unchanged. 3,733 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python tools/verify_lean_sources.py` | 1,673 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added 31
entries to `tools/definition_lock.json`: the four statements, the definitions
above, the walk and its sums, the call and the calibration constants. No
existing entry changed. The run recorded here is a later one without that
flag.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The specification was written before the proofs, reviewed, and
pinned by hash from this audit onward. The intermediate constants differ from
the source's ($d_0\ge4b^2$ against $(8/3)b^2$; an exact integral in place of
a series bound), but the stated constants are the source's.

## Review

The item was planned by one agent and criticized by a second. The critic:
- replaced a chosen cutoff, whose junk branch would have made the statements trivially true, by quantification over every calibrated cutoff, with the existence and uniqueness statement as a companion;
- required explicit bounds on the call's cost and value;
- flagged the integrability of $1/(2d)$.

A third agent wrote the proofs. Before the specification was pinned, a fourth agent that had not written them:
- rebuilt the modules and printed the axioms;
- checked the statements and intermediate constants against the source;
- checked that the hypotheses can be met at $\rho=1/4$ and $\rho=1/1000$, and that $\theta(q_\eta)=(1+\eta)\rho/2$ separates $\eta=\pm1/2$.

It found no defect in the Lean. Its two minor points concerned docstrings, which overstated the ruin bounds and said a statement "proves" its claim, and both were corrected before the pin. These were reviews by AI agents, not a specialist referee report.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
