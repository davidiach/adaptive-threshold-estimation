# The clipping boundary: library audit

The audit note
[`CLIPPING_BOUNDARY.tex`](../../research/2026-10-27-nonlinear-population/audit/CLIPPING_BOUNDARY.tex)
of the nonlinear-population package asks when clipping an estimator to the
known interval $[0,\rho]$ keeps a variance lower bound. It proves two
propositions. Under bounded kurtosis the variance transfers: if $F$ is
unbiased for $\theta\in[0,\rho]$ with variance $\sigma^2$ and
$\mathbb E(F-\theta)^4\le K\sigma^4$, $1\le K$, then
$\mathbb E(\Pi_\rho(F)-\theta)^2\ge\min\{\sigma^2,\rho^2\}/(256K^2)$. Without
such a premise it does not: independent seed noise leaves $F$ unbiased, adds
$\varepsilon M^2$ to its variance and at most $\varepsilon\rho^2$ to the risk.
The [secondary-claims list](../../docs/SECONDARY_CLAIMS.md) kept this as a
conditional paper result. Lean now checks both propositions, in
[`lean/ThresholdHC/ClippingBoundary`](../../lean/ThresholdHC/ClippingBoundary/Full.lean).
The research package is unchanged. The audit runs below were made at commit
[`ce1c237`](https://github.com/davidiach/adaptive-threshold-estimation/commit/ce1c237).

## Statements

[`Specification.lean`](../../lean/ThresholdHC/ClippingBoundary/Specification.lean)
writes $\Pi_\rho(x)=\min\{\rho,\max\{0,x\}\}$ as the existing `clipEstimate`,
which agrees with it for $\rho\ge0$, defines the seed noise (`seedNoise`: $0$
with probability $1-\varepsilon$, $\pm M$ with probability $\varepsilon/2$ each)
and states five targets.

| Target | Statement |
|---|---|
| `kurtosis_transfer` | For $F\in L^4(P)$ with mean $\theta$, $0\le\theta\le\rho$, $1\le K$ and $\int(F-\theta)^4\,dP\le K\,\mathrm{Var}(F)^2$: the clipped squared risk is at least $\min\{\mathrm{Var}(F),\rho^2\}/(256K^2)$. |
| `kurtosis_rms` | The same premises give clipped RMS at least $\min\{\rho,\sqrt{\mathrm{Var}(F)}\}/(16K)$, the form of the secondary-claims list. |
| `uniform_clipped_floor` | If the premises hold for the output of an estimator under every rare sign law with one $K$, the clipped estimator's rare RMS risk is at least $(16K)^{-1}\min\{\rho,(\sup_q\mathrm{Var}_q)^{1/2}\}$, the supremum in $[0,\infty]$ over extended variances. |
| `noise_counterexample` | For $F_0\in L^2(P)$ with mean $\theta\in[0,\rho]$ and $0\le\varepsilon\le1$: with independent seed noise $Z$, $F_0+Z$ has mean $\theta$ and variance $\mathrm{Var}(F_0)+\varepsilon M^2$, and its clipped squared risk is at most the raw squared risk of $F_0$ plus $\varepsilon\rho^2$. |
| `noisy_estimator` | The same in the original adaptive experiment: the estimator with the noise as an extra seed coordinate has the same policy and expected work, the same mean when the output is integrable, variance increased by $\varepsilon M^2$ when it is square-integrable, and the risk bound; uniform unbiasedness and uniform budgets transfer, and a uniform variance bound $V\ge0$ becomes $V+\varepsilon M^2$. |

The finite-variance and fourth-moment premises are $F\in L^4$ with a Bochner
fourth-moment bound; the paper's premise already forces a finite fourth
moment, and without the integrability hypotheses Lean's value $0$ for the
integral of a non-integrable function would make the premises vacuous. In the
uniform corollary "every $q$" is read as every rare sign law, which places the
target $\theta=\int q\,d\mu$ in $[0,\rho]$; $\rho\ge1$ recovers the whole sign
class. The note's remark that the noise "respects the inherited additive
class" is read as the transfer of the three uniform properties used by the
unbiased converse; membership in the structural additive class of the note's
construction is not defined in Lean.

## How the proofs go

- [`Pointwise.lean`](../../lean/ThresholdHC/ClippingBoundary/Pointwise.lean)
  and [`Kurtosis.lean`](../../lean/ThresholdHC/ClippingBoundary/Kurtosis.lean):
  instead of Hölder's inequality and the Paley–Zygmund inequality, the proof
  integrates pointwise polynomial inequalities. Young's quartic inequality,
  from $y(y-s)^2(y+2s)\ge0$, gives $v\le K(\mathbb E|X|)^2$; a truncated-mean
  inequality and a tangent line then give $\min\{v/(16K),\rho^2/(64K^2)\}$,
  which implies the stated constants.
- [`Uniform.lean`](../../lean/ThresholdHC/ClippingBoundary/Uniform.lean) moves
  the constant, the minimum and the square root inside the supremum and
  applies the bound at each rare sign law.
- [`Noise.lean`](../../lean/ThresholdHC/ClippingBoundary/Noise.lean) proves
  the noise facts as separate lemmas, each with only the hypotheses it needs:
  on the atom $0$ the clipped error is at most the raw error, and on $\pm M$
  both the clipped estimate and $\theta$ lie in $[0,\rho]$.
- [`NoisyEstimator.lean`](../../lean/ThresholdHC/ClippingBoundary/NoisyEstimator.lean)
  builds the noisy estimator and transports those lemmas through a Fubini
  identity for the experiment's law.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_clipping_boundary.py --replay --jobs 3` | 8 exact statements (the 5 targets and 3 components) and 55 transitive axiom reports over the 7 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 7 modules replayed through the independent kernel checker. | [clipping-boundary-audit.log](clipping-boundary-audit.log) |
| `python -m unittest discover -s tools -p 'test_clipping_boundary.py'` | 11 guard tests pass. | |
| `python tools/verify_project_axioms.py` | 17,759 constants (14,295 theorems) in 1,521 modules, same axioms. 148 exported instances, one of them the group's named, global, Prop-valued `seedNoise_isFiniteMeasure`; 6 registered orphans, unchanged. 3,324 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python tools/verify_lean_sources.py` | 1,522 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added ten
entries to `tools/definition_lock.json`: `seedNoise`, the five statements and
the four definitions of the noisy estimator. No existing entry changed. The
run recorded here is a later one without that flag.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The specification was written after the proofs; it is pinned by
hash from this audit onward. Three passages of the note are not targets: the
remark that the variance–work lower bound survives clipping, the divergence
remark at $M=1/\varepsilon$ and the tail-energy transfer. The note's
observation that no uniform kurtosis bound is supplied for the telescope
estimator is unchanged.

## Review

The group was planned by one agent and criticized by a second, which required
the noise step to go through separate lemmas and added the additive-class
clauses; a third wrote it. Before the specification was pinned, a fourth
agent that had not written the proofs rebuilt the modules, printed the axioms
of all 55 public declarations, restated the targets and ran the audit's
scans. It checked non-vacuity in Lean with a fair-coin witness ($F\in\{0,1\}$,
$\theta=1/2$, $\rho=1$, $K=1$), and argued on paper that the uniform premise can
hold with positive variance. It found four docstring points: the risk
comparison is clipped against raw risk, the additive-class clauses stand in
for the note's class rather than define it, one docstring said real where the
statement is extended-real, and the range of $\varepsilon$ was missing. All
four were reworded before this audit. These were reviews by AI agents, not a
specialist referee report.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
