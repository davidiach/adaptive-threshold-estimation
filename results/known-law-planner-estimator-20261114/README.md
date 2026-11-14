# The planner's output as a named estimator

The [planner-output record](../known-law-planner-output-20261112/README.md)
bounds the minimax risk, an infimum over all estimators. Those statements
name no estimator, and as statements they already follow from the
[upper theorem](../../lean/ThresholdHC/EntropyTail/Upper.lean), which bounds
the minimax risk by $28000\,K$ under the same hypotheses. That record's text
says its exact-planner row is a statement about the output of the planner;
this record corrects it, and leaves the earlier record unchanged as a
description of its checkpoint. Here the estimator the planner returns is
named in each statement. All statements are in
[PlannerEstimator.lean](../../lean/ThresholdHC/KnownLawPlanner/PlannerEstimator.lean).

$K_{\mu,\rho}(B)$ is the
[entropy-tail selection functional](../../lean/ThresholdHC/EntropyTail/Model.lean).
Budget $B$ means expected work at most $B$ under every sign law of rarity
$\rho$, and risk is the worst root-mean-square error over those sign laws.

| Statement | Lean-checked guarantee |
|---|---|
| Plan estimator | For a split $\sigma+\tau+\zeta$ whose core is the quantile core, an enclosure $E$ with a vanishing envelope and weights $w$, the estimator is the plan at the carried cap search of $E$, the terminal level chosen from $E$'s unresolved mass and the counts from $w$. Restated by `rfl`. |
| Decision | The planner runs the plan when $2048\bar z\le\rho$ and $\sqrt{\text{certificate}}\le\rho/2$, and returns the constant $\rho/2$ otherwise. Restated by `Iff.rfl`. |
| From a rate | If $\min\{\rho/2,\sqrt{\text{certificate}}\}\le C K$ when $2048\bar z\le\rho$, and $\rho/2\le CK$ otherwise, then in each branch the returned estimator has budget $B$ and risk at most $CK$. |
| Exact planner | On the quantile split cut at $h=B^{-1/2}$, with the exact integrals and the optimal weights $\sqrt{17\delta_l/k_l}$: in each branch the returned estimator has budget $B$ and risk at most $44801\,K_{\mu,\rho}(B)$. |
| From upper bounds | For every tight enclosure of that split and weights within a factor $\theta$ of the optimal ones: in each branch the returned estimator has budget $B$ and risk at most $\bigl(1+\tfrac85\max\{4096,224000\sqrt\theta\}\bigr)K_{\mu,\rho}(B)$. The weight bounds can hold only when $\theta\ge1$. |
| Supporting facts | The core lies above the quantile threshold, and a band edge lies below it for every law. |

The quantile split exists for every probability law of positive gaps
(`exists_quantile_split` in the planner-output record), so the hypotheses can
be met for every law. Because $\rho/(1+\sqrt B)\le K$, the constant alone is
within $CK$ once $B\le(2C-1)^2$, about $8\cdot10^9$ flips for $C=44801$; the
bounds have content beyond that budget.

The plan's estimator uses the exact bank weights of the core and the exact
null mixture of the law. The record does not cover the toolkit's planner as
written, which uses bank weights and a null test from the oracle's bounds, a
smaller level price and randomized rounding, nor a coin of gap zero, the
robust continuation or the all-budget controller.

At [the proof checkpoint](https://github.com/davidiach/adaptive-threshold-estimation/commit/b4a88c43a7ad7f4b68dfeb78f69d205102e7e359),
the new module was built from source on Linux with Lean `v4.36.0-rc1`, on top
of a build of every project module made in the same environment and against
the Mathlib cache for the pinned revision. It compiled without warnings.
[8 exact statements](known_law_planner_estimator.lean) passed with
[8 transitive axiom reports](known_law_planner_estimator.log), one for each
declaration of the module, using only `propext`, `Classical.choice` and
`Quot.sound`. The whole-project audit passed on the same build; see the
[project-definitions record](../project-definitions-20261114/README.md). The
[native record](status.json) lists the source hash of every project module in
the import closure of the new module. Its base checkpoint is `b471d6b`.

Run `python tools/verify_known_law_planner_estimator.py` with the pinned
toolchain. The audit restates every definition and theorem in full and fails
if a declaration of the module is not registered or cannot be read.
