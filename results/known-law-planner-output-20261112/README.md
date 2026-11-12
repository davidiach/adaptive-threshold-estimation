# The planner's output, end to end

This record covers the output of the
[known-law planner](../known-law-planner-20261112/README.md) with no split
left as a hypothesis. The rate theorems for
[exact integrals](../known-law-plan-rate-20261112/README.md) and for
[upper bounds](../known-law-plan-tight-rate-20261112/README.md) are stated for
a split $\sigma+\tau+\zeta$ with hypotheses that identify it as the quantile
split cut at $h=B^{-1/2}$. Here that split is constructed for every law, and
the validity of the plan is combined with its rate.

$K_{\mu,\rho}(B)$ is the
[entropy-tail selection functional](../../lean/ThresholdHC/EntropyTail/Model.lean)
and the minimax risk is over all adaptive estimators with expected budget
$B$, under every rare prior. All statements are in
[PlannerOutput.lean](../../lean/ThresholdHC/KnownLawPlanner/PlannerOutput.lean).

| Statement | Lean-checked guarantee |
|---|---|
| Cut | Every finite measure of positive gaps is the sum of a finite part on gaps at least $h$ and a finite part on gaps at most $h$. |
| Quantile split | For every probability law $\mu$ of positive gaps and $0<\rho\le1$ there are finite $\sigma,\tau,\zeta$ with $\sigma+\tau+\zeta=\mu$, $\sigma$ the quantile core, $\tau+\zeta$ the quantile part, $\tau$ on gaps at least $h$ and $\zeta$ on gaps at most $h$. |
| Output in minimax form | For an enclosure whose envelope meets the termination requirement, a terminal level with $\bar z\le\delta_J/8$ and positive weights: the minimax risk at budget $B$ is at most $\min\{\rho/2,\sqrt{\text{certificate}}\}$. |
| From upper bounds | For the quantile split, every tight enclosure and all weights within a factor $\theta$ of the optimal ones: the planner's output, the plan when $2048\bar z\le\rho$ and the constant otherwise, gives minimax risk at most $\bigl(1+\tfrac85\max\{4096,224000\sqrt\theta\}\bigr)K_{\mu,\rho}(B)$. |
| Exact planner | For every probability law $\mu$ of positive gaps, every $0<\rho\le1/4$ and every $B>0$: the planner run on the quantile split with the exact integrals and the optimal weights gives minimax risk at most $44801\,K_{\mu,\rho}(B)$. |
| Mass at zero | For $\alpha=z_0\delta_0+(1-z_0)\eta$ with $z_0<\rho\le1$, the scaled quantile split of the [zero-atom design](../known-law-plan-tight-rate-20261112/README.md) exists, and its exact integrals with $z_0$ added to the unresolved mass are a tight enclosure. |

The last row shows that the hypotheses of the zero-atom rate can be met. It
is not a statement about an estimator: the experiment has positive gaps only.

The exact-planner row differs from the existing
[upper theorem](../../lean/ThresholdHC/EntropyTailExecution/UpperTheorem.lean),
which bounds the minimax risk by 28000 times the selection value of every
selection, with an estimator that runs each level at its least admissible cap
with the optimal counts. Here the estimator is the output of the specified
planner: the quantile split, the carried cap search, the level prices, the
terminal rule, the counts and the constant fallback. $44801=1+\tfrac85\cdot28000$.

It does not include the toolkit's planner as written, a concrete enclosure
for a finite law, a coin of gap zero, the robust continuation, the all-budget
controller or the arbitrary-law adaptation theorem, which remains a paper
proof.

At [the proof checkpoint](https://github.com/davidiach/adaptive-threshold-estimation/commit/7db45b9918589b9b40ee479871ffede26ebaf7a9),
the new module was built from source on Linux with Lean `v4.36.0-rc1`, on top
of a build of every project module made in the same environment and against
the Mathlib cache for the pinned revision. It compiled without warnings.
[9 exact statements](known_law_planner_output.lean) passed with
[9 transitive axiom reports](known_law_planner_output.log), one for each
declaration of the module, using only `propext`, `Classical.choice` and
`Quot.sound`. The exact enclosure with mass at zero is restated through its
fields. The whole-project audit
`python tools/verify_project_axioms.py --no-build` passed on the same build:
1,183 modules, 12,554 constants and 10,132 theorems, with no declared axiom. Its
kernel replay was not run locally. The [native record](status.json) lists the
source hash of every project module in the import closure of the new
module. Its base checkpoint is the head of the
[tight-rate change](../known-law-plan-tight-rate-20261112/README.md).

Run `python tools/verify_known_law_planner_output.py` with the pinned
toolchain. The audit restates every definition and theorem in full and fails
if a declaration of the module is not registered.
