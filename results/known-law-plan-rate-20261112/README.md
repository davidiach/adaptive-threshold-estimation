# The rate of the exact known-law plan

This record covers the rate of the
[known-law plan](../known-law-planner-20261112/README.md) when it is computed
from the exact design integrals of the quantile split: the comparison of its
certified risk with the selection functional, the terminal rule, and the
reported radius.

Fix a probability law $\mu$ of positive gaps, a rarity $0<\rho\le1/4$ and a
budget $B>0$, with $h=B^{-1/2}$. The plan uses the quantile split of $\mu$:
the core $\sigma$ is the quantile core at rarity $\rho$, and the quantile part
is cut at $h$ into the resolved tail $\tau$, on gaps at least $h$, and the
unresolved part $\zeta$, on gaps at most $h$, of mass $z$. $\Gamma$ is the
cost entropy of the band costs of $\sigma$, $H=\int d^{-1}\,d\tau$,
$\delta_\ell=\rho\,16^{-(\ell+1)}$, and $K=K_{\mu,\rho}(B)$ is the
[entropy-tail selection functional](../../lean/ThresholdHC/EntropyTail/Model.lean).
The plan takes the exact resolved error as its envelope and the exact
integrals in its prices. Its weights lie within a factor $\theta$ of the
optimal ones: $\sqrt{v_\ell/k_\ell}\le w_\ell\le\theta\sqrt{v_\ell/k_\ell}$.

| Statement | Lean-checked guarantee |
|---|---|
| [Caps](../../lean/ThresholdHC/KnownLawPlanner/PlanRate.lean) | With the exact resolved error as envelope, the carried cap search returns the least admissible cap of each level, and the price of each level is at most the level work certificate of the upper theorem. |
| [Multilevel sum](../../lean/ThresholdHC/KnownLawPlanner/PlanRate.lean) | For a terminal level $J$ with $z\le\delta_J/8$: $\sum_{\ell\le J}\sqrt{17\delta_\ell k_\ell}\le28000\,(\sqrt{\rho\Gamma}+H)$. |
| [Terminal rule](../../lean/ThresholdHC/KnownLawPlanner/PlanRate.lean) | The planner stops at the first level $J$ with $\delta_J/16<\max\{128z,\rho/(16(1+\sqrt B))\}$. That level exists. When $2048z\le\rho$ it has $z\le\delta_J/128$, and for $z\ge0$, $\delta_J<2048z+\rho/(1+\sqrt B)$. |
| [Certified risk](../../lean/ThresholdHC/KnownLawPlanner/PlanRate.lean) | For $z\le\delta_J/8$, the square root of the certificate is at most $\delta_J+\sqrt\theta\cdot28000\,(\sqrt{\rho\Gamma}+H)/\sqrt B$. |
| [Floor](../../lean/ThresholdHC/KnownLawPlanner/PlanQuantileRate.lean) | For $0<\rho\le1$ and $B>0$: $\rho/(1+\sqrt B)\le K_{\mu,\rho}(B)$. |
| [Rate](../../lean/ThresholdHC/KnownLawPlanner/PlanQuantileRate.lean) | When $2048z\le\rho$, with the terminal level of the rule: $\min\{\rho/2,\sqrt{\text{certificate}}\}\le\bigl(1+\tfrac85\max\{2048,28000\sqrt\theta\}\bigr)K$. |
| [Fallback](../../lean/ThresholdHC/KnownLawPlanner/PlanQuantileRate.lean) | When $2048z>\rho$ the planner returns the constant $\rho/2$, and $\rho/2$ obeys the same bound. |
| [Radius](../../lean/ThresholdHC/KnownLawPlanner/PlanQuantileRate.lean) | When $2048z\le\rho$, let $r\le\kappa\sqrt{8\min\{\rho^2/4,\text{certificate}\}}$ with $\kappa\sqrt8\le6$. Then $r\le6\bigl(1+\tfrac85\max\{2048,28000\sqrt\theta\}\bigr)K$. |

For dyadic upper square roots, $\theta=2$, the rate coefficient is below
63,358 and the radius coefficient below 380,148. The rate combines the
[certificate of a plan](../known-law-planner-20261112/README.md), the
multilevel sum bound of the checked upper theorem, the floor and the checked
comparison $Q\le(8/5)K$ of the closed quantile value: the certified risk is at
most $K+\max\{2048,28000\sqrt\theta\}\,(z+hH+h\sqrt{\rho\Gamma_\sigma})$, and
the last factor is the uncapped quantile value. The radius statement holds for
every relative upper square root, so it does not degrade for small radii; a
fixed absolute rounding error would not give it.

The coefficients differ from $C_0=1+4\max\{4096,8\sqrt2C_{\rm sum}\}$ and
$C_*=6C_0$ of the [adaptation proof](../../docs/ARBITRARY_LAW_ADAPTATION.md#4-robust-use-of-the-known-law-estimator).
Those are for a planner that works from upper bounds within a factor two of
the integrals and for a reference law with mass at zero. This record is for
exact integrals and a law of positive gaps.

It does not include:

- The rate of a plan computed from upper bounds, and the coefficients $C_0$
  and $C_*$ of the adaptation proof.
- A reference law with mass at zero run through the plan.
- The toolkit's planner as written, which uses a smaller level price.
- The robust continuation, the all-budget controller and the arbitrary-law
  adaptation theorem, which remains a paper proof.

At [the proof checkpoint](https://github.com/davidiach/adaptive-threshold-estimation/commit/fdf0addef318919f8258db8dda67afc617313173),
the two new modules were built from source on Linux with Lean `v4.36.0-rc1`,
on top of a build of every project module made in the same environment and
against the Mathlib cache for the pinned revision. They compiled without
warnings. [18 exact statements](known_law_plan_rate.lean) passed with
[18 transitive axiom reports](known_law_plan_rate.log), one for each
declaration of the two modules, using only `propext`, `Classical.choice` and
`Quot.sound`. The whole-project audit
`python tools/verify_project_axioms.py --no-build` passed on the same build:
1,179 modules, 12,501 constants and 10,082 theorems, with no declared axiom. Its
kernel replay was not run locally. The [native record](status.json) lists the
source hash of every project module in the import closure of the new
modules. Its base checkpoint is the head of the plan-certificate change.

One check outside Lean was run during review and is supporting evidence only.
A floating-point transcription of the plan as defined in Lean was run on 3,000
random finite laws, with the selection functional from the
[toolkit's exhaustive enclosure](../../toolkit/threshold_toolkit/rare_event_functional.py).
On the 2,742 plans and 258 fallbacks every bound above held. The largest
certified risk was 20.2 times $K$, and the largest multilevel sum was 0.0006
of its bound: the coefficients are far from tight.

Run `python tools/verify_known_law_plan_rate.py` with the pinned toolchain.
The audit restates every definition and theorem in full and fails if a
declaration of the two modules is not registered.
