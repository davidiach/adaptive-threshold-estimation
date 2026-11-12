# The rate of a known-law plan computed from upper bounds

This record covers the rate of the
[known-law plan](../known-law-planner-20261112/README.md) when the planner
has upper bounds of the design integrals in place of
[the exact integrals](../known-law-plan-rate-20261112/README.md), and when
its reference law has mass at zero. It gives the planned coefficient $C_0$
and the radius coefficient $C_*=6C_0$ of the
[adaptation proof](../../docs/ARBITRARY_LAW_ADAPTATION.md#4-robust-use-of-the-known-law-estimator),
at the multilevel coefficient 28000 of the checked upper theorem.

Fix a rarity $0<\rho\le1/4$ and a budget $B>0$, with $h=B^{-1/2}$ and
$\delta_\ell=\rho\,16^{-(\ell+1)}$. The design is a split $\sigma+\tau+\zeta$
of positive gaps, core, resolved tail and unresolved part, with $\Gamma$ the
cost entropy of the band costs of $\sigma$, $H=\int d^{-1}\,d\tau$, $\eta(M)$
the resolved error of $\sigma+\tau$, $O_\tau(M)$ the ordinary work of $\tau$,
and $z$ the unresolved mass of the design. An enclosure is **tight** when

$$
 \bar\Gamma\le4\Gamma,\qquad \bar H\le2H,\qquad z\le\bar z\le2z,\qquad
 \bar\eta(4^k)\le2\eta(4^k),\qquad \bar O(4^k)\le2O_\tau(4^k)
$$

for every $k$. The plan searches its caps against $\bar\eta$, prices its
levels with the enclosure, stops at the first level $J$ with
$\delta_J/16<\max\{128\bar z,\rho/(16(1+\sqrt B))\}$, and falls back to the
constant $\rho/2$ when $2048\bar z>\rho$. Its weights lie within a factor
$\theta$ of the optimal ones.

| Statement | Lean-checked guarantee |
|---|---|
| [Entropy bound](../../lean/ThresholdHC/KnownLawPlanner/PlanTightRate.lean) | Band costs $a\le\bar a\le2a$ give $G(a)\le G(\bar a)\le2G(a)$. A logarithm bound within a factor two gives the second factor of the contract. |
| [Caps](../../lean/ThresholdHC/KnownLawPlanner/PlanTightRate.lean) | The envelope of a tight enclosure meets the termination requirement of the cap search. The searched cap of level $\ell$ is at most the least admissible cap of level $\ell+1$. |
| [Prices](../../lean/ThresholdHC/KnownLawPlanner/PlanTightRate.lean) | The ordinary work does not decrease with the cap. The price of level $\ell$ at its searched cap is at most four times the level work certificate of level $\ell+1$ of the upper theorem, and every price is positive when $\sigma+\tau$ has positive mass. |
| [Multilevel sum](../../lean/ThresholdHC/KnownLawPlanner/PlanTightRate.lean) | For a terminal level with $z\le\delta_J/128$ and $\rho/128<(\sigma+\tau)(\text{all gaps})$: $\sum_{\ell\le J}\sqrt{17\delta_\ell k_\ell}\le8\cdot28000\,(\sqrt{\rho\Gamma}+H)$. |
| [Certified risk](../../lean/ThresholdHC/KnownLawPlanner/PlanTightRate.lean) | The square root of the certificate is at most $\delta_J+\sqrt\theta\cdot224000\,(\sqrt{\rho\Gamma}+H)/\sqrt B$. |
| [Terminal rule](../../lean/ThresholdHC/KnownLawPlanner/PlanTightRate.lean) | When $2048\bar z\le\rho$: $z\le\delta_J/128$ and $\delta_J<4096z+\rho/(1+\sqrt B)$. |
| [Positive gaps](../../lean/ThresholdHC/KnownLawPlanner/PlanTightQuantileRate.lean) | For the quantile split of a probability law $\mu$ of positive gaps, with $z=\zeta(\text{all gaps})$: $\min\{\rho/2,\sqrt{\text{certificate}}\}\le\bigl(1+\tfrac85\max\{4096,224000\sqrt\theta\}\bigr)K_{\mu,\rho}(B)$. The fallback constant obeys the same bound, and a radius $r\le\kappa\sqrt{8\min\{\rho^2/4,\text{certificate}\}}$ with $\kappa\sqrt8\le6$ is at most six times it. |
| [Zero-atom floor](../../lean/ThresholdHC/KnownLawPlanner/PlanZeroAtomRate.lean) | For $\alpha=z_0\delta_0+(1-z_0)\eta$ with $\eta$ a probability law of positive gaps, $0<\rho\le1/2$ and $B>0$: $\rho/(1+\sqrt B)\le K_\alpha(B)$. |
| [Zero-atom design](../../lean/ThresholdHC/KnownLawPlanner/PlanZeroAtomRate.lean) | Take the quantile split of $\eta$ at the conditional rarity $(\rho-z_0)/(1-z_0)$, scaled by $1-z_0$ and cut at $h$, and put the mass at zero in the unresolved part: $z=z_0+\zeta(\text{all gaps})$. For $0\le z_0<\rho$ the [zero-atom quantile value](../arbitrary-law-zero-quantile-20261112/README.md) is $Q_\alpha=\min\{\rho,\;z+hH+h\sqrt{\rho\Gamma_\sigma}\}$. |
| [Zero-atom rate](../../lean/ThresholdHC/KnownLawPlanner/PlanZeroAtomRate.lean) | For an enclosure of that split that is tight at $z$, outside the fallback: $\min\{\rho/2,\sqrt{\text{certificate}}\}\le\bigl(1+4\max\{4096,224000\sqrt\theta\}\bigr)K_\alpha(B)$. |
| [Large unresolved mass](../../lean/ThresholdHC/KnownLawPlanner/PlanZeroAtomRate.lean) | When $2048\bar z>\rho$ the constant $\rho/2$ obeys the same bound, for every $z_0\ge0$. |
| [$C_0$ and $C_*$](../../lean/ThresholdHC/KnownLawPlanner/PlanZeroAtomRate.lean) | With $C_0(C_{\rm sum})=1+4\max\{4096,8\sqrt2\,C_{\rm sum}\}$, which does not decrease with $C_{\rm sum}$, and upper square roots within a factor two: $\min\{\rho/2,\sqrt{\text{certificate}}\}\le C_0(28000)\,K_\alpha(B)$, and the radius is at most $6\,C_0(28000)\,K_\alpha(B)$. |

$K_\alpha$ is the
[selection functional extended to laws with mass at zero](../../lean/ThresholdHC/ArbitraryLawAdaptation/ZeroModel.lean).
The paper's $C_0$ uses its explicit multilevel coefficient 30000, so the
bounds with the paper's $C_0$ and $C_*$ follow. $C_0(28000)$ is below
1,267,137 and $6C_0(28000)$ below 7,602,819. The radius statement is for
every relative upper square root, so it does not degrade for small radii.

The factor four in place of $8/5$ is (A16), $Q_\alpha\le4K_\alpha$. The
factor eight in the multilevel sum is the shift by one level: a price at
most four times the next level's certificate, and
$\delta_\ell=16\,\delta_{\ell+1}$. The unresolved mass of the design is a
parameter of the multilevel statements, and they do not need
$\sigma+\tau+\zeta$ to be a probability measure, so the same statements serve
laws with and without mass at zero.

These are statements about the numbers the planner computes. They do not
include:

- **A coin of gap zero.** The experiment of the upper theorem has positive
  gaps only. The estimator that runs the plan of a reference law with mass
  at zero, and the fair-coin likelihood its bank uses for that mass, are not
  formalized. The [validity of a plan](../known-law-planner-20261112/README.md)
  is checked for laws of positive gaps.
- **A concrete enclosure.** The theorems hold for every tight enclosure. The
  rational arithmetic that produces one for a finite law is not formalized.
- **The toolkit's planner as written**, which uses a smaller level price.
- The robust continuation, the all-budget controller and the arbitrary-law
  adaptation theorem, which remains a paper proof.

At [the proof checkpoint](https://github.com/davidiach/adaptive-threshold-estimation/commit/23617fb82d277e5935208d300b5a48917928d040),
the three new modules were built from source on Linux with Lean
`v4.36.0-rc1`, on top of a build of every project module made in the same
environment and against the Mathlib cache for the pinned revision. They
compiled without warnings.
[31 exact statements](known_law_plan_tight_rate.lean) passed with
[31 transitive axiom reports](known_law_plan_tight_rate.log), one for each
declaration of the three modules, using only `propext`, `Classical.choice`
and `Quot.sound`. The whole-project audit
`python tools/verify_project_axioms.py --no-build` passed on the same build:
1,182 modules, 12,540 constants and 10,119 theorems, with no declared axiom. Its
kernel replay was not run locally. The [native record](status.json) lists the
source hash of every project module in the import closure of the new
modules. Its base checkpoint is the head of the
[exact-rate change](../known-law-plan-rate-20261112/README.md).

One check outside Lean was run during review and is supporting evidence only.
A floating-point transcription of the plan as defined in Lean was run on 3,000
random finite laws, with independent enclosure factors in $[1,2]$, and
$[1,4]$ for the entropy. $K_\alpha$ came from the
[toolkit's exhaustive enclosure](../../toolkit/threshold_toolkit/rare_event_functional.py)
through $K_\alpha=\min\{\rho,z_0+(1-z_0)K_{\eta,\rho/(1-z_0)}\}$, an identity
that is not Lean-checked; 44 laws outside the range of that enclosure were
skipped. On the 2,226 plans, 1,233 of them with mass at zero, and the 730
fallbacks, every bound above held. The largest certified risk was 2,784 times
$K_\alpha$, attained where the term $4096z$ dominates; the largest multilevel
sum was 0.0002 of its bound.

Run `python tools/verify_known_law_plan_tight_rate.py` with the pinned
toolchain. The audit restates every definition and theorem in full and fails
if a declaration of the three modules is not registered.
