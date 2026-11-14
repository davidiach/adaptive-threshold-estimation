# The plan of a reference law under every true law coupled above it

This record covers the estimator that runs the
[known-law plan](../known-law-planner-20261112/README.md) of a reference law
when the true law has larger gaps, as in the
[robust use of the known-law estimator](../../docs/ARBITRARY_LAW_ADAPTATION.md#4-robust-use-of-the-known-law-estimator).
It turns the [level certificates under a coupled law](../robust-level-certificates-20261113/README.md)
into statements about the plan: its expected work, its squared risk, and its
rate against the selection functional of the reference.

**Reference.** $\alpha=z_0\delta_0+(1-z_0)\eta$, with $\eta$ a probability law
of positive gaps. Its positive part $c\,\eta$, $c=1-z_0$, has a design
$\sigma+\tau+\zeta=c\,\eta$. The level race of level $l$ uses the band
weights of $\sigma$, null law $\eta$, allowances $\varepsilon_l$ and
$\rho\varepsilon_l/c$, and a cap $4^{\kappa_l}$; it is defined for
$\rho\le c$. The plan's estimator runs a Poisson number of corrections at
each level with mean counts $r$, and has no argument for the true law.

**True law.** $\mu$ is a probability law of positive gaps of the form
$\mu=\pi_2+\mu_0$, where $\pi$ is a finite measure on pairs of gaps with
first marginal $c\,\eta$ and $z_1\le z_2$ almost everywhere, and $\pi_2$ is
its second marginal. Risk and work are those of the original experiment
under $\mu$, over every sign law with positive fraction at most $\rho$.

| Statement | Lean-checked guarantee |
|---|---|
| [Level race](../../lean/ThresholdHC/RobustContinuation/RobustPlan.lean) | It buys at least one flip and at most $2\cdot4^{\kappa_l}$, and returns zero or one. |
| [Bias](../../lean/ThresholdHC/RobustContinuation/RobustPlan.lean) | Under $\mu$, at a cap with $\eta_{\sigma+\tau}(4^{\kappa_l})\le\delta_l/8$ and with $\zeta(\text{all gaps})+\mu_0(\text{all gaps})\le\delta_l/8$: the mean of the race is within $\delta_l$ of the positive fraction. |
| [Corrections](../../lean/ThresholdHC/RobustContinuation/RobustPlan.lean) | Under the same conditions at every level up to $l$: the correction of level $l$ has second moment at most $17\delta_l$. |
| [Level work](../../lean/ThresholdHC/RobustContinuation/RobustPlan.lean) | Under $\mu$, with $\zeta(\text{all gaps})\le\rho$: the expected work of the race is at most the level price of the reference design with unresolved mass $\zeta(\text{all gaps})+\mu_0(\text{all gaps})$. |
| [Budget and risk](../../lean/ThresholdHC/RobustContinuation/RobustPlan.lean) | If each price is at least that level price and $\sum_lr_lk_l\le B$, the expected work is at most $B$. If each cap passes the error test and $\zeta(\text{all gaps})+\mu_0(\text{all gaps})\le\delta_J/8$, the squared risk is at most the certificate $\delta_J^2+\sum_l17\delta_l/r_l$. |
| [Admissible plan](../../lean/ThresholdHC/RobustContinuation/RobustPlan.lean) | A plan computed from an enclosure of the reference design whose unresolved mass covers $\zeta(\text{all gaps})+\mu_0(\text{all gaps})$ spends at most $B$ in expectation under $\mu$ and has root-mean-square risk at most the square root of its certificate. The same holds for the planner's searched caps and mean counts from positive weights. |
| [Uncoupled mass](../../lean/ThresholdHC/RobustContinuation/RobustPlannerOutput.lean) | With first marginal $(1-z_0)\eta$ and $z_0\le1$: $\mu_0(\text{all gaps})=z_0$. |
| [From upper bounds](../../lean/ThresholdHC/RobustContinuation/RobustPlannerOutput.lean) | For the zero-atom quantile design of $\alpha$, $0\le z_0$, $0<\rho\le1/4$, $B>0$, every enclosure tight at $z_0+\zeta(\text{all gaps})$ and weights within a factor two of the optimal ones: there is one estimator such that, under every $\mu$ as above, the expected work is at most $B$ and the root-mean-square risk at most $C_0K_\alpha(B)$. |
| [Exact planner](../../lean/ThresholdHC/RobustContinuation/RobustPlannerOutput.lean) | For every $\eta$, $0\le z_0<\rho\le1/4$ and $B>0$ there is one estimator with the same two bounds under every $\mu$ as above. |

$C_0=1+4\max\{4096,8\sqrt2\cdot28000\}$ is the
[planned coefficient](../known-law-plan-tight-rate-20261112/README.md) at the
multilevel coefficient of the checked upper theorem, and $K_\alpha$ is the
[selection functional extended to laws with mass at zero](../../lean/ThresholdHC/ArbitraryLawAdaptation/ZeroModel.lean).

The last two statements have the form "there is an estimator such that for
every true law": the estimator is fixed by the reference before the true
law is chosen. It is the plan's estimator when $2048\bar z\le\rho$ and the
square root of the plan's certificate is at most $\rho/2$, and the constant
$\rho/2$ otherwise. With $z_0=0$, $\pi$ the diagonal coupling of $\eta$ and
$\mu_0=0$, the true law is the reference itself.

The proofs reuse the plan of the known-law theorem. Its work and risk bounds
are stated for an arbitrary family of calls and an arbitrary law of the
experiment, so the reference enters through the calls and the true law
through the experiment. The three facts about the calls come from the
level certificates under a coupled law.

It does not include:

- **The coupling.** $\pi$ and $\mu_0$ are hypotheses. Deriving them from CDF
  domination of the reference law by the true law is not part of this record.
- **The toolkit's estimator.** The Lean estimator draws Poisson counts,
  reads both races of a correction from the same flips, prices a level with
  the constants of the checked level-work theorem, and uses the bank whose
  null law is the positive part of the reference. The toolkit differs in each
  of these.
- **The physical-cap median** with its conditional coverage and reported
  radius, and the connection to the paid stage.
- A concrete enclosure for a finite reference law, the all-budget controller
  and the arbitrary-law adaptation theorem, which remains a paper proof.

At [the proof checkpoint](https://github.com/davidiach/adaptive-threshold-estimation/commit/7176a2ff8eb86af691e52a84feb248d7711de855),
the two new modules were built from source on Linux with Lean `v4.36.0-rc1`,
on top of a build of every project module made in the same environment and
against the Mathlib cache for the pinned revision. They compiled without
warnings. [20 exact statements](robust_plan.lean) passed with
[20 transitive axiom reports](robust_plan.log), one for each declaration of
the two modules, using only `propext`, `Classical.choice` and `Quot.sound`.
The whole-project audit `python tools/verify_project_axioms.py --no-build`
passed on the same build: 1,192 modules, 12,676 constants and 10,249
theorems, with no declared axiom. Its kernel replay was not run locally. The
[native record](status.json) lists the source hash of every project module in
the import closure of the new modules. Its base checkpoint is the head of the
[robust-level change](../robust-level-certificates-20261113/README.md).

No numerical side check was run: the statements combine checked theorems.

Run `python tools/verify_robust_plan.py` with the pinned toolchain. The
audit restates every definition and theorem in full and fails if a
declaration of the two modules is not registered.
