# The certificate of a known-law plan

This record covers the plan of the
[known-law estimator](../../docs/KNOWN_LAW_ESTIMATOR.md#work-and-error-of-a-returned-plan):
its cap search, its level prices, its mean counts and its squared-error
certificate, and the proof that the certificate is valid. The level price
uses the constants of the Lean-checked level-work theorem.

The known gap law is split as $\sigma+\tau+\zeta$: the selected core, whose
gaps are bounded below, the resolved tail and the unresolved part. Fix a
rarity $0<\rho\le1/4$ and write $\delta_\ell=\rho\,16^{-(\ell+1)}$. A plan has a
terminal level $J$, a cap $4^{\kappa_\ell}$ and a price $C_\ell$ for each
level, and positive mean counts $r_0,\dots,r_J$. Its certificate is

$$
 \delta_J^2+\sum_{\ell=0}^{J}\frac{17\,\delta_\ell}{r_\ell}.
$$

The plan's estimator runs, at each level, a Poisson number of corrections
with mean $r_\ell$. A correction of level $\ell$ runs the races of levels
$\ell$ and $\ell-1$ on one coin. The estimator observes flips only; it sees
no gap, sign or component label. $\eta(M)$ is the resolved error of
$\sigma+\tau$ at cap $M$, $\Gamma$ the cost entropy of the band costs of
$\sigma$, $H=\int d^{-1}\,d\tau$, $O_\tau(M)$ the ordinary work of $\tau$ and
$z$ the mass of $\zeta$. All statements hold under every rare prior, that is
every measurable gap-dependent sign law with positive fraction at most $\rho$.

| Statement | Lean-checked guarantee |
|---|---|
| [Level races](../../lean/ThresholdHC/KnownLawPlanner/PlanFamily.lean) | Let $z\le\delta_\ell/8$. At any cap $4^k$ with $\eta(4^k)\le\delta_\ell/8$ the race of level $\ell$ has bias at most $\delta_\ell$. When the caps of all levels up to $\ell$ pass that test, the correction of level $\ell$ has second moment at most $17\delta_\ell$. Every run of a race at cap $4^k$ buys at most $2\cdot4^k$ flips. |
| [Level price](../../lean/ThresholdHC/KnownLawPlanner/PlanFamily.lean) | For $z\le\rho$, the expected work of the race of level $\ell$ at cap $4^k$ is at most $\min\{2\cdot4^k,\;128(\ell+1)\Gamma+6H^2/\rho+2O_\tau(4^k)+2z\,4^k\}$, and this price is at least 1. |
| [Any positive counts](../../lean/ThresholdHC/KnownLawPlanner/PlannedEstimator.lean) | The Poisson multilevel estimator with rates $r_i$ has expected work at most $\sum_ir_ic_i$ and squared risk at most $\sum_iv_i/r_i+b^2$, where $c_i$ bounds the expected cost of call $i$, $v_i$ its second moment and $b$ the bias of the sum. |
| [Work of a plan](../../lean/ThresholdHC/KnownLawPlanner/PlanCertificate.lean) | When $z\le\rho$, every $C_\ell$ is at least the level price and $\sum_\ell r_\ell k_\ell\le B$, with $k_0=C_0$ and $k_\ell=C_\ell+C_{\ell-1}$: the expected work is at most $B$. |
| [Error of a plan](../../lean/ThresholdHC/KnownLawPlanner/PlanCertificate.lean) | When $\eta(4^{\kappa_\ell})\le\delta_\ell/8$ for every $\ell\le J$ and $z\le\delta_J/8$: the squared risk is at most the certificate. |
| [Enclosures](../../lean/ThresholdHC/KnownLawPlanner/PlanCertificate.lean) | An enclosure is a set of upper bounds for $\Gamma$, $H$, $z$, and for $\eta(M)$ and $O_\tau(M)$ at every cap. A plan whose caps pass the test against the enclosure's error envelope, whose terminal level covers the enclosure's unresolved mass and whose counts are priced by the enclosure's level prices has expected work at most $B$ and root-mean-square risk at most the square root of its certificate. The minimax risk at budget $B$ is at most the smaller of that and the constant fallback $\rho/2$. |
| [Cap search](../../lean/ThresholdHC/KnownLawPlanner/PlanCaps.lean) | Starting from the cap 4, each level multiplies the cap by four until the envelope is at most $\delta_\ell/8$ and carries the cap to the next level. The search needs the envelope to get below every positive level along the powers of four; the exact resolved error of a finite measure does. The caps returned pass the test, every cap the search passed over failed it, and the caps are at least 4 and do not decrease. |
| [Counts from weights](../../lean/ThresholdHC/KnownLawPlanner/PlanAllocation.lean) | The mean counts $n_i=Bw_i/\sum_jk_jw_j$ spend the budget exactly. With $\sqrt{v_i/k_i}\le w_i\le\theta\sqrt{v_i/k_i}$, $\sum_iv_i/n_i\le\theta\,(\sum_i\sqrt{v_ik_i})^2/B$. |
| [Planner output](../../lean/ThresholdHC/KnownLawPlanner/PlanCertificate.lean) | The plan with the searched caps, the enclosure's prices and the counts from any positive weights is admissible, for every terminal level $J$ with the enclosure's unresolved mass at most $\delta_J/8$. With weights within a factor $\theta$ its certificate is at most $\delta_J^2+\theta\,(\sum_\ell\sqrt{17\delta_\ell k_\ell})^2/B$. |

The proofs reuse the checked upper theorem: its bank and ordinary races, its
population error and work bounds, the telescoping corrections and the Poisson
realization. That theorem runs each level at the least admissible cap with the
optimal counts; here the caps and counts are those of the plan.

This is a mathematical specification of a planner and a proof about every
plan that meets it. It differs from the toolkit's planner in three ways, and
it is not a proof about that program:

- **Level price.** The toolkit uses $80(\ell+2)\bar G+4H^2/\rho$ and the
  paper $80(\ell+1)\Gamma+4H^2/\rho$, where this record has
  $128(\ell+1)\Gamma+6H^2/\rho$. The smaller prices are not
  Lean-checked; a plan priced with them is not covered.
- **Counts.** The estimator here draws Poisson counts. The toolkit rounds its
  mean counts at random.
- **Corrections.** A correction here reads both races from the same flips.
  Its cost is the larger of the two and it is priced by their sum. The toolkit
  runs the coarse race on further flips of the same coin.

It does not include:

- The rate of the plan: the comparison of the certificate with the selection
  functional, the coefficients $C_0$ and $C_*$, and the terminal rule that
  chooses $J$ from the budget.
- The planner's enclosures for a particular law, such as the rational
  arithmetic for finite laws, and a reference law with mass at zero.
- The robust continuation, the all-budget controller and the arbitrary-law
  adaptation theorem, which remains a paper proof.
- Python execution of the toolkit.

At [the proof checkpoint](https://github.com/davidiach/adaptive-threshold-estimation/commit/260788218f808ff9075a13f715e67c07e85d1f84),
the five new modules were built from source on Linux with Lean `v4.36.0-rc1`,
on top of a build of every project module made in the same environment and
against the Mathlib cache for the pinned revision. They compiled without
warnings. [49 exact statements](known_law_planner.lean) passed with
[49 transitive axiom reports](known_law_planner.log), one for each
declaration of the five modules, using only `propext`, `Classical.choice` and
`Quot.sound`. The enclosure is restated through its constructor. The
whole-project audit `python tools/verify_project_axioms.py --no-build` passed
on the same build: 1,177 modules, 12,477 constants and 10,060 theorems, with no
declared axiom. Its kernel replay was not run locally. The
[native record](status.json) lists the source hash of every project module in
the import closure of the new modules. Its base checkpoint is the head of the
[zero-quantile change](../arbitrary-law-zero-quantile-20261112/README.md).

One check outside Lean was run during review and is supporting evidence only.
On 300 plans with levels returned by the
[toolkit's planner](../../toolkit/threshold_toolkit/known_rare_estimator.py),
1,366 levels in all, exact rational arithmetic confirmed the facts stated
here that do not depend on the price constants: the level accuracies, the
cap search including 2,525 failed probes, the terminal level, the work
identity $\sum_\ell n_\ell k_\ell=B$ and the certificate formula. In floating
point the variance term lay between $(\sum\sqrt{v k})^2/B$ and twice that.

Run `python tools/verify_known_law_planner.py` with the pinned toolchain. The
audit restates every definition and theorem in full and fails if a
declaration of the five modules is not registered.
