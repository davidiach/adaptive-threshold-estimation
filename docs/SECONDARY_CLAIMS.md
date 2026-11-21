# Secondary-claim reconciliation

This is the disposition of the inventory in [#89](https://github.com/davidiach/adaptive-threshold-estimation/issues/89),
against `main` at `533fa752d1dd9791e5d2c261fe5404dafce0d93b` (after #118).
It separates a historical construction or constant from a later theorem with
a related conclusion. No claim is newly promoted to Lean-checked here.
The [reconciliation record](../results/secondary-claims-20261116/README.md)
identifies the inspected sources and this version of the mapping.

The core theorem and its publication are complete. The selected scope for
these auxiliary claims is explicit: retain the paper proofs listed below;
reuse checked results only with their actual hypotheses and conclusions;
track the selected approximation proof in #93 and execution verification in
#85 and #86. A paper-only disposition completes an inventory item under #89's
acceptance rule; it does not prove that claim in Lean or independently re-review
its entire paper proof.

## The nine inventory items

### 1. The simpler unknown-law confidence sequence

**Retain as paper-only:** for `0 < delta < 1`, the particular construction in
[UNKNOWN_LAW_CONFIDENCE.md](UNKNOWN_LAW_CONFIDENCE.md#all-authorized-budgets).
It assumes iid fresh latent pairs with `0 < D <= 1/2`, conditionally iid
flips, arbitrary measurable dependence of the sign on the gap, and a supplied
upper bound `u >= theta` (or `u = 1`). Its stage uses
`n = floor(sqrt(c))`, `m = floor(c/n)`, three empirical outcome proportions,
and the displayed integer thresholds. Intersections over completed stages
have simultaneous coverage at every authorized integer budget and width
tending to zero. The particular stage bound is
`P(D <= 2r) + 3a + 3tau`, not the oracle rate.

The later [arbitrary_law_controller](../lean/ThresholdHC/ArbitraryLawController/Full.lean)
is checked for `0 < rho <= 1/4` and `0 < delta <= 1/4`, with its own paid
pilot, learned law and continuation. It does not certify the simpler
construction's thresholds, width formula, or full `u = 1` domain.
[Controller evidence](../results/arbitrary-law-controller-20261116/README.md).

**Retain the sharper coefficient as paper-only:** the note's
[Bernoulli-subfamily lower bound](UNKNOWN_LAW_CONFIDENCE.md#a-time-uniform-lower-bound-in-the-original-experiment)
uses one online controller, a deterministic nonincreasing half-width envelope,
joint coverage and width probability `1-delta`, and `0 < rho <= 1/4`. Its
coefficient is `sqrt(3(1-delta)rho/64)` multiplying
`sqrt(log(log n)/n)` infinitely often. It cites an external proposition.
The checked [law_dependent_interval_lower](../lean/ThresholdHC/AnytimeLower/Intervals.lean)
instead gives `10^-22 K(n/budgetInflation(delta,n)) <= t(n)` for arbitrarily
large `n`, under its measurable observable interval and joint-event hypotheses,
with `0 < delta <= 1/4`; it requires no monotonicity of `t`.
Its stronger law dependence does not supply the historical numerical coefficient.
[Lower-bound evidence](../results/anytime-asymptotic-20261105/README.md).

### 2. Unknown rarity

**Retain as paper-only:** the [unknown-rarity obstruction](process/TRACK_D.md#an-obstruction-to-completely-uniform-adaptation-to-unknown-rarity).
For a fixed known `0 < d < 1/2`, the same family `A_B` must work without
receiving `rho`, stop almost surely at every constant sign prior
`theta in [0,1/4]`, and satisfy a single finite-constant RMS bound
`C min(rho, sqrt(rho)/(d sqrt(B)))` for every `B >= 1`, every
`0 < rho <= 1/4`, and every `theta <= rho`. The proof first forces zero output
at `theta = 0`, transfers this through stopped-transcript absolute continuity,
then contradicts the rate at `theta = rho = 1/4`.
The checked adaptation controller receives `rho`; it neither proves nor
contradicts this different quantifier order. Additive error floors, a positive
lower bound on rarity, and restricted parameter ranges remain outside the
obstruction. This reconciliation introduces no new unknown-rarity theorem.

*Update, 21 November 2026.* The obstruction is now Lean-checked in the Tier 6
adaptive experiment at the gap law $\delta_d$, with the expected-work form and
the stopped-transcript absolute continuity it uses; one estimator at one
budget $B>4C^2/d^2$ that stops almost surely at $\theta=1/4$ already fails the
bound ([record](../results/unknown-rarity-20261121/README.md)). The process note keeps its original status
line.

### 3. Earlier critical single-coin and additive-class claims

The [historical critical note](../research/2026-10-27-critical-two/construction.tex)
fixes `a = 1/4`, the exact quadratic law, `0 < rho <= 1/4`, and
`L = 1 + log(1/rho)`. It studies separate uniform variance/raw-second-moment
and expected-work suprema for observable, randomized single-coin procedures
with unbounded stopping; its small-bias version permits bias `rho/64`.

**Existing checked lower-bound component:**
[critical_base_cost_explicit](../lean/ThresholdHC/CriticalAllSizes/BaseCost.lean)
has precisely a uniform extended-variance bound `V`, finite expected work
under every measurable capped prior, and uniform bias at most `rho/64`.
It proves `rho * criticalLogFactor(rho) / 15000000000 <= V * W_null`.
The raw version uses `CappedPopulationGuarantee` and coefficient `1/10000000000`.
Null work is bounded by the corresponding uniform work supremum, so these
are the checked lower-bound mechanisms behind the product order; this map
does not invent a new exact theorem for a separately defined paper infimum.
[Exact targets](../lean/ThresholdHC/CriticalAllSizes/Specification.lean) ·
[audit record](../results/critical_all_sizes_002.json).

**Retain as paper-only:** the historical infimum formulations and their
particular construction, the component-selection lemma, and the exact
additive-class theorem with a seed-preselected integrable random coin count,
heterogeneous local kernels, signed sums and its explicit square-integrability
conditions. The checked
[critical_algorithm_lower_bound](../lean/ThresholdHC/CriticalEntropy/CriticalMinimax.lean)
covers every `Tier6.AdaptiveEstimator` with its uniform budget, for `B >= 1`;
the [critical_minimax_upper_bound](../lean/ThresholdHC/CriticalUpper/Full.lean)
proves the matching unrestricted order with coefficient `100000`.
Those resolve the broader critical minimax question. They do not by themselves
provide a formal embedding of the historical additive class or the historical
component-selection proof. The checked upper construction's single-coin
moment/work constants are `28 rho` and `112000000 criticalLogFactor(rho)`.
[Upper evidence](../results/critical_upper_components_003.json).

### 4. Population-step auxiliary claims

**Retain the following claims as paper-only**, with the domains in the
[population-step report](../research/2026-10-27-population-step/FINAL_REPORT.md):

| Claim | Exact scope retained |
|---|---|
| Conditional information reduction | A uniform directional Fisher-information/work bound for every capped one-coin policy, plus the stated likelihood regularity, transfers to finite-prefix creation/interleaving. Terminal testing requires termination at both endpoints and the uniform expected-work bound. A variance/work lower bound is not that information premise. |
| Radial counterexample | For the fixed quadratic law and `q_eta = (1+eta) min(1,b^2/d^2)/2`, `abs(eta) <= 1/2`, with the cutoff calibrated to rarity, the supremum over finite-cap policies has information/work ratio at least `a^2 rho/(32L)`. This refutes the proposed extra-log bound only in that radial direction. |
| Calibrated radial upper bound | On that known-profile submodel, with exact calibration integrals, `R_radial(B) <= min(rho/4, sqrt(160 rho L/B))`; the displayed variance/work constants and approximate-calibration perturbation bound belong to this construction. This is not an arbitrary-sign-law upper bound. |
| Restricted pilot correction | An independent pilot selecting only a scalar correction coefficient for fixed unbiased features, with the stated parameter-independent positive variance, cannot improve minimax raw production MSE over the best fixed coefficient. It is not a general prohibition on acquisition feedback or nonlinear estimators. Lean-checked since 21 November 2026 for an abstract mixture model of one coin's observations, with a nonvacuity witness ([record](../results/pilot-correction-20261121/README.md)). |

The report's inherited single-coin obstruction is mapped in item 3. Its
finite-prior dynamic-program values are exact finite examples, not a new
uniform expected-budget theorem. The later full critical theorem resolves the
report's historical broad open question by a different argument; it does not
upgrade these four auxiliary claims or their constants.

### 5. Nonlinear feedback, depth and finite approximation

**Retain as paper-only:** the following claims of the
[nonlinear report](../research/2026-10-27-nonlinear-population/FINAL_REPORT.md).

| Claim | Exact scope retained |
|---|---|
| Strict acquisition-feedback advantage | Law `(delta_(1/4)+delta_(1/8))/2`, `rho = 1/4`, deterministic total cap two. The displayed feedback policy has worst MSE below `0.015443` over the entire feasible sign triangle; every preselected independent local-acquisition design has MSE above `0.015475`, including shared seeds and nonlinear terminal estimation. This does not compare expected-budget-two procedures or prove an asymptotic advantage. |
| Bounded-depth obstruction | Exact quadratic law, `K >= 1`, hard pair with separation `Delta_K = rho/((K+1)(2K+1))`, identical word probabilities through depth `2K`. Arbitrary feedback with that per-coin depth cap has RMS at least `Delta_K/2`. The unrestricted exit bound is `p_K >= 1-4 epsilon^2/Delta_K^2`; each `K` uses a different pair, so these tails cannot be summed under one population. Since 21 November 2026 the population half is Lean-checked for every cap, gap law and matching pair (equal transcript laws under arbitrary feedback and the floor `|theta_H-theta_L|/2`); the explicit pair, `Delta_K` and the exit bound stay paper-only ([record](../results/depth-obstruction-20261121/README.md)). |
| Approximation of the expected-budget minimax value | With exact known-law bin masses, total truncation cap `N`, gap mesh `eta`, downward prior mesh `gamma`, and the same uniform expected budget `B > 0`, the squared-value error is at most `rho^2 B/N + rho^2 N(eta+gamma) + 2rho gamma + rho^2 N^2(eta+gamma)/(4(B+N^2(eta+gamma)))`. The activation correction preserves the budget; the claim is not a solved numerical convex program or a complexity theorem. |
| Clipping and pilot-profile observations | For an unbiased `F`, `theta in [0,rho]`, finite variance `sigma^2`, and `E(F-theta)^4 <= K sigma^4` with `1 <= K < infinity`, clipping to `[0,rho]` has RMS at least `min(rho,sigma)/(16K)`. The [clipping note](../research/2026-10-27-nonlinear-population/audit/CLIPPING_BOUNDARY.tex) retains this conditional transfer and its independent-noise counterexample; both are Lean-checked since 21 November 2026, with the uniform corollary over every rare sign law and the noise construction in the original experiment ([record](../results/clipping-boundary-20261121/README.md)). No uniform kurtosis bound for the telescope is supplied. Shallow word matching alone does not control the response-weighted calibration bias. |

The checked [fixed_cap_identification](../lean/ThresholdHC/CapIdentification/Full.lean)
and [selection finite approximation](../lean/ThresholdHC/SelectionStability/FiniteApproximation.lean)
have different objects: fixed observation caps and the deterministic selection
functional, respectively. Neither is an exact formalization of the displayed
depth hard pair or the budget-preserving squared-minimax-value approximation.
The synthetic 7,680-replicate experiment remains numerical evidence.

### 6. The particular critical-Psi witness

**Lean-checked since 20 November 2026** (`psi_sequence` in
[PaperCorollaries](../lean/ThresholdHC/PaperCorollaries/Full.lean),
[record](../results/paper-corollaries-20261120/README.md)), after first being
retained as a paper derivation: at the exact quadratic law,
`rho_n = exp(-exp(n))` and `B_n = rho_n^(-2)` give a divergent risk/Psi ratio
in the [results guide](RESULTS.md#critical-power-margin-full-minimax-characterization),
at least `7*10^-20 sqrt(1 + n)` times `Psi` for `n >= 3`.
The checked [critical_matching_psi_refuted](../lean/ThresholdHC/CriticalPsi/Full.lean)
already proves, for every `C > 0`, the existence of valid `rho` and `B >= 1`
with risk greater than `C Psi`. Its proof uses budget
`L(1+log L)/rho`, not the prescribed sequence.
[Exact statements](../lean/ThresholdHC/CriticalPsi/Specification.lean) ·
[evidence](../results/critical_psi_001.json).
The broader refutation is complete; the particular sequence is not a pending
premise of that theorem. Since 20 November 2026 (`PaperStatements`) the same
sequence is also checked in the critical theorem's own model, with the exact
`Psi`, `Psi > 0` and constant `10^-18/16`, together with the arithmetic of the
slow-divergence remark, `sqrt(1 + log(1 + log(1/rho))) < 2.54` for `10^-100 <= rho <= 1/4`
(`critical_psi_divergence`, `critical_slow_divergence` in
[PaperStatements](../lean/ThresholdHC/PaperStatements/Full.lean), [record](../results/paper-statements-20261120/README.md)).

### 7. Fixed-plan comparison and its analytic integral

**Retain as paper-only:** for `n` independent fresh items and odd `m` flips
per item, the majority indicator has bias in absolute value at most the
mean misclassification probability `e_m`, and the average has variance at
most `1/(4n)`, hence RMS at most `sqrt(e_m^2+1/(4n))`, uniformly over signs
at the specified known gap law. For success rates uniformly distributed on
`[0,1]`, with `a=(m+1)/2`, the analytic error integral is
`2 integral_0^(1/2) I_p(a,a) dp = binom(2a,a)/2^(2a+1) = 1/(2a Beta(a,1/2))`.
See [practical comparison](RESULTS.md#practical-comparison-with-a-fixed-plan)
and the formula in [EvenlySpread.majority_terms](../toolkit/threshold_toolkit/planner.py).
Since 21 November 2026 the bias, variance and RMS bound and the analytic
integral are Lean-checked for the plan run in the original experiment, with
the integrand in binomial-tail form `P(Bin(2a-1,p) >= a)` rather than as
`I_p(a,a)` ([record](../results/fixed-plan-20261121/README.md)).
The integral and bias/variance formula are separate from their floating-point
evaluation. Deterministic calculator correctness belongs to #85; independent
coin callbacks and actual execution belong to #86. Simulation comparisons
are not universal performance theorems.

### 8. The auxiliary light-contraction constant

**Retain `C_V < 256` as paper-only:** for the exact independent multiplier
with CDF `2 exp(-1/(2v^2))` on `(0,1/4)` and the remaining atom at `1/4`,
`p_k = P(2^(-k-1) < V <= 2^(-k))`, the particular series in
[(A4)](ARBITRARY_LAW_ADAPTATION.md#1-finite-envelopes-and-the-zero-atom)
is bounded by 256. Its selected-submeasure entropy calculation belongs to
that paper route. The checked [light-contraction record](../results/arbitrary-law-light-20261106/README.md)
uses a different fixed reference code to prove the required post-division
entropy factor `1024` and tail factor `32`, hence the factor-32 selection
comparison. No proof of the sharper intermediate series is needed by that
completed formal result, and none is claimed here.

*Update, 21 November 2026.* The constants of this item are now Lean-checked
separately: $p_2=1-2e^{-32}$, $p_k\le2e^{-4^k/2}$ for $k\ge3$, a first
summand below $192$, $C_V<256$ (in fact $C_V\le1024/5$), $\mathbb
EV^{-2}\le C_V$, $\mathbb EV^{-2}\le256$ and $\mathbb EV^{-1}\le16$, for
every law with that distribution function
([record](../results/light-contraction-constant-20261121/README.md)). The entropy inequality
$\Gamma_{\mathcal L(VD)}\le C_V\Gamma_\mu$ of (A4) stays paper-only.

### 9. Cross-check of the rest of the current inventory

The [33-entry status source](../paper/v6/status.json) remains unchanged:
32 entries are Lean-checked in their stated scopes, and one is paper-only.
The following dispositions cover the additional boundaries exposed by
RESULTS and manuscript section 18.

| Boundary | Disposition |
|---|---|
| Critical-window Corollary 14.14 and Remark 14.15 | Kept paper-only by the decision in #100, and Lean-checked since 20 November 2026 in `CriticalWindow`. For `3/2 <= alpha <= 3` they simplify the checked uniform rate using constants `5.13` and `3.4*10^5`; the remark reads off the exponent-dependent asymptotics and transition window. The Lean targets give the remark's universal constants explicitly. The five frozen `PowerWindow` targets do not include these statements; the v6 status table changes with the next manuscript update. [Source](../paper/v6/psi-window.tex), [record](../results/critical-window-20261120/README.md). |
| Finite-law `(1+epsilon)` approximation | Selected formal follow-up #93. The entropy perturbation and compression invariant are already checked; concrete bins, parameter/state bounds, the finite-law bridge and terminating rational endpoint selection are the remaining assembled theorem. Bit complexity and Python execution have separate scopes. [Existing components](../lean/ThresholdHC/SelectionApproximation/README.md). |
| Earlier `5/3` and algebraic quantile-comparison constants | Their particular computation-note derivation stays a paper proof. The checked all-law `8/5` comparison gives a stronger numerical inequality on the same positive-gap probability-law domain; this does not identify the historical argument with the later proof. [Current comparison](RESULTS.md#general-law-rare-event-characterization), [computation note](RARE_EVENT_COMPUTATION.md). |
| Earlier above-two construction and constants | Retain the original paper construction and constants, including `153/56` for its second moment. The formal observable construction uses `28` and its own work bound and lower coefficient; its exact rate theorem is already checked. [Scope map](RARE_ABOVE_TWO.md), [original record](../research/2026-10-27-route-a/CHECKPOINT.md). |
| Main confidence, hard-cap, time-uniform, tail-certificate and arbitrary-law results | Already checked in their stated scopes and records in [RESULTS](RESULTS.md). A section containing a paper proof does not imply that its current theorem lacks a Lean proof. Items 1 and 8 isolate the distinct auxiliary construction and constant. |
| Exact-selection complexity and sharp cap convergence | Open research in #87 and #88. Existing exact finite-menu reduction, approximation results and sufficient convergence rates are not solutions to these optimality questions. |
| Calculator arithmetic, finite precision, runtime and PRNG | #85 and #86. Mathematical Lean proofs do not certify CPython execution, numerical enclosures or ideal independence of a seeded PRNG. Finite certificates and benchmarks retain their explicitly limited evidence status. |
| Reference-law zero atom and classical planner choices | Retain the documented model boundary in [ARBITRARY_LAW_FORMALIZATION](ARBITRARY_LAW_FORMALIZATION.md). The final theorem charges zero mass through the positive-part split and does not use a physical fair-coin null-likelihood implementation. These are not missing premises in the proved controller. |
| Novelty, external review and practical superiority | No new claim or completion gate. Existing provenance and benchmark limitations remain as recorded. Historical reports saying the general minimax problem was open describe their own checkpoints. |

Every original checkbox now has an explicit disposition. The selected next
mathematical extension is #93; this reconciliation neither closes that proof
task nor promotes any retained paper-only statement.
