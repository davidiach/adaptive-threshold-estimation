# Current work and completion ledger

Use this page to choose follow-up work. [RESULTS.md](RESULTS.md) records the
current mathematical scope; [VERIFY.md](VERIFY.md#choose-checks-by-task) maps
changes to checks. The detailed completion ledger is preserved below for source,
review, and CI history.

## Current priorities

This section was brought up to date on 19 November 2026 with
[#155](https://github.com/davidiach/adaptive-threshold-estimation/pull/155),
which publishes the [release build](../paper/v6/README.md#release-build) of
the v6 manuscript. An AI review of the proofs, the paper and the toolkit on
that date found no mathematical error; its corrections to wording, the
toolkit and the audit tools are in
[#149](https://github.com/davidiach/adaptive-threshold-estimation/pull/149),
[#151](https://github.com/davidiach/adaptive-threshold-estimation/pull/151),
[#152](https://github.com/davidiach/adaptive-threshold-estimation/pull/152)
and [#154](https://github.com/davidiach/adaptive-threshold-estimation/pull/154).
The first table lists what is open. The second lists areas that are
finished and where their evidence is.

### Open work

| Area | What is open | Starting point |
|---|---|---|
| Toolkit outputs and Lean statements ([#85](https://github.com/davidiach/adaptive-threshold-estimation/issues/85)) | The opt-in certificate path checks individual outputs. Full internal solver transcripts, other selection entry points, concrete planners and schedules, and the floating calculators are not connected yet. | [Deterministic verification](DETERMINISTIC_VERIFICATION.md) |
| Stochastic execution ([#86](https://github.com/davidiach/adaptive-threshold-estimation/issues/86)) | No proof that the Python execution and its PRNG refine the observable model. | [Deterministic verification](DETERMINISTIC_VERIFICATION.md) |
| Exact selection ([#87](https://github.com/davidiach/adaptive-threshold-estimation/issues/87)) | The complexity of exact selection with unrestricted band costs. A relative approximation is Lean-checked. | [Finite-law approximation](FINITE_SELECTION_APPROXIMATION.md) |
| Finite-cap convergence ([#88](https://github.com/davidiach/adaptive-threshold-estimation/issues/88)) | The sharp rate and constants for the ordinary and genie programs. The best checked cap is $N\ge4B/9$ (`SquareRootCap`, Theorem Q.1 of the paper). | [Cap rate](FINITE_CAP_RATE.md), [Lean statement](../lean/ThresholdHC/SquareRootCap/Specification.lean) |
| Constants of the main law (no issue yet) | The lower constant $1/6$ is sharp and the upper constant is $12$ (`UpperScale` with the call cost of `UpperCallCost`, after $119$ in `UpperConstant`, $45$ in `UpperWork`, $36$ in `UpperMoment`, $27$ in `UpperMixture`, $19$ in `UpperCost`, $17$ in `UpperDisagreement`, $15$ in `UpperSign` and $13$ in `UpperQuarter`; the paper proves $12$ in Appendix AB, and the frozen target states $512$). A [numerical study](../research/2026-11-19-upper-constant-12/README.md) puts the actual worst ratio of the algorithm behind $12$ near $5.4$ (that of the single-level algorithm behind $36$ is near $7.6$, [earlier study](../research/2026-11-18-upper-constant/README.md)). The remaining slack is in the Hoeffding bounds behind the call second moment $13/2$ and the padded call cost $26/5$, against exact values near $2.2$ and $3.6$, and in the bias bound. With the paper's thresholds, the method of the Lean proof gives at best about $11.2$ with the current bias bound. A [scoping study](../research/2026-11-19-one-coin-bounds/README.md) finds that Bahadur's binomial tail bound in place of Hoeffding's, with the same proof structure and estimator, would give about $7.75$ ($7.35$ with a bias bound near $1/2$), so $9$ is a safe target and $8$ needs a median bound or a sharp bias bound as well; interval arithmetic on exact one-coin values would gain little. For $B\ge25$ the best lower constant lies in $[0.175198,\,0.186752]$ (`LargeBudgetRMS`, Theorem AA.7 of the paper); its exact value is open. | [Results](RESULTS.md#minimax-law-and-unbiasedness), [Lean statement](../lean/ThresholdHC/LargeBudgetRMS/Specification.lean) |
| The paper's status entry for the critical window | Corollary 14.14 and Remark 14.15 of v6 §14.8, the critical-window simplification, were the one tracked result with a paper proof only. Lean checks them since 20 November 2026 (`CriticalWindow`). The v6 status source and the manuscript still list them as a paper proof; the next manuscript update moves them, after which all 33 tracked results are Lean-checked. | [Results](RESULTS.md#the-variational-modulus-in-closed-form), [record](../results/critical-window-20261120/README.md) |
| Remaining paper and guide claims (no issue yet) | Twelve claims stated with only a written proof, numerics or an existential constant are Lean-checked since 20 November 2026 (`PaperStatements`, fifteen targets with two bridging statements and one new corollary), after Corollary 14.14, Remark 14.15 and three corollaries (`CriticalWindow`, `PaperCorollaries`). The pilot-feedback and scheduled-update separations are in the audited library since 20 November 2026 (`PilotFeedback`, [record](../results/pilot-feedback-20261120/README.md)); the one-update stopping-time package followed on 21 November 2026 with its certificate split into 27 pieces per row (`StoppingUpdate`, [record](../results/stopping-update-20261121/README.md)); the two-update package stays outside it until its certificate is split, since its research build of one row ran out of memory above 13.5 GB. Since 21 November 2026 Lean also checks the impossibility half of Proposition `prop:bounded` (`NonnegativeUnbiased`) and states the explicit constants $15/(256\sqrt2)$, $1/256$ and $28\rho$ (`ExplicitConstants`), and both corollaries of the finite-gap manuscript, `cor:one-gap` and `cor:mse` (`FiniteGapCorollaries`, [record](../results/finite-gap-corollaries-20261121/README.md)), the remark that stopping a time-uniform procedure at budget $n$ gives the fixed-budget coefficient (`StoppedTimeUniform`, [record](../results/stopped-time-uniform-20261121/README.md)), $\theta=G_{\mu,q}(P>1/2)$ for every law (`LatentThreshold`) and its converse, the $G$-form of the population class (`LatentDisintegration`, [record](../results/latent-disintegration-20261121/README.md)), the zero-atom split of the selection functional (`ZeroAtomSplit`), the explicit fixed-cap estimate (`CapIdentificationEstimate`), the bias-subtraction remark of Appendix H (`BiasSubtraction`), the common-pair RMS bound at the critical law (`CriticalPairRMS`), the coefficient $1/6$ in the restricted settings of the rms-gap note (`RestrictedRMS`), the strictness of the sharp bound for $B\ne4$ (`SharpStrict`), the global-cut bound of the certified-selection note (`GlobalCut`), and Proposition `prop:psi-null` with its corollary $R\ge\Psi/8192$, which proves the single-coin obstruction premise of the transfer theorems for every gap law (`PsiNull`, [record](../results/psi-null-20261121/README.md)), its confidence form $r^{\rm exp}\ge\Psi/8192$ and the exact-power-law confidence rate above two of the confidence-transfer note (`ConfidenceTransferSteps`, [record](../results/confidence-transfer-steps-20261121/README.md)), the three-piece form, $c<C$ and hard assignments of Theorem 13.2 (`EntropyTailForms`, [record](../results/entropy-tail-forms-20261121/README.md)), the noninterval optimal assignment of the rare-event discussion (`NonintervalSelection`, [record](../results/noninterval-selection-20261121/README.md)), the stopping-program factor $3\sqrt7/2$ of the rms-constants review (`ProgramFactor`, [record](../results/program-factor-20261121/README.md)), the fixed-plan majority bound of the toolkit comparison (`FixedPlan`, [record](../results/fixed-plan-20261121/README.md)), the sharpness of the magnitude-oracle coefficient $1/2$ (`OracleSharpness`, [record](../results/oracle-sharpness-20261121/README.md)), the clipping boundary of the nonlinear-population audit note (`ClippingBoundary`, [record](../results/clipping-boundary-20261121/README.md)), the oracle upper bound $R\le\omega/2$, which makes $1/2$ the exact oracle coefficient (`OracleUpper`, [record](../results/oracle-upper-20261121/README.md)), the upper-constant study's remark that clipping the output to $[0,1]$ can only help (`ClippedOutput`, [record](../results/clipped-output-20261121/README.md)), the 20+5 revisit witness of the rms-constants package (`RevisitUpper`, [record](../results/revisit-upper-20261121/README.md)), the Hoeffding replication count of Proposition `prop:outer` (`ObservedHoeffding`, [record](../results/observed-hoeffding-20261121/README.md)), and the Giles–Haji-Ali assumptions for the class of Corollary `cor:nested`, against transcriptions not yet compared with the paper's text (`NestedAssumptions`, [record](../results/nested-assumptions-20261121/README.md)), the constant $C_V<256$ of the light random contraction (`LightContractionConstant`, [record](../results/light-contraction-constant-20261121/README.md)), the 64-band selection example for the formal solver (`BandCostExample`, [record](../results/band-cost-example-20261121/README.md)), the repeated-check counterexample of the confidence-transfer package (`RepeatedCheck`, [record](../results/repeated-check-20261121/README.md)), the countable-reservoir termination counterexample of the minimax audit (`ReservoirTermination`, [record](../results/reservoir-termination-20261121/README.md)), the upper end $c_*<1.462554551280$ with the whole of `thm:sharp-quantile-factor` (`QuantileFactorUpper`, [record](../results/quantile-factor-upper-20261121/README.md)), the per-coin creation fee of the model paragraph (`CreationCharge`, [record](../results/creation-charge-20261121/README.md)), the pilot events (A8) and (A11) under the law of the whole learning stage (`StagePilotLaw`, [record](../results/stage-pilot-law-20261121/README.md)), the bias audit of the constant search (`BiasAudit`, [record](../results/bias-audit-20261121/README.md)), the obstruction to uniform adaptation to unknown rarity (`UnknownRarity`, [record](../results/unknown-rarity-20261121/README.md)), the hard-cap counterexamples of the hard-budget note (`HardCapNecessity`, [record](../results/hard-cap-necessity-20261121/README.md)), the restricted pilot correction of the population-step note (`PilotCorrection`, [record](../results/pilot-correction-20261121/README.md)), and the population half of the bounded-depth obstruction (`DepthObstruction`, [record](../results/depth-obstruction-20261121/README.md); the exit bound remains), Theorem `loc:thm:counter` with Proposition `loc:prop:noise` of the localization appendix (`LocalizationCounter`, [record](../results/localization-counter-20261121/README.md)), the categorical case of the affine comparison lemma of the full critical note (`AffineComparison`, [record](../results/affine-comparison-20261121/README.md)), the two-flip acquisition-feedback advantage against the normal-form comparison class (`TwoFlipFeedback`, [record](../results/two-flip-feedback-20261121/README.md)), the simpler unknown-law confidence sequence (`UnknownLawConfidence`, [record](../results/unknown-law-confidence-20261121/README.md)), the decimals and remarks of the upper-12 appendix (`UpperTwelveNumerics`, [record](../results/upper-twelve-numerics-20261121/README.md)), the calibrated radial upper bound of the population-step note (`RadialUpper`, [record](../results/radial-upper-20261121/README.md)), the two-sided time-uniform order in one model (`TimeUniformTwoSided`, [record](../results/time-uniform-two-sided-20261121/README.md)), the explicit odd-Legendre pair of the bounded-depth obstruction (`DepthLegendre`, [record](../results/depth-legendre-20261121/README.md)), and the known-gap estimator of the minimax audit that needs no rarity (`KnownGapRarity`, [record](../results/known-gap-rarity-20261121/README.md); its shared-regression example was not taken up), and the margin-class corollaries `cor:gap` and `cor:power` without its row $\alpha=1$ (`MarginClasses`, [record](../results/margin-classes-20261121/README.md)). The six items of the ninth scoping batch and the ten of the tenth (21 November 2026, from `ClippedOutput` on) are all in the audited library, and so are the thirteen of the eleventh (from `CreationCharge` on), four of them in part: the exit bound of the bounded-depth obstruction (its explicit Legendre pair followed in the twelfth batch), the Poisson case of the affine comparison, the dominance reduction behind the two-flip comparison class and the approximate values $5.182$, $5.185$ and $1.762$ of the upper-12 appendix remain. The radial counterexample of the population-step note was scoped and not taken up, as not worth its cost. Of the seventeen candidates of the twelfth batch, six are in the library so far (from `TimeUniformTwoSided` on). Two further candidates of the tenth batch were not taken up: the 5/3 quantile note follows from the checked factors $8/5$ and $31/20$, and the drafted time-uniform profile statement was wrong as written for negative arguments. The two-update pilot package stays outside the library, as above. The known-law universal constant for general laws is open. | [Record](../results/paper-statements-20261120/README.md), [Lean map](../lean/README.md) |
| Maintenance ([#90](https://github.com/davidiach/adaptive-threshold-estimation/issues/90), [#91](https://github.com/davidiach/adaptive-threshold-estimation/issues/91)) | Parameterize repeated entropy/base-cost and prefix-information/event-transfer arguments; extract shared audit code; simplify redundant premises and unused facts. These are non-blocking. Kernel replay covers the 204 main RMS modules, the twelve controller modules, the 54 `SharpRMS` modules, the 28 `LargeBudgetRMS` modules, the 4 `UpperConstant` modules, the 7 `UpperWork` modules, the 6 `UpperMoment` modules, the 3 `UpperMixture` modules, the 7 `UpperCost` modules, the 9 `UpperDisagreement` modules, the 11 `UpperSign` modules, the 12 `UpperQuarter` modules, the 8 `UpperCallCost` and `UpperScale` modules, the 5 `CriticalWindow` modules, the 4 `PaperCorollaries` modules, the 6 `PaperStatements` modules, the 18 `PilotFeedback` modules, the 2 `ExplicitConstants` modules, the 3 `NonnegativeUnbiased` modules, the 3 modules each of `FiniteGapCorollaries`, `StoppedTimeUniform`, `LatentThreshold`, `ZeroAtomSplit`, `CapIdentificationEstimate`, `BiasSubtraction`, `RestrictedRMS`, `SharpStrict` and `GlobalCut`, the 2 `CriticalPairRMS` modules, the 6 `PsiNull` modules, the 4 `ConfidenceTransferSteps` modules, the 4 `EntropyTailForms` modules, the 5 `NonintervalSelection` modules, the 5 `ProgramFactor` modules, the 6 `FixedPlan` modules, the 5 `OracleSharpness` modules, the 7 `ClippingBoundary` modules, the 7 `OracleUpper` modules, the 3 `ClippedOutput` modules, the 8 `RevisitUpper` modules, the 5 `ObservedHoeffding` modules, the 5 `NestedAssumptions` modules, the 5 `LightContractionConstant` modules, the 8 `BandCostExample` modules, the 8 `RepeatedCheck` modules, the 6 `ReservoirTermination` modules, the 8 `QuantileFactorUpper` modules, the 4 `CreationCharge` modules, the 4 `StagePilotLaw` modules, the 5 `BiasAudit` modules, the 5 `UnknownRarity` modules, the 6 `HardCapNecessity` modules, the 7 `PilotCorrection` modules, the 7 `DepthObstruction` modules, the 6 `LocalizationCounter` modules, the 6 `AffineComparison` modules, the 10 `TwoFlipFeedback` modules, the 9 `UnknownLawConfidence` modules, the 6 `UpperTwelveNumerics` modules, the 9 `RadialUpper` modules, the 4 `TimeUniformTwoSided` modules, the 9 `DepthLegendre` modules, the 4 `LatentDisintegration` modules, the 7 `KnownGapRarity` modules, the 6 `MarginClasses` modules and the 20 `StoppingUpdate` modules; extending it to every module is open. | [Recorded refactoring scope](#pr-10-review-and-maintenance-follow-up), [Lean map](../lean/README.md), [tool index](../tools/README.md) |

CI builds every Lean module and audits the axioms of every constant whenever
a Lean input changes ([record](../results/project-axioms-20261109/README.md)).
It also checks the exported instances and the
[definition lock](../tools/definition_lock.json)
([record](../results/project-definitions-20261114/README.md)).

### Finished areas

| Area | State | Evidence |
|---|---|---|
| General-law rare-event results | All eight frozen entropy-tail targets, including the lower half and two-sided law, are Lean-checked. The universal closed-quantile minimax corollary is also Lean-checked. The direct finite-law bounds with coefficients $10^{-20}$ and 30001 are also Lean-checked. The [explicit general-law theorem](../lean/ThresholdHC/EntropyTailSharp/Full.lean) checks the lower coefficient $10^{-17}$ for both the entropy-tail and quantile functionals. The stopping-program, cap-identification and genie results are also Lean-checked. The [arbitrary-law $\Psi$ lower bound](../results/psi-selection-20261109/README.md) is Lean-checked as a corollary of the explicit entropy-tail bounds, through the comparison $\Psi\le\mathcal K$. | [Manuscript and audit](../paper/rare-event/README.md), [claim scope](RESULTS.md#general-law-rare-event-characterization), [audits](VERIFY.md#entropy-tail-selection-functional) |
| Additional results | The [sublinear power-margin row](../results/sublinear-power-20261105/README.md) has checked two-sided RMS and confidence rates and envelope-uniform upper families. The [logarithmic and intermediate rows](../results/shifted-power-20261105/README.md) are also checked for RMS and hard-cap confidence, including uniformity over the margin class. The [smooth-density theorem](../results/smooth-density-20261105/README.md) is checked for both complexity bounds and unbiased impossibility. The [finite-cell observed-state lower bound](../results/finite-observed-20261105/README.md) is also checked. The [continuous-magnitude lower bounds and regularity](../results/continuous-observed-lower-20261105/README.md) are also checked. The [fresh-state upper-bound transfer](../results/observed-state-upper-20261105/README.md) completes the observed-state rates. The [ordinary stochastic-envelope corollary](../results/stochastic-envelope-20261105/README.md) is Lean-checked for RMS, fixed confidence and unbiased estimation. Lemmas 1–3 and the [full 8/5 comparison](../lean/ThresholdHC/QuantileSelection/Full.lean) are Lean-checked. The [finite-law bandwise-suffix theorem and search bound](../lean/ThresholdHC/BandwiseSuffix/Search.lean) are also Lean-checked. Lean also verifies [total-variation stability, band-preserving rounding and finite approximation](../results/selection-stability-20261104/README.md). The [hard-budget audit](../results/hard-budget-rms-20261104/README.md) verifies the advance statement, all valid observation paths, independent stages, the squared-risk recurrence and the ordinary, critical and general-law minimax bounds. The [quarter-smoothing bound](../results/quarter-smoothing-20261104/README.md) is Lean-checked. The [single-type adaptive KL transfer, stopped experiment and common-pair confidence lower bound](../results/confidence-population-20261104/README.md) are also Lean-checked. The [critical-law confidence lower bound](../results/critical-confidence-20261104/README.md) is now Lean-checked. The [fixed-confidence audit](../results/known-law-confidence-20261104/README.md) verifies the observable capped median and both minimax rates for every known law. The [known-law time-uniform controller, coverage and width](../results/anytime-confidence-20261105/README.md) are also checked. The [selected-type information transfer](../results/adaptive-types-20261105/README.md) is now checked through unbounded stopping. The [common-pair construction and its confidence consequence](../results/common-pair-20261105/README.md) are also Lean-checked. The [fractional-submeasure confidence localization](../results/additive-confidence-20261105/README.md) is also Lean-checked. The [generic RMS and additive obstruction transfers](../results/rms-localization-20261105/README.md) are also checked with coefficient $1/128$. The [direct stopping-program comparison](../results/entropy-confidence-20261105/README.md) also checks the sharper general-law confidence coefficient $10^{-17}$. | [Finite-gap manuscript](../paper/finite-gap-rare-events/README.md), [certified-selection package](../research/2026-10-30-certified-selection/README.md#limitations), [hard-cap scope](RESULTS.md#hard-observation-caps-for-the-rms-rates), [confidence scope](RESULTS.md#confidence-rates-and-sequential-stopping), [results guide](RESULTS.md), [research index](../research/README.md) |
| Arbitrary-law completion | The full controller is Lean-checked: unconditional physical caps, consistent prefixes, nested all-budget coverage and eventual width `2^32 C_* K(B/Lambda)` on one event. The onset is deterministic and uniform over admissible sign laws. The thirty-three component audits cover 1,065 exact statements and 1,063 transitive reports. The [publication record](../results/adaptation-publication-20261116/README.md) reconciles the manuscript, proof evidence and tracker. Numerical enclosures and Python/PRNG execution remain outside the formal theorem. | [Exact scope](ARBITRARY_LAW_FORMALIZATION.md#full-arbitrary-law-all-budget-controller), [proof record](../results/arbitrary-law-controller-20261116/README.md), [current paper](../paper/v6/README.md) |
| Closed form of $\Psi$ | Proposition 14.9, Theorem 14.11, Lemma 14.12 and Theorem 14.13 are Lean-checked in their stated scopes. The uniform power-law proof includes exponent two, arbitrary scale, entropy constants $1/2$ and $3.83$, the deterministic quantile comparison and the unconditional statistical consequences. [#100](https://github.com/davidiach/adaptive-threshold-estimation/issues/100) is complete through #118 (`533fa75`), including the [publication update](../results/power-window-publication-20261116/README.md); Corollary 14.14 and Remark 14.15 are Lean-checked separately, in `CriticalWindow`. | [Critical-window record](../results/critical-window-20261120/README.md), [Sharpness record](../results/psi-sharpness-20261116/README.md), [uniform power-law record](../results/power-window-complete-20261116/README.md), [scope](RESULTS.md#the-variational-modulus-in-closed-form) |

The core arbitrary-law mathematical milestone is complete through
[#114](https://github.com/davidiach/adaptive-threshold-estimation/pull/114),
merged at `39e3587b5a8f4d9466df7762f455ff587a40202e`.
Publication issue [#84](https://github.com/davidiach/adaptive-threshold-estimation/issues/84)
is complete through #115; #118 publishes the additional uniform power-law results. The
[tracker](https://github.com/davidiach/adaptive-threshold-estimation/issues/76)
separates these remaining extensions from the core theorem:

- Numerical specification and stochastic Python/PRNG refinement: #85 and #86.
- The [secondary-claim inventory](SECONDARY_CLAIMS.md) reconciles #89 by
  recording existing checked components and explicit paper-only dispositions.
  The [assembled finite-law approximation theorem](FINITE_SELECTION_APPROXIMATION.md)
  for #93 is merged through #121 (`2e8e8b5`); #119 (`8ca1ddd`) closed #89.
  The [deterministic verification work](DETERMINISTIC_VERIFICATION.md) now
  adds an opt-in kernel checker for actual sqrt/log/entropy outputs and
  [positive finite-law objective/oracle certificates](FINITE_LAW_CERTIFICATES.md).
  The [envelope/transfer certificates](ENVELOPE_TRANSFER_CERTIFICATES.md) add
  residual-zero integration, rounding and conditional transfer. The
  [global selection certificates](GLOBAL_SELECTION_CERTIFICATES.md) add bounded
  complete menus, original-`K` intervals, optimizer and approximation claims.
  Full internal solver transcripts, other selection entry points, concrete
  planners/schedules and floating calculators remain in #85.
  The selected v6 §14.8 targets in #100 are complete; Corollary 14.14 and
  Remark 14.15, first kept paper-only, are Lean-checked since 20 November 2026
  ([record](../results/critical-window-20261120/README.md)). The localization
  theorems keep their single-coin obstruction premise; since 21 November 2026
  Lean proves that premise for every gap law in the form of Proposition
  `prop:psi-null` ([record](../results/psi-null-20261121/README.md)).
- Open research: exact-selection complexity with unrestricted costs (#87)
  and sharp finite-cap convergence (#88).
- Non-blocking proof and verifier maintenance: #90 and #91. A physical
  zero-gap coin from #81 is not used by the completed adaptation construction;
  its unresolved mass is handled by the positive-part split.

The [consolidated v6 manuscript](../paper/v6/README.md) presents all of
these results in one paper; the v5, general-law and finite-gap manuscripts
remain preserved as its sources. When a paper-proof result is formalized,
change its entry in [status.json](../paper/v6/status.json) and its evidence
paths, run `python tools/build_v6.py` and `python tools/build_status_docs.py`,
update the v6 verification section and any per-section status remark, and
rebuild the PDF. The second command regenerates the status sentence in the
[README](../README.md#scope-and-review) and the status table in the
[results guide](RESULTS.md#verification-status).

The original RMS law, critical quadratic law, unbiased existence
characterization, confidence characterization, and canonical magnitude-oracle
lower bounds already have formal results with the scopes recorded in
[RESULTS.md](RESULTS.md). Preserve their specifications and evidence when
extending them. The Python toolkit remains outside the Lean proof.

The additive [lower-bound development](ENTROPY_TAIL_LOWER_PROGRESS.md)
now completes the finite-certificate bound, retained-band packing and joint
rarity allocation, one-sided finite-prefix comparison and vanishing-tail
limit. The canonical lower and two-sided-law theorems inhabit the original
frozen specifications. The [completion record](../results/entropy-tail-complete-20261101/README.md)
records the supporting and eight-target native audits, with reused
dependencies explicitly identified. The proof increments were developed in
[PR #38](https://github.com/davidiach/adaptive-threshold-estimation/pull/38).
The later [explicit comparison](../results/entropy-tail-explicit-20261104/README.md)
verifies the general-law coefficient $10^{-17}$ and the estimator converse.

Finite-law rate computation is now available in the
[rare-event calculator](../toolkit/README.md#3-compute-the-rare-event-rate-for-a-known-finite-law):
$O(n\log n)$ preprocessing and $O(\log n)$ evaluation or target-value
inversion, without subset search. The accompanying
[deterministic paper proof](RARE_EVENT_COMPUTATION.md) strengthens the
comparison to $\mathcal K\le Q\le(5/3)\mathcal K$ for all positive-gap laws.
Lean verifies the stronger [factor $8/5$](../results/quantile-selection-20261104/README.md)
and the [finite-law suffix reduction](../results/bandwise-suffix-20261104/README.md)
from the certified-selection package. The sufficient search family has at most
$\prod_j(n_j+1)$ elements and can grow exponentially with the number of occupied
bands. The Python calculator is unverified. The [known-law estimator](KNOWN_LAW_ESTIMATOR.md)
implements the finite-level race with a certified integration oracle or finite
atom table, an expected flip budget and a per-plan MSE bound. Its performance
proof for this implementation's prices and rounding is on paper. A Lean
variant of the plan, with the level price of the checked upper theorem and
Poisson counts, has a checked certificate and rate, and the estimator its
planner returns is [checked by name](ARBITRARY_LAW_FORMALIZATION.md#the-planners-output-as-a-named-estimator).

The [sharp quantile factor](OPTIMAL_QUANTILE_FACTOR.md) has a Lean-checked unique scalar characterization and finite-law sharpness proof. A separate rational certificate gives a numerical bracket of width $10^{-12}$; its lower end is Lean-checked since 20 November 2026 ([record](../results/paper-statements-20261120/README.md)).
Lean verifies the upper factor [$31/20$](../results/quantile-price-20261104/README.md).
The [unique scalar root and finite-vector optimum](../results/optimal-quantile-root-20261105/README.md) are now Lean-checked. The [entropy Lipschitz bound and finite-core selection reduction](../results/quantile-core-reduction-20261105/README.md) are also checked. The [all-law upper comparison](../results/sharp-quantile-upper-20261105/README.md), including measure normalization, is also checked at the exact scalar-root coefficient. The [finite-law realization and optimality proof](../results/quantile-optimality-20261105/README.md) completes this characterization.

For structured finite laws, [grouping repeated suffix costs](BAND_COST_SELECTION.md)
reduces the search to a polynomial number of states when the number of distinct
positive costs is fixed. The general many-band exact complexity remains open. A new
[paper proof and rational prototype](../research/2026-11-06-selection-approximation/README.md)
give a fully polynomial `(1+epsilon)` approximation without repeated costs.
The [assembled theorem](FINITE_SELECTION_APPROXIMATION.md) now checks the
concrete bins, parameters, all-stage state count, suffix witness and rational
endpoint chain for the original K, with a proved finite precision bound.
The polynomial bit-complexity claim remains paper-only; numerical-oracle and
Python execution remain #85's separate boundary. The new proof record does not
upgrade the earlier component evidence or published PDFs.

For a new contribution, follow [CONTRIBUTING.md](../CONTRIBUTING.md) and
[AGENTS.md](../AGENTS.md). The project owner does not plan human specialist
review; its absence remains a stated limitation, not a pending completion gate.

## Completion ledger

The expandable record retains the earlier status descriptions, working rules,
source checkpoints, and CI outcomes. Read dates and commit identities with each
entry; earlier references to pending work describe that checkpoint.

<details>
<summary>Open the preserved verification and consolidation ledger</summary>

# Verification and consolidation

This ledger records the follow-up authorized on 27 October
2026. The starting published commit is `b3f88e6bc02b3d59ec9fe99529688e2bd911e1db`.
It preserves the full requested scope; a partial formalization does not complete
this plan. The original checkpoint is on `research/verification-consolidation-20261027`.

**Current status (29 October 2026):** the core verification and consolidation
package is complete and merged into `main`, through
[PR #10](https://github.com/davidiach/adaptive-threshold-estimation/pull/10).
The original RMS law and critical quadratic law are proved in Lean in both
directions; the exact Psi comparison, all-size extension, consolidated v5
manuscript, specialist packet, and process note are published.

The next contribution, the unbiased-estimation converse and its `I²/16`
lower bound, is now proved in Lean at `631886e`. All three completion gates
passed: the general two-distribution variance inequality, the information
bound in the existing observable adaptive experiment, and the inverse-moment
limit. The [full theorem](../lean/ThresholdHC/UnbiasedConverse/Full.lean) and
[audit](../results/unbiased_converse_001.json) cover the exact target and all
38 declarations. It was reviewed and merged in
[PR #13](https://github.com/davidiach/adaptive-threshold-estimation/pull/13)
at `d3dc500`, after all six branch/PR checks passed and no blocking findings
remained.

The 713 construction is now realized in the same observable model by
[one law-independent estimator](../lean/ThresholdHC/Observable713/Full.lean),
with uniform extended variance at most `23 I`, actual expected work at most
`31 I`, and product of separate suprema at most `713 I²`. Its second full
target combines the upper construction with the converse to prove unbiased
existence iff the inverse gap is integrable. The
[new audit](../results/observable713_001.json) checks both frozen targets and
all 47 declarations at proof checkpoint `15dbbda`.
The new realization was reviewed and merged in
[PR #14](https://github.com/davidiach/adaptive-threshold-estimation/pull/14)
at `45dde91`, after all six checks passed and no blocking findings remained.

The confidence characterization is now proved in the same observable model
at `d6feb30`: a lower coefficient `1/64`, an upper coefficient `8192`, one
family depending only on budget and failure probability, and explicit
nonvacuity. The model and full targets were frozen at `76e9a8f` before
supporting proofs. All three construction steps are complete: measurable
median amplification, exact execution of independent observable batches,
and the expected-work/radius comparison for every admissible budget.
The [full theorem](../lean/ThresholdHC/Confidence/Full.lean) and
[audit](../results/confidence_001.json) cover 18 modules, all 107 declaration
roots, and four frozen targets. It was reviewed and merged in
[PR #15](https://github.com/davidiach/adaptive-threshold-estimation/pull/15)
at `3aba9ee`, after all six checks passed and no blocking findings remained.

PR #12's toolkit was reviewed, repaired, and merged at `a7ed3b0` after all
10 checks passed on `d1f2191`. All 13 review threads were resolved, covering
numerical integration, binomial tails, invalid inputs, hangs, and overstated
planning claims. Its Python implementation remains outside the Lean proof.

The stronger RMS and confidence lower bounds are now proved for canonical
revealed and adaptively selected magnitudes at `4a5805c`. Their coefficients
are `1/64` and the paper's `15/(256 sqrt(2))`. The selected model has explicit
creation, revisit and stop operations, and a proved fresh-label/persistent-gap
interpretation; the revealed model grants the entire iid magnitude array.
The hidden experiment embeds unchanged. The [full theorems](../lean/ThresholdHC/OracleLower/Full.lean)
and [audit](../results/oracle_lower_001.json) cover eight frozen targets,
10 modules and 54 declarations, including minimax bounds and nonvacuity.
Models and targets were compiled and frozen at `3474a37` before supporting
lower-bound and semantic-embedding proofs. Publication and CI are recorded
on the focused oracle PR; local checks alone do not establish CI success.

The alpha > 2 rare-event RMS theorem is now proved in the same observable model.
The [full package](../lean/ThresholdHC/RareAboveTwo/Full.lean) covers all seven
frozen targets, including a single-coin family that is unbiased on every
power-margin law (second moment at most 28 rho in the proof), a law-independent
upper construction, a supported-law lower bound (coefficient 1/256 in the
proof), exact-power minimax and Psi rates, existence and nonvacuity.
The [scope guide](RARE_ABOVE_TWO.md) explains the proof and its conservative
constants. The [saved audit](../results/rare_above_two_001.json) passed at
`637fb4a`, covering 54 modules, 322 declarations and all seven frozen targets.
Publication and CI are recorded on
[PR #22](https://github.com/davidiach/adaptive-threshold-estimation/pull/22);
local checks alone do not establish CI success.

The 29 October
[finite-gap manuscript](../paper/finite-gap-rare-events/README.md), introduced
in [PR #18](https://github.com/davidiach/adaptive-threshold-estimation/pull/18),
supplies a separate paper-proof closed quantile law for known finite positive-gap
laws, global rarity and uniform expected observation budgets. It is not
Lean-checked or externally specialist-reviewed. General infinite-support
and unknown-law extensions remain outside its scope; this contribution does
not change the formal verification boundary above.

The next formalization priorities are the new general-law rare-event
characterization and stopping-program arguments, the remaining paper-only
rare-event results below two, and auxiliary envelope, smooth-density and observed-state
results. Sharp rare-event confidence rates at and above the quadratic boundary
remain open research.

**Rare-event manuscript update (29 October 2026):** the separate
[general-law manuscript, revised v2](../paper/rare-event/README.md), supplies an
entropy-tail characterization, an attained four-prior stopping dual, and
convergent genie certificates as audited paper proofs. The PDF, sources, exact
finite checks, and audit records are preserved together. Formalizing these new
general claims is follow-up work; finite certificates do not discharge it.
The current [claim scopes](RESULTS.md#general-law-rare-event-characterization)
record the pointwise finite-divergence qualification and sufficient-cap scope.

The project owner does not plan human specialist review. Its absence remains
a stated review limitation, not a pending task or completion gate. The four
maintenance refactorings below are non-blocking follow-up work. Historical
checkpoints and their original evidence scopes are retained below.

The unbiased-estimator review unit is [PR #4](https://github.com/davidiach/adaptive-threshold-estimation/pull/4),
based on that branch at `2162210`. The full critical upper proof is a further
focused unit on `research/critical-minimax-upper-20261028`, based on PR #4's
verified checkpoint `678e81c`. It is published as
[PR #5](https://github.com/davidiach/adaptive-threshold-estimation/pull/5) at
`c127478`. The separate Psi comparison is on
`research/critical-psi-comparison-20261028`, published as
[PR #7](https://github.com/davidiach/adaptive-threshold-estimation/pull/7) at
`eabf274`. The final manuscript and process update is on
`research/manuscript-completion-20261028`, published as
[PR #8](https://github.com/davidiach/adaptive-threshold-estimation/pull/8)
and based on PR #7.

The reviewer follow-up is split into [PR #9](https://github.com/davidiach/adaptive-threshold-estimation/pull/9)
for manuscript clarity and attribution, and
[PR #10](https://github.com/davidiach/adaptive-threshold-estimation/pull/10)
on `research/finite-gap-all-sizes-20261028` for the mathematical extension.
The latter removes the gap-count restriction at coefficient 1/4096, retains
the existing 1/512 large-count theorem, and supplies explicit single-coin
raw-moment and variance constants. It does not claim the same 1/512 constant
for all counts or an explicit final population minimax constant.

### PR #10 review and maintenance follow-up

The merge review repairs standalone v5 assembly and input-graph validation,
tests lock-file registration and dependency-set mutations, and corrects
notation, layout, scope and provenance in the manuscripts and current guides.
The corrected Lean docstring has a fresh audit record; the earlier record
and every target statement remain unchanged.

Four non-blocking refactoring suggestions are deferred to a separate cleanup:
parameterize the duplicated entropy-to-base-cost chain; parameterize the
prefix-information/event-transfer lemmas; extract a shared audit runner;
and remove the redundant scale-count lemma premise and unused intermediate
facts. These changes would reorganize proofs or statements without changing
the proved claims, and are not correctness defects in this PR.

## Current proof boundary

The original distribution-blind upper theorem is now proved against its
unchanged specification: one observable family satisfies the budget and RMS
bound for every gap law. The [full audit](../results/blind_upper_components_002.json)
includes almost-sure execution identities and every budget. The matching
critical rare-event upper is also proved against its frozen specification,
with coefficient 100000 in the original observable experiment. The exact
Psi formula, two-sided rate and counterexample are also proved; see the
[Psi audit](../results/critical_psi_001.json). The manuscript and review packet
now reference checkpoint `eabf274`; both have been rebuilt and visually checked.
Elapsed time and component counts do not establish completion.

The critical upper construction now has calibrated observable classifiers and
an unbiased random-level single-coin estimator under the full global rarity
constraint. Its actual population second moment is at most `28*rho`, and its
expected flip count is at most `112000000*criticalLogFactor(rho)`. Integrability,
population transfer and both bounds are proved; see
[the critical audit](CRITICAL_AUDIT.md#upper-construction-checkpoint).
Fresh-coin aggregation, its exact work/output identities in the original
experiment, and every budget regime are now proved. The unchanged
[full upper specification](../lean/ThresholdHC/CriticalUpper/Specification.lean)
is inhabited by [the final theorem](../lean/ThresholdHC/CriticalUpper/Full.lean).
The explicit comparison with the actual variational Psi objective now also
passes the frozen-target audit. The manuscript, process note and verification
guide now describe these completed proofs and their precise limits. Publication
and CI are tracked per PR; a local proof audit is not a claim that a later
GitHub Actions run has finished.

| Work | Completion evidence | Current state |
|---|---|---|
| Adversarial audit of the critical quadratic theorem | Trace every proof dependency, record objections and their resolution, distinguish paper arguments from kernel checks | [CRITICAL_AUDIT.md](CRITICAL_AUDIT.md) records the source audit, dependency checks, resolved proof obligations and review dependence; the full lower, upper and Psi statements now have separate kernel audits. This is not external specialist review |
| Specialist review package | Short overview, complete consolidated proof, precise questions, source and prior-art references | [Prepared](../paper/critical-review/README.md): four-page brief, two-page all-size addendum and complete proof, 20-page PDF compiled and visually checked; external specialist review is not planned |
| Formal critical argument | Exact statistical specification, proved dependency chain, kernel and axiom audit; scalar lemmas alone do not satisfy this item | The base-cost theorem, common hard pair, unrestricted critical minimax lower bound, and matching upper bound are proved in the original observable experiment for the full rare-prior class. See the [lower audit](../results/critical_components_016.json) and [full upper audit](../results/critical_upper_components_003.json). The [exact Psi formula, rate and minimax separation](../results/critical_psi_001.json) are also proved |
| Original distribution-blind upper bound | One budget-indexed observable algorithm independent of the magnitude/sign laws, realized in the original experiment; uniform work and RMS bounds; exact type and axiom audit | [Complete](BLIND_UPPER.md): the frozen full statement is inhabited by one budget-indexed observable family, with coefficient 512. Actual execution, almost-sure cost/output identities, uniform budget and RMS bounds are proved; exact-type and transitive-axiom audit passed |
| Consolidated v5 manuscript | Original minimax law, unbiasedness, 713 bound, rare-event regimes, critical result and correction to the Psi conjecture; accurate verification labels; compiled and visually checked | [Written](../paper/v5/README.md): 62-page manuscript including the all-size addendum, complete source-derived proof appendices, source checks and rendered-page review. Both critical bounds and Psi are linked at `eabf274`; the addendum's explicit constants are linked at `ebd3667`, the converse at `631886e`, the observable 713 construction at `15dbbda`, confidence at `d6feb30`, and the oracle lower bounds at `4a5805c`. No independent specialist review is claimed |
| General-law rare-event manuscript v2 | Standalone PDF and source identity, exact finite certificate replay, revision audit, and explicit claim status | [Added separately](../paper/rare-event/README.md): 55-page audited paper proof with the two editorial fixes. Existing manuscripts are preserved. `python tools/verify_rare_event_manuscript.py` checks identities and finite evidence; the new general theorems are not Lean-formalized |
| Process note | Reproducible account of construction, frozen statements, semantic review, failed approaches, reviewer dependence, and limits | [Written](process/METHOD.md) and refreshed at `6009662`, including completed realization proofs, the formula's freeze chronology, and lessons from the long run and focused PRs |
| Repository cleanup and publication | Clear current entry points, preserved source/evidence identities, passing relevant guards and CI, pushed commits and reviewable changes | The proof and manuscript stack through PR #10 is merged into main. README, results and verification guides lead to current evidence; historical bundles remain intact. CI results belong to each exact commit and are recorded in the corresponding PR |

## Working rules

* Preserve the existing frozen sources, imported manuscripts and historical
  evidence. Corrections should be conspicuous and must not silently rewrite
  what an earlier audit actually checked.
* Keep current mathematical explanations separate from chronological evidence.
  Reuse this ledger and the audit document rather than producing another package
  for every intermediate attempt.
* Record a failed proof or counterexample before changing course. If a claim
  fails, repair or qualify all current summaries that depend on it.
* A proved implication with a statistical hypothesis is not a proof of that
  hypothesis. Expose pending realization and probability steps explicitly.
* Push checked checkpoints. Do not label a run successful until its actual jobs
  have completed on the corresponding commit.

## Baseline verification

GitHub Actions [run 40488398325](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/40488398325)
completed successfully on the starting main commit. This resolves the reviewers'
earlier observation that its run was still in progress. The new audit does not
turn those regression checks into verification of the critical paper theorem.

The original working tree contains pre-existing untracked research files. Work
here uses a separate Git worktree, leaving that material intact. No history
rewrite is planned to remove wording from old commit messages.

The published probability checkpoint `8e0124f9c2691163f015ceda93d5f01b29604def`
also passed all three Linux jobs in
[run 40494565796](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/40494565796),
including its four scoped critical targets and the existing complete Lean
audits.

The finite-gap extension and updated specialist packet, published at
`071b650d928ba3fd35ff737ab2a455e8225f17e6`, passed all three jobs in
[run 40497825571](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/40497825571),
including the five exact critical targets and all 63 declaration checks.
The later v5 consolidation has separate source, compilation, link, and visual
checks. Its numerical and research jobs passed in
[run 40499796986](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/40499796986),
while the Lean job was cancelled after the subsequent push; that run is not
recorded as a full CI pass. The stopped-suffix checkpoint
`0bbd0ee7164b3b15aa2bda68466e5c0e25a6480f` passed all three jobs in
[run 40501696138](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/40501696138),
including all six exact targets and 84 declaration checks.

The fixed-count restart checkpoint `af25e8827254f8ce9050cca409c7294ede0c64b8`
passed all three jobs in
[run 40504616018](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/40504616018),
including its eight exact targets and 117 declaration checks. The subsequent
sign-test and estimator-entropy checkpoint `65131e6e782afebc6c320ca2b1b0010f4afb2a0d`
also passed all three jobs in
[run 40506853150](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/40506853150),
including its ten exact targets and 135 declaration checks. The population
moment checkpoint `145a78519b58e84a01314da356b380882b644c5b` passed all three jobs in
[run 40510054032](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/40510054032),
including twelve exact targets and 189 declaration checks. The good-gap
checkpoint `13435c1464e449bfc76225ac3d2544e9699e7e4f` passed all three jobs in
[run 40513347586](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/40513347586).
The finite-scale checkpoint `891d5dc4e74d849cc93b100fbf99a28da112ccc3` also
passed all three jobs in
[run 40516081123](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/40516081123),
including seventeen exact targets and 251 declaration checks. Later extensions
require their own CI results. The published base-cost and manuscript correction
checkpoint `5ba7166a6975e1d874e9166d9dbe015b90a5cbc5` passed all three jobs in
[run 40520815549](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/40520815549),
including all twenty exact critical targets and 290 declaration checks.

The capped-transcript checkpoint `b054202c8a1958ca4b79e7021a9270e0e0f6da35`
passed all three jobs in
[run 40527378928](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/40527378928),
including twenty-three exact critical targets and 351 declaration checks.

The population and observation geometry checkpoint `582f0f4491f729db999cb46cef4a372e62364f44`
passed all three jobs in
[run 40532725851](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/40532725851).
The capped-policy risk checkpoint `1910216e77e0a39136dfed27fc5d199fe48d66a8`
also passed all three jobs in
[run 40539447152](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/40539447152).
The common-pair checkpoint `d726b00d4ed552cc03e49a0eaf33cdedbb73ecbb`
passed all three jobs in
[run 40546208702](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/40546208702),
including the full Lean audit and the research and numerical evidence jobs.

The unbiased-estimator checkpoint `678e81c` in PR #4 passed all three Linux
jobs in [run 40667339241](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/40667339241).
The full-upper checkpoint `c127478` in PR #5 also passed all three jobs in
[run 40672110946](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/40672110946).
The Psi and manuscript PRs report their own commit-specific CI results.

</details>
