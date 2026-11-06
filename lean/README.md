# Lean proof navigation

Use this map to find a formal statement, its proof, and the audit that checks it.
[Results and scope](../docs/RESULTS.md) explains the mathematical assumptions;
[verification setup](../docs/VERIFY.md#setup) covers Python, Lean, and Mathlib.
Commands below run from the repository root.

## Main theorem entry points

Read a development's `Specification.lean` first, where one exists, then its
final theorem and the imported model/proof modules. The audit checks exact target types and transitive
axioms; a successful build alone is not a substitute for that audit.
The audit does not show that a type means what the paper says; the
[model-fidelity brief](../docs/MODEL_FIDELITY.md) compares the central
definitions with the paper for that review.

| Result | Formal entry point | Audit command |
|---|---|---|
| General RMS lower bound in the observable experiment | [Tier6 specification](ThresholdHC/Tier6/Specification.lean), [Full](ThresholdHC/Tier6/Full.lean) | `python tools/verify_tier6.py --sequential --require-complete` |
| Distribution-blind RMS upper bound | [BlindUpper specification](ThresholdHC/BlindUpper/Specification.lean), [Full](ThresholdHC/BlindUpper/Full.lean) | `python tools/verify_blind_upper_components.py --sequential` |
| Critical quadratic rare-event lower bound | [CriticalEntropy specification](ThresholdHC/CriticalEntropy/Specification.lean), [CriticalMinimax](ThresholdHC/CriticalEntropy/CriticalMinimax.lean) | `python tools/verify_critical_components.py --sequential` |
| Critical quadratic rare-event upper bound | [CriticalUpper specification](ThresholdHC/CriticalUpper/Specification.lean), [Full](ThresholdHC/CriticalUpper/Full.lean) | `python tools/verify_critical_upper_components.py --sequential` |
| Critical Psi formula and counterexample | [CriticalPsi specification](ThresholdHC/CriticalPsi/Specification.lean), [Full](ThresholdHC/CriticalPsi/Full.lean) | `python tools/verify_critical_psi.py --sequential` |
| Entropy at every finite gap count and single-coin base costs | [CriticalAllSizes](ThresholdHC/CriticalAllSizes/) | `python tools/verify_critical_all_sizes.py --sequential` |
| Unbiased-estimation converse | [UnbiasedConverse specification](ThresholdHC/UnbiasedConverse/Specification.lean), [Full](ThresholdHC/UnbiasedConverse/Full.lean) | `python tools/verify_unbiased_converse.py --sequential` |
| Observable 713 construction and unbiased existence characterization | [Observable713 specification](ThresholdHC/Observable713/Specification.lean), [Full](ThresholdHC/Observable713/Full.lean) | `python tools/verify_observable713.py --sequential` |
| Confidence characterization | [Confidence specification](ThresholdHC/Confidence/Specification.lean), [Full](ThresholdHC/Confidence/Full.lean) | `python tools/verify_confidence.py --sequential` |
| Revealed/selected magnitude-oracle lower bounds | [OracleLower specification](ThresholdHC/OracleLower/Specification.lean), [Full](ThresholdHC/OracleLower/Full.lean) | `python tools/verify_oracle_lower.py --sequential` |
| Observable rare-event rate above alpha two | [RareAboveTwo specification](ThresholdHC/RareAboveTwo/Specification.lean), [Full](ThresholdHC/RareAboveTwo/Full.lean), [scope guide](../docs/RARE_ABOVE_TWO.md) | `python tools/verify_rare_above_two.py --sequential` |
| Finite-menu cost grouping and exact certificates | [Dynamic](ThresholdHC/BandCostSelection/Dynamic.lean), [Counting](ThresholdHC/BandCostSelection/Counting.lean), [Entropy](ThresholdHC/BandCostSelection/Entropy.lean), [Comparison](ThresholdHC/BandCostSelection/Comparison.lean), [Certificates](ThresholdHC/BandCostSelection/Certificates.lean) | `python tools/verify_band_cost_selection.py` |
| Concrete finite-law menus and original selection value | [Menus](ThresholdHC/GapLawMenus/Menus.lean), [Entropy and costs](ThresholdHC/GapLawMenus/Costs.lean), [Full solver](ThresholdHC/GapLawMenus/Full.lean), [Atomic formulas](ThresholdHC/GapLawMenus/Atoms.lean) | `python tools/verify_gap_law_menus.py` |
| Finite-law bandwise-suffix optimizer and search bound | [Specification](ThresholdHC/BandwiseSuffix/Specification.lean), [Theorem 5](ThresholdHC/BandwiseSuffix/Full.lean), [Search](ThresholdHC/BandwiseSuffix/Search.lean) | `python tools/verify_bandwise_suffix.py` |
| Selection stability and finite approximation | [Variation](ThresholdHC/SelectionStability/Variation.lean), [Rounding](ThresholdHC/SelectionStability/Rounding.lean), [Enclosures](ThresholdHC/SelectionStability/Approximation.lean), [Finite approximation](ThresholdHC/SelectionStability/FiniteApproximation.lean) | `python tools/verify_selection_stability.py` |
| Confidence transfer, Lemma 1 | [Specification](ThresholdHC/ConfidenceTransfer/Specification.lean), [Quarter smoothing](ThresholdHC/ConfidenceTransfer/Quarter.lean) | `python tools/verify_quarter_smoothing.py` |
| Confidence transfer in the observable population | [Hybrid identity](ThresholdHC/ConfidenceTransfer/Hybrid.lean), [Observable prefixes](ThresholdHC/ConfidenceTransfer/Observable.lean), [Stopped law](ThresholdHC/ConfidenceTransfer/Terminal.lean), [Common-pair rate](ThresholdHC/ConfidenceTransfer/CommonPairRate.lean) | `python tools/verify_confidence_population.py` |
| Hard-cap controller and RMS minimax applications | [Locked statement](ThresholdHC/HardBudget/Specification.lean), [controller](ThresholdHC/HardBudget/Full.lean), [applications and record](../results/hard-budget-rms-20261104/README.md) | `python tools/verify_hard_budget.py` |
| Critical confidence lower bound from the fixed gap law | [Rate](ThresholdHC/ConfidenceTransfer/CriticalRate.lean) | `python tools/verify_critical_confidence.py` |
| Ordinary cap square-root convergence | [Truncation and optimized value](ThresholdHC/FiniteCapTruncation/Full.lean), [risk certificate](ThresholdHC/FiniteCapTruncation/Risk.lean) | `python tools/verify_finite_cap_truncation.py` |
| Uniform finite-cap convergence | [Original program values and risk](ThresholdHC/GenieRate/Full.lean) | `python tools/verify_genie_rate.py` |
| Sharper $31/20$ quantile-selection comparison and $16/9$ separated cost | [Original functional](ThresholdHC/QuantilePrice/Full.lean), [kernel record](../results/quantile-price-20261104/README.md) | `python tools/verify_quantile_price_upper.py` |
| Full $8/5$ quantile-selection comparison, Lemmas 1 and 2, saturation and the tail floor | [Statements](ThresholdHC/QuantileSelection/Specification.lean), [Theorem 4](ThresholdHC/QuantileSelection/Full.lean) | `python tools/verify_quantile_selection.py` |
| Scalar inequality (Lemma 3) of the 8/5 quantile-selection comparison | [QuantileComparison specification](ThresholdHC/QuantileComparison/Specification.lean), [Scalar](ThresholdHC/QuantileComparison/Scalar.lean) | `python tools/verify_quantile_comparison.py --sequential --require-complete` |
| Full entropy-tail law: both halves and five selection-functional properties | [EntropyTail specification](ThresholdHC/EntropyTail/Specification.lean), [Upper](ThresholdHC/EntropyTail/Upper.lean), [Lower](ThresholdHC/EntropyTail/Lower.lean), [Law](ThresholdHC/EntropyTail/Law.lean), [Bridge](ThresholdHC/EntropyTail/Bridge.lean), [HardSelection](ThresholdHC/EntropyTail/HardSelection.lean) | `python tools/verify_entropy_tail.py --sequential --require-complete` |
| Complete finite-certificate lower proof: weighted signs, annular localization, retained-band packing and finite-prefix limit | [EntropyTailLower](ThresholdHC/EntropyTailLower/), [proof map and scope](../docs/ENTROPY_TAIL_LOWER_PROGRESS.md) | `python tools/verify_entropy_tail_lower_components.py` |
| Explicit general-law entropy-tail comparison, $10^{-17}\mathcal K\le R\le28000\mathcal K$ and $10^{-17}Q\le R$ | [Specification](ThresholdHC/EntropyTailSharp/Specification.lean), [Full](ThresholdHC/EntropyTailSharp/Full.lean) | `python tools/verify_entropy_tail_sharp.py` |
| Direct finite-law quantile bounds with constants $10^{-20}$ and 30001 | [Full theorem](ThresholdHC/FiniteQuantile/Full.lean), [estimator and converse](ThresholdHC/FiniteQuantile/Operational.lean) | `python tools/verify_finite_quantile.py` |
| Universal two-sided closed-quantile minimax rate | [ClosedQuantile specification](ThresholdHC/ClosedQuantile/Specification.lean), [Full](ThresholdHC/ClosedQuantile/Full.lean) | `python tools/verify_closed_quantile.py` |
| Observable entropy-tail and closed-quantile upper theorems ($R\le28000\,\mathcal K$, $R\le30001\,Q$), quantile split and $\mathcal K\le Q\le(1+2\sqrt2)\mathcal K$ | [EntropyTailQuantile specification](ThresholdHC/EntropyTailQuantile/Specification.lean), [UpperTheorem](ThresholdHC/EntropyTailExecution/UpperTheorem.lean), [QuantileComparison](ThresholdHC/EntropyTailQuantile/QuantileComparison.lean) | `python tools/verify_entropy_tail_upper.py` |
| Robust stopping program ($R\le P_N$, attained four-prior dual, $R\le P_N\le16R$), fixed-cap identification and genie certificates | [StoppingProgram specification](ThresholdHC/StoppingProgram/Specification.lean), [FiniteCertificate](ThresholdHC/StoppingProgram/FiniteCertificate.lean), [CapIdentification](ThresholdHC/CapIdentification/Full.lean), [Genie](ThresholdHC/Genie/) | [Sixteen audits](../docs/VERIFY.md#stopping-program-identification-and-genie-certificates), e.g. `python tools/verify_finite_risk_certificate.py` |
| Fixed confidence for every known positive-gap law, both budget models | [Upper](ThresholdHC/ConfidenceProgram/Upper.lean), [stopping-program lower bound](ThresholdHC/ConfidenceProgram/Lower.lean), [observable median](ThresholdHC/ConfidenceProgram/Amplify.lean), [record](../results/known-law-confidence-20261104/README.md) | `python tools/verify_stopping_confidence.py`; `python tools/verify_confidence_amplification.py` |
| Envelope minimax rates and unbiased variance and work for unknown laws ordered by their gap CDFs | [Minimax](ThresholdHC/Envelope/Minimax.lean), [Unbiased](ThresholdHC/Envelope/Unbiased.lean), [record](../results/stochastic-envelope-20261105/README.md) | `python tools/verify_stochastic_envelope.py` |
| Sublinear power margins: both rare-event minimax rates and one estimator family across the margin class | [Full](ThresholdHC/SubcriticalPower/Full.lean), [record](../results/sublinear-power-20261105/README.md) | `python tools/verify_sublinear_power.py` |
| Shifted power margins: both remaining rare-event rows, including hard-cap confidence and uniformity over the margin class | [Full](ThresholdHC/ShiftedPower/Full.lean), [record](../results/shifted-power-20261105/README.md) | `python tools/verify_shifted_power.py` |
| Time-uniform confidence: nested observable intervals, a shared purchase history, data-dependent stopping and the known-law iterated-logarithm width | [Full](ThresholdHC/Anytime/Full.lean), [record](../results/anytime-confidence-20261105/README.md) | `python tools/verify_anytime_confidence.py` |
| Smooth-density robustness: both expected-complexity bounds and uniform unbiased impossibility in the original adaptive experiment | [Full](ThresholdHC/SmoothDensity/Full.lean), [proof map](../docs/SMOOTH_DENSITY.md), [record](../results/smooth-density-20261105/README.md) | `python tools/verify_smooth_density.py` |
| Finite-cell observed-state lower bound: a measurable uniform-state partition and the exact testing bound for arbitrary selected-state policies | [Finite](ThresholdHC/ObservedState/Finite.lean), [proof map](../docs/OBSERVED_STATES.md), [record](../results/finite-observed-20261105/README.md) | `python tools/verify_observed_states.py` |
| Continuous-magnitude observed-state complexity and RMS lower bounds in the actual selected-query experiment, with density regularity | [UniformLower](ThresholdHC/ContinuousObserved/UniformLower.lean), [UniformRMSLower](ThresholdHC/ContinuousObserved/UniformRMSLower.lean), [Regularity](ThresholdHC/ContinuousObserved/Regularity.lean), [proof map](../docs/CONTINUOUS_OBSERVED.md), [record](../results/continuous-observed-lower-20261105/README.md) | `python tools/verify_continuous_observed.py` |
| Fresh-state upper bounds transferred to selected-state queries, and uniform-gap rates | [Upper](ThresholdHC/ContinuousObserved/Upper.lean), [UniformUpper](ThresholdHC/ContinuousObserved/UniformUpper.lean), [proof map](../docs/OBSERVED_UPPER.md), [record](../results/observed-state-upper-20261105/README.md) | `python tools/verify_observed_upper.py` |
| Selected-type information transfer, coefficient $16/3$, for the actual randomized countable population through unbounded stopping | [SignTransfer](ThresholdHC/TypedConfidence/SignTransfer.lean), [type labels](ThresholdHC/TypedConfidence/Labels.lean), [proof map](../docs/ADAPTIVE_TYPES.md), [record](../results/adaptive-types-20261105/README.md) | `python tools/verify_typed_confidence.py` |
| Common pair for every capped local policy from a variance–null-work obstruction; estimator and minimax confidence coefficient $1/128$ | [CommonPair](ThresholdHC/ConfidenceLocalization/CommonPair.lean), [ConfidenceRate](ThresholdHC/ConfidenceLocalization/ConfidenceRate.lean), [proof map](../docs/COMMON_PAIRS.md), [record](../results/common-pair-20261105/README.md) | `python tools/verify_confidence_localization.py` |
| Additive confidence localization, coefficient $1/128$, for finite overlapping submeasures with original observation laws and weighted work | [Full](ThresholdHC/AdditiveConfidence/Full.lean), [proof map](../docs/ADDITIVE_CONFIDENCE.md), [record](../results/additive-confidence-20261105/README.md) | `python tools/verify_additive_confidence.py` |
| Sharper general-law confidence: lower coefficient $10^{-17}$ and hard-cap upper coefficient $750000$, through a direct retained-entropy program comparison | [Full](ThresholdHC/ConfidenceEntropy/Full.lean), [Program](ThresholdHC/ConfidenceEntropy/Program.lean), [proof map](../docs/ENTROPY_CONFIDENCE.md), [record](../results/entropy-confidence-20261105/README.md) | `python tools/verify_confidence_entropy.py` |
| Generic RMS transfer and additive submeasure localization, coefficient $1/128$ in the original experiment | [CommonPair](ThresholdHC/RMSLocalization/CommonPair.lean), [Full](ThresholdHC/RMSLocalization/Full.lean), [proof map](../docs/RMS_LOCALIZATION.md), [record](../results/rms-localization-20261105/README.md) | `python tools/verify_rms_localization.py` |
| Sharp quantile factor: the finite-vector factor is equivalent to the unique scalar root for every real factor | [FiniteSharp](ThresholdHC/OptimalQuantile/FiniteSharp.lean), [Root](ThresholdHC/OptimalQuantile/Root.lean), [record](../results/optimal-quantile-root-20261105/README.md) | `python tools/verify_optimal_quantile.py` |
| Finite-core selection reduction at the exact scalar-root factor, and the all-law comparison on the original selection functional | [Lipschitz](ThresholdHC/QuantileSharpLaw/Lipschitz.lean), [CoreReduction](ThresholdHC/QuantileSharpLaw/CoreReduction.lean), [Full](ThresholdHC/QuantileSharpLaw/Full.lean), [reduction record](../results/quantile-core-reduction-20261105/README.md), [comparison record](../results/sharp-quantile-upper-20261105/README.md) | `python tools/verify_quantile_sharp_law.py` |
| Finite-law sharpness and exact optimality: general and finite-support laws have the same least comparison factor | [Full](ThresholdHC/QuantileOptimality/Full.lean), [record](../results/quantile-optimality-20261105/README.md) | `python tools/verify_quantile_optimality.py` |
| All-law time-uniform lower bound: every nonnegative deterministic half-width envelope with joint simultaneous coverage and width control is at least $10^{-22}\mathcal K(n/[\log(1/\delta)+\log\log n])$ at arbitrarily late integer budgets, with no monotonicity assumption, in the original observable experiment. Prior families preserve admissibility and mean separation; every adaptive observable prefix has a quadratic KL bound; first-crossing testing, the infinite-moment tail family with adaptive acquisition, the asymptotic cases and the interval consequence are checked ([research note](../docs/TIME_UNIFORM_LOWER.md), [sequential step](../docs/ANYTIME_SEQUENTIAL.md), [tail family](../docs/ANYTIME_TAIL.md)) | [Full](ThresholdHC/AnytimeLower/Full.lean), [Intervals](ThresholdHC/AnytimeLower/Intervals.lean), [Quartet](ThresholdHC/AnytimeLower/Quartet.lean), [final record](../results/anytime-asymptotic-20261105/README.md), [information record](../results/anytime-lower-20261105/README.md) | `python tools/verify_anytime_asymptotics.py`, `python tools/verify_anytime_sequential.py`, `python tools/verify_anytime_tail.py`, `python tools/verify_anytime_lower.py`; profile regression checks: `python tools/verify_anytime_lower_profiles.py` |

The general-law entropy-tail law (v6 Theorem 13.2) is now Lean-checked
against all eight frozen target types: the two-sided comparison, both halves,
hard selection, elementary bounds, single-atom and small-budget values, and
nonvacuity. The upper half uses the observable EntropyTailQuantile development;
the lower half uses finite certificates and the additive EntropyTailLower
development. The constants are conservative and the original experiment is
unchanged. See the [completion evidence](../results/entropy-tail-complete-20261101/README.md)
for exact audit scope and reused dependencies.
Its stopping-program, fixed-cap identification and genie results are also
proved, in the StoppingProgram, CapIdentification and Genie modules.
The existing critical-law and optimizer formalizations do not certify its
general claims.
See its [separate status](../paper/rare-event/README.md). The two-sided closed
quantile law of the [finite-gap manuscript](../paper/finite-gap-rare-events/README.md)
has a [direct proof with its explicit coefficients](ThresholdHC/FiniteQuantile/Full.lean). The
separate `ClosedQuantile` corollary now proves a two-sided rate for every law
with conservative universal constants; its upper coefficient is 30001.
See its [audit evidence](../results/closed-quantile-law-20261101/README.md).
The [certified-selection package](../research/2026-10-30-certified-selection/README.md)
sharpens its comparison with the selection functional to $\mathcal K\le Q\le\frac85\mathcal K$.
Lemmas 1–3, the comparison and the finite-law bandwise-suffix theorem
are Lean-checked. The suffix optimizer minimizes over all submeasures.

## Foundations and supporting developments

The tier numbers name development milestones. They remain useful dependencies,
not interchangeable versions of the same theorem.

| Area | Role |
|---|---|
| [Statements](ThresholdHC/Statements.lean), [Statements2](ThresholdHC/Statements2.lean), and [Proofs](ThresholdHC/Proofs/) | Original frozen scalar, classifier, information, and rare-event targets and their proofs; checked by `tools/verify_lean_checkpoint.py`. |
| [Tier3](ThresholdHC/Tier3/) | Randomized information bounds, unbounded stopping, and the arbitrary-law variational optimizer. |
| [Tier4](ThresholdHC/Tier4/) | Infinite-transcript KL for a fixed finite coin family. |
| [Tier5](ThresholdHC/Tier5/) | Information/work bounds with unrestricted adaptive coin creation. |
| [Tier6](ThresholdHC/Tier6/) | Observable population realization, risk model, testing reduction, and main RMS lower bound. |
| [Uniform713](ThresholdHC/Uniform713/) | Earlier separate 713 development, with its own frozen specification and audit. |
| [ObservableSimulation](ThresholdHC/ObservableSimulation/) | Shared execution/law identities used to connect constructions to the original observable experiment. |
| [ResearchRouteA](ThresholdHC/ResearchRouteA/) | Locked separate-moment bridge with a limited scope; it does not establish the whole above-two paper result. |

The [kernel-check sequence](../docs/VERIFY.md#lean-kernel-checks) covers the
baseline, Uniform713, and tiers. The [CI workflow](../.github/workflows/checks.yml)
records the complete suite and ordering. `ThresholdHC.lean` is the frozen
original import entry point; use the development-specific specifications and
audits above to navigate later results.

## Making and checking a proof change

Inspect the applicable frozen manifest and specification/dependency lock first.
Even a supporting module may be locked by another result. Follow
[contribution rules](../CONTRIBUTING.md#preserve-reproducibility) for any proposed
change to frozen material.

Use `--sequential` on the audits that accept it when memory is constrained. Baseline,
Uniform713, and tier audits write tracked `results/` files, so reproduce those
in a disposable checkout containing your changes. Every audit added from
4 November onward, for example the bandwise-suffix, hard-budget and
finite-quantile audits, prints its kernel report and writes no evidence files.
The other tabled audits write timestamped directories under `.runtime/`;
[tools/README.md](../tools/README.md) maps those locations.
Run the corresponding verifier regression tests when proof registration or
verification logic changes. Keep published checkpoints intact.

[Finite-family law adaptation](../docs/FINITE_FAMILY_ADAPTATION.md) has 17 checked
components in [Parity](ThresholdHC/LawAdaptation/Parity.lean),
[Identification](ThresholdHC/LawAdaptation/Identification.lean),
[Concentration](ThresholdHC/LawAdaptation/Concentration.lean),
[Pilot](ThresholdHC/LawAdaptation/Pilot.lean),
[Transfer](ThresholdHC/LawAdaptation/Transfer.lean) and
[Rate](ThresholdHC/LawAdaptation/Rate.lean). Run
`python tools/verify_law_adaptation.py`. The full observable construction is now
checked by `python tools/verify_law_adaptation_realization.py` (22 exact statements).
[Moments](ThresholdHC/LawAdaptation/Moments.lean) supplies determinacy and finite
separation; [Observation](ThresholdHC/LawAdaptation/Observation.lean) and
[Execution](ThresholdHC/LawAdaptation/Execution.lean) realize the parity pilot;
[Controller](ThresholdHC/LawAdaptation/Controller.lean),
[Budget](ThresholdHC/LawAdaptation/Budget.lean) and
[Coverage](ThresholdHC/LawAdaptation/Coverage.lean) connect observations, caps and
probability; [Full](ThresholdHC/LawAdaptation/Full.lean) constructs the family
with its joint coverage-and-width guarantee; [Properties](ThresholdHC/LawAdaptation/Properties.lean)
checks nesting and the original-experiment endpoint law.
[Native record](../results/law-adaptation-realization-20261105/README.md).

The [arbitrary-law adaptation formalization](../docs/ARBITRARY_LAW_FORMALIZATION.md)
starts with `ArbitraryLawAdaptation/EntropyTransport.lean` and `BandPenalty.lean`.
Run `python tools/verify_arbitrary_law_entropy.py` for 15 exact statements and
transitive axiom reports. This is finite entropy transport, not the full
arbitrary-law statistical theorem.

`ArbitraryLawAdaptation/CDFEnvelope.lean` constructs the conservative finite
measure, including its zero atom and closed-CDF boundary values. Run
`python tools/verify_arbitrary_law_envelope.py` for 25 exact statements and
24 transitive reports. The statistical pilot event remains unproved in Lean.

`ArbitraryLawAdaptation/LearnedStage.lean` joins a paid pilot to a continuation
chosen from its observed finite envelope. Its cap, fresh labels, chronological
readback and original-experiment joint endpoint law have 17 exact statements
and 16 transitive reports in `python tools/verify_arbitrary_law_stage.py`.
This component does not yet instantiate the statistical pilot or establish
the full all-budget controller.

`ArbitraryLawAdaptation/CountableEntropy.lean`, `CountableTransport.lean` and
`GammaTransport.lean` extend the factor-three bound to countably many cells
and identify its entropy with canonical Gamma. Run
`python tools/verify_arbitrary_law_countable.py` for 16 exact statements and
axiom reports. Individual destination columns are summable; the full moment
and entropy may be infinite. The coupling construction is checked below.

`ArbitraryLawAdaptation/BandGeometry.lean`, `TransportCells.lean` and
`CouplingEntropy.lean` construct the canonical cells of an increasing-gap
coupling and prove its factor-three Gamma comparison. Run
`python tools/verify_arbitrary_law_coupling.py` for 19 exact statements and
axiom reports. `SelectionLift.lean` and `IncreasingSelection.lean` transport
all fractional selections and prove `K(new) <= sqrt(3) K(old)`. Run
`python tools/verify_arbitrary_law_selection.py` for 13 exact statements and
reports. These are positive-gap results under a supplied coupling; the
following modules construct it and include unresolved mass at zero.

`ArbitraryLawAdaptation/CDFCoupling.lean` constructs a common-uniform coupling
from CDF domination, including atoms at zero. Run
`python tools/verify_arbitrary_law_cdf_coupling.py` for 11 exact statements and
reports. `ZeroModel.lean`, `ZeroCoupling.lean`, `ZeroSelection.lean` and
`CDFSelection.lean` extend the functional to `[0,1/2]`, prove exact agreement
with positive-gap K, and derive `K(new) <= sqrt(3) K(old)` from CDF domination.
Run `python tools/verify_arbitrary_law_zero.py` for 36 exact statements and
reports. The light random contraction and statistical composition remain.

The dominated-mass comparison (A5) is checked by
`python tools/verify_arbitrary_law_dominated.py`: 22 exact statements and
22 transitive reports. Bounded density restriction transfers fractional
selections and controls their residuals. For finite measures,
`lambda <= c eta + e delta_0` gives `K(lambda) <= c K(eta) + e`
when `c >= 1` and `e >= 0`, retaining infinite entropy and the cap.

Run `python tools/verify_arbitrary_law_light_entropy.py` for 36 exact statements
and transitive reports: product-reference entropy, explicit numerical budgets,
two-band product geometry and the factor-1024 entropy bound for actual product
measure cells. Run `python tools/verify_arbitrary_law_light.py` for 26 more
exact statements and transitive reports: residual tails, the constructed
multiplier's exact CDF, and the full capped selection comparison with factor 32.
The final result imposes no inverse-moment or entropy condition on the input law.
