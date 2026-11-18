# Guides

This folder holds the project's written guides. Four pages are entry points.
The rest are notes on one result each, guides to the toolkit's output
certificates, and historical records. The
[repository map](../README.md#repository-map) describes the other folders.

## Start here

| Page | Use it to |
|---|---|
| [RESULTS.md](RESULTS.md) | Find any claim with its exact assumptions, its verification status and its evidence |
| [VERIFY.md](VERIFY.md) | Reproduce a check; the [task table](VERIFY.md#choose-checks-by-task) picks the commands |
| [WORKPLAN.md](WORKPLAN.md) | See what is open and what is finished |
| [MODEL_FIDELITY.md](MODEL_FIDELITY.md) | Compare the paper's model with the Lean definitions; written for a specialist reviewer |

## Notes on individual results

Each note states one result, its scope and how it was checked.
[RESULTS.md](RESULTS.md) links to most of them from the matching section.

### The main law, for every sign law

| Page | Subject |
|---|---|
| [RESULTS.md, minimax law](RESULTS.md#minimax-law-and-unbiasedness) | The sharp lower constant $1/6$ and the constants for large budgets. They have no separate note. Appendix AA of the paper proves $1/6$ and $\sqrt{59/2100}$; the bracket for $B\ge25$ is written up only in the [research package](../research/2026-11-17-rms-constants/README.md#the-coefficient-for-budgets-of-at-least-25) |
| [BLIND_UPPER.md](BLIND_UPPER.md) | The distribution-blind minimax upper bound |
| [SMOOTH_DENSITY.md](SMOOTH_DENSITY.md) | The smooth-density theorem |
| [OBSERVED_STATES.md](OBSERVED_STATES.md) | Observed-state lower bounds for finitely many cells |
| [CONTINUOUS_OBSERVED.md](CONTINUOUS_OBSERVED.md) | Observed-state lower bounds for continuous magnitudes |
| [OBSERVED_UPPER.md](OBSERVED_UPPER.md) | Transfer of the upper bound to fresh outer states |

### Rare events with a known gap law

| Page | Subject |
|---|---|
| [RARE_ABOVE_TWO.md](RARE_ABOVE_TWO.md) | Power-law gaps above the inverse-square boundary |
| [CRITICAL_AUDIT.md](CRITICAL_AUDIT.md) | The critical quadratic theorem: its current formal boundary, then the record of the follow-up audit |
| [FINITE_SELECTION_APPROXIMATION.md](FINITE_SELECTION_APPROXIMATION.md) | Finite-law relative approximation, certified original-K endpoints and the execution boundary |
| [RARE_EVENT_COMPUTATION.md](RARE_EVENT_COMPUTATION.md) | Computing the rare-event rate, and a tighter selection comparison |
| [QUANTILE_PRICE_BOUNDS.md](QUANTILE_PRICE_BOUNDS.md) | Sharper bounds on the quantile-to-selection factor |
| [OPTIMAL_QUANTILE_FACTOR.md](OPTIMAL_QUANTILE_FACTOR.md) | The optimal universal quantile-to-selection factor |
| [BAND_COST_SELECTION.md](BAND_COST_SELECTION.md) | Finite-law selection with repeated band costs |
| [FINITE_CAP_RATE.md](FINITE_CAP_RATE.md) | A convergence rate for the optimized stopping programs |

### Confidence and lower-bound transfers

| Page | Subject |
|---|---|
| [STOPPING_CONFIDENCE.md](STOPPING_CONFIDENCE.md) | A confidence lower bound from the stopping-program dual |
| [ENTROPY_CONFIDENCE.md](ENTROPY_CONFIDENCE.md) | The sharper general-law confidence coefficient |
| [ADAPTIVE_TYPES.md](ADAPTIVE_TYPES.md) | Information transfer for adaptively selected types |
| [COMMON_PAIRS.md](COMMON_PAIRS.md) | Common pairs from a variance–null-work obstruction |
| [ADDITIVE_CONFIDENCE.md](ADDITIVE_CONFIDENCE.md) | Confidence localization over fractional submeasures |
| [RMS_LOCALIZATION.md](RMS_LOCALIZATION.md) | RMS obstruction transfer and additive localization |

### Time-uniform confidence

| Page | Subject |
|---|---|
| [ANYTIME_SEQUENTIAL.md](ANYTIME_SEQUENTIAL.md) | Sequential testing in the observable experiment |
| [ANYTIME_TAIL.md](ANYTIME_TAIL.md) | Infinite-moment tail families |
| [TIME_UNIFORM_LOWER.md](TIME_UNIFORM_LOWER.md) | Time-uniform lower bounds that depend on the gap law |

### Unknown gap law

| Page | Subject |
|---|---|
| [UNKNOWN_LAW_CONFIDENCE.md](UNKNOWN_LAW_CONFIDENCE.md) | Confidence intervals from flips alone when the gap law is unknown |
| [FINITE_FAMILY_ADAPTATION.md](FINITE_FAMILY_ADAPTATION.md) | Oracle-rate adaptation over a supplied finite family of gap laws |
| [ARBITRARY_LAW_ADAPTATION.md](ARBITRARY_LAW_ADAPTATION.md) | Eventual oracle-rate adaptation for arbitrary gap laws: the paper proof of the Lean-checked theorem |
| [ARBITRARY_LAW_TAIL.md](ARBITRARY_LAW_TAIL.md) | Tail certificates at the oracle scale, one part of that proof |
| [ARBITRARY_LAW_FORMALIZATION.md](ARBITRARY_LAW_FORMALIZATION.md) | The Lean proof of that theorem: its components, the full controller and what stays outside it |

### Toolkit and experiments

| Page | Subject |
|---|---|
| [KNOWN_LAW_ESTIMATOR.md](KNOWN_LAW_ESTIMATOR.md) | Running the known-law rare-event estimator |
| [BUDGET_CONTROLLER_TRANSITIONS.md](BUDGET_CONTROLLER_TRANSITIONS.md) | Execution contracts of the Python budget controllers, followed by their audit of 6 November |
| [EXPERIMENT_PERSISTENCE.md](EXPERIMENT_PERSISTENCE.md) | How the benchmark runs are stored and recovered, followed by the persistence audit of 6 November |

### Toolkit output certificates

These guides belong to
[#85](https://github.com/davidiach/adaptive-threshold-estimation/issues/85):
the Lean kernel checks individual outputs of the Python toolkit. The Python
code itself is not verified.

| Page | Subject |
|---|---|
| [DETERMINISTIC_VERIFICATION.md](DETERMINISTIC_VERIFICATION.md) | Start here: the inventory of deterministic toolkit functions, the numerical certificate checker and what remains outside it |
| [FINITE_LAW_CERTIFICATES.md](FINITE_LAW_CERTIFICATES.md) | Finite laws as original measures, and certificates for objective and oracle outputs |
| [ENVELOPE_TRANSFER_CERTIFICATES.md](ENVELOPE_TRANSFER_CERTIFICATES.md) | Zero-residual envelopes, rounding pushforwards and conditional transfer outputs |
| [GLOBAL_SELECTION_CERTIFICATES.md](GLOBAL_SELECTION_CERTIFICATES.md) | Bounded complete menus, global solver intervals, exact-optimality claims and relative approximation |

## Historical records

These pages describe their own checkpoints and are kept as written. Use the
pages above for the current state.

| Page | Subject |
|---|---|
| [TIER4.md](TIER4.md), [TIER5.md](TIER5.md), [TIER6.md](TIER6.md) | Run notes for three stages of the main lower-bound formalization |
| [ENTROPY_TAIL_LOWER_PROGRESS.md](ENTROPY_TAIL_LOWER_PROGRESS.md) | Progress record of the entropy–tail lower-bound formalization |
| [SECONDARY_CLAIMS.md](SECONDARY_CLAIMS.md) | The disposition of the paper's secondary claims as of 16 November 2026, kept byte for byte because a [record](../results/secondary-claims-20261116/README.md) pins it. The approximation theorem it names as the next step is since Lean-checked: see [FINITE_SELECTION_APPROXIMATION.md](FINITE_SELECTION_APPROXIMATION.md) |
| [process/](process/README.md) | The process record: method, provenance, reports and run logs |
