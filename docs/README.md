# Guides

This folder holds the project's written guides. Four pages are entry points;
the rest are notes on one result each. The [repository map](../README.md#repository-map)
describes the other folders.

## Start here

| Page | Use it to |
|---|---|
| [RESULTS.md](RESULTS.md) | Find any claim with its exact assumptions, its verification status and its evidence |
| [VERIFY.md](VERIFY.md) | Reproduce a check; the [task table](VERIFY.md#choose-checks-by-task) picks the commands |
| [WORKPLAN.md](WORKPLAN.md) | See the current priorities and what is finished |
| [MODEL_FIDELITY.md](MODEL_FIDELITY.md) | Compare the paper's model with the Lean definitions; written for a specialist reviewer |

## Notes on individual results

Each note states one result, its scope and how it was checked.
[RESULTS.md](RESULTS.md) links to them from the matching section.

### The main law, for every sign law

| Page | Subject |
|---|---|
| [BLIND_UPPER.md](BLIND_UPPER.md) | The distribution-blind minimax upper bound |
| [SMOOTH_DENSITY.md](SMOOTH_DENSITY.md) | The smooth-density theorem |
| [OBSERVED_STATES.md](OBSERVED_STATES.md) | Observed-state lower bounds for finitely many cells |
| [CONTINUOUS_OBSERVED.md](CONTINUOUS_OBSERVED.md) | Observed-state lower bounds for continuous magnitudes |
| [OBSERVED_UPPER.md](OBSERVED_UPPER.md) | Transfer of the upper bound to fresh outer states |

### Rare events with a known gap law

| Page | Subject |
|---|---|
| [RARE_ABOVE_TWO.md](RARE_ABOVE_TWO.md) | Power-law gaps above the inverse-square boundary |
| [CRITICAL_AUDIT.md](CRITICAL_AUDIT.md) | The critical quadratic theorem and its follow-up audit |
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
| [ARBITRARY_LAW_ADAPTATION.md](ARBITRARY_LAW_ADAPTATION.md) | The paper proof of eventual oracle-rate adaptation for arbitrary gap laws |
| [ARBITRARY_LAW_TAIL.md](ARBITRARY_LAW_TAIL.md) | Tail certificates at the oracle scale, one part of that proof |
| [ARBITRARY_LAW_FORMALIZATION.md](ARBITRARY_LAW_FORMALIZATION.md) | Which components of that proof are Lean-checked, and what remains |

### Toolkit and experiments

| Page | Subject |
|---|---|
| [KNOWN_LAW_ESTIMATOR.md](KNOWN_LAW_ESTIMATOR.md) | Running the known-law rare-event estimator |
| [BUDGET_CONTROLLER_TRANSITIONS.md](BUDGET_CONTROLLER_TRANSITIONS.md) | Execution contracts of the Python budget controllers, and their audit |
| [EXPERIMENT_PERSISTENCE.md](EXPERIMENT_PERSISTENCE.md) | Persistence audit of the benchmark runs |

## Historical records

These pages describe their own checkpoints and are kept as written. Use the
pages above for the current state.

| Page | Subject |
|---|---|
| [TIER4.md](TIER4.md), [TIER5.md](TIER5.md), [TIER6.md](TIER6.md) | Run notes for three stages of the main lower-bound formalization |
| [ENTROPY_TAIL_LOWER_PROGRESS.md](ENTROPY_TAIL_LOWER_PROGRESS.md) | Progress record of the entropy–tail lower-bound formalization |
| [process/](process/README.md) | The process record: method, provenance, reports and run logs |
