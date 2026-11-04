# Lean proof navigation

Use this map to find a formal statement, its proof, and the audit that checks it.
[Results and scope](../docs/RESULTS.md) explains the mathematical assumptions;
[verification setup](../docs/VERIFY.md#setup) covers Python, Lean, and Mathlib.
Commands below run from the repository root.

## Main theorem entry points

Read a development's `Specification.lean` first, then its final theorem and the
imported model/proof modules. The audit checks exact target types and transitive
axioms; a successful build alone is not a substitute for that audit.

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
| Finite-law bandwise-suffix optimizer and search bound | [Specification](ThresholdHC/BandwiseSuffix/Specification.lean), [Theorem 5](ThresholdHC/BandwiseSuffix/Full.lean), [Search](ThresholdHC/BandwiseSuffix/Search.lean) | `python tools/verify_bandwise_suffix.py` |
| Selection stability and finite approximation | [Variation](ThresholdHC/SelectionStability/Variation.lean), [Rounding](ThresholdHC/SelectionStability/Rounding.lean), [Enclosures](ThresholdHC/SelectionStability/Approximation.lean), [Finite approximation](ThresholdHC/SelectionStability/FiniteApproximation.lean) | `python tools/verify_selection_stability.py` |
| Confidence transfer, Lemma 1 | [Specification](ThresholdHC/ConfidenceTransfer/Specification.lean), [Quarter smoothing](ThresholdHC/ConfidenceTransfer/Quarter.lean) | `python tools/verify_quarter_smoothing.py` |
| Confidence transfer in the observable population | [Hybrid identity](ThresholdHC/ConfidenceTransfer/Hybrid.lean), [Observable prefixes](ThresholdHC/ConfidenceTransfer/Observable.lean), [Stopped law](ThresholdHC/ConfidenceTransfer/Terminal.lean), [Common-pair rate](ThresholdHC/ConfidenceTransfer/CommonPairRate.lean) | `python tools/verify_confidence_population.py` |
| Hard-cap controller and RMS minimax applications | [Locked statement](ThresholdHC/HardBudget/Specification.lean), [controller](ThresholdHC/HardBudget/Full.lean), [applications and record](../results/hard-budget-rms-20261104/README.md) | `python tools/verify_hard_budget.py` |
| Critical confidence lower bound from the fixed gap law | [Rate](ThresholdHC/ConfidenceTransfer/CriticalRate.lean) | `python tools/verify_critical_confidence.py` |
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

Use `--sequential` on the listed audits when memory is constrained. Baseline,
Uniform713, and tier audits write tracked `results/` files, so reproduce those
in a disposable checkout containing your changes. The other tabled audits write
under `.runtime/`; [tools/README.md](../tools/README.md) maps the output locations.
Run the corresponding verifier regression tests when proof registration or
verification logic changes. Keep published checkpoints intact.

The [fixed-confidence theorem](ThresholdHC/ConfidenceProgram/Upper.lean)
bounds both budget models for every known positive-gap law. It uses the
[stopping-program lower bound](ThresholdHC/ConfidenceProgram/Lower.lean)
and the [observable median](ThresholdHC/ConfidenceProgram/Amplify.lean).
[Exact statements and native record](../results/known-law-confidence-20261104/README.md)
