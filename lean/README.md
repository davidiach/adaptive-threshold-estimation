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
| Canonical entropy-tail selection properties | [Frozen specification](ThresholdHC/EntropyTail/Specification.lean), [HardSelection](ThresholdHC/EntropyTail/HardSelection.lean) | `python tools/verify_entropy_tail.py --sequential` |
| Both entropy-tail interfaces, stopping and genie results | [Compatibility](ThresholdHC/EntropyTailBridge/Compatibility.lean), [canonical upper](ThresholdHC/EntropyTailBridge/Upper.lean) | `python tools/verify_rare_event_completion.py --jobs 2` |
| Arbitrary-law entropy-tail and closed-quantile upper bounds | [EntropyTail specification](ThresholdHC/EntropyTailQuantile/Specification.lean), [UpperTheorem](ThresholdHC/EntropyTailExecution/UpperTheorem.lean), [scope guide](../docs/ENTROPY_TAIL_FORMALIZATION.md) | `python tools/verify_entropy_tail_upper.py` |
| Arbitrary-law deterministic quantile comparison | [QuantileComparison](ThresholdHC/EntropyTailQuantile/QuantileComparison.lean), [published audit](../results/entropy-tail-quantile-20261030/README.md) | `python tools/verify_entropy_tail_components.py` |
| Fixed-cap identification and infinite-budget floor | [CapIdentification Full](ThresholdHC/CapIdentification/Full.lean), [checkpoint scope](../results/cap-identification-20261030/README.md) | `python tools/verify_stopping_components.py` |
| Infinite-divergence counterexample | [InfiniteDivergenceExample](ThresholdHC/Genie/InfiniteDivergenceExample.lean), [checkpoint scope](../results/genie-counterexample-20261030/README.md) | `python tools/verify_genie_counterexample.py` |
| Direct risk and finite genie SOCP | [DirectRisk](ThresholdHC/Genie/DirectRisk.lean), [AtomConicRealization](ThresholdHC/Genie/AtomConicRealization.lean), [checkpoint scope](../results/genie-conic-20261030/README.md) | `python tools/verify_genie_conic.py` |
| Posterior information and convergent genie certificates | [RevealConvergence](ThresholdHC/Genie/RevealConvergence.lean), [OptimizedConvergence](ThresholdHC/Genie/OptimizedConvergence.lean), [checkpoint scope](../results/genie-convergence-20261030/README.md) | `python tools/verify_genie_convergence.py` |
| Monotone genie brackets and Bellman certificates | [RevealTruncation](ThresholdHC/Genie/RevealTruncation.lean), [RevealBellman](ThresholdHC/Genie/RevealBellman.lean), [RevealResidual](ThresholdHC/Genie/RevealResidual.lean), [checkpoint scope](../results/genie-brackets-20261030/README.md) | `python tools/verify_genie_brackets.py` |
| Exact attained infinite-cap dual | [InfiniteDuality](ThresholdHC/Genie/InfiniteDuality.lean), [InfiniteMidpoint](ThresholdHC/Genie/InfiniteMidpoint.lean), [checkpoint scope](../results/infinite-cap-dual-20261030/README.md) | `python tools/verify_infinite_cap_dual.py` |
| Exact factor-sixteen finite certificate | [FiniteCertificate](ThresholdHC/StoppingProgram/FiniteCertificate.lean), [checkpoint scope](../results/finite-risk-certificate-20261030/README.md) | `python tools/verify_finite_risk_certificate.py` |
| Adaptive information and finite-prefix risk | [PrefixModulus](ThresholdHC/StoppingProgram/PrefixModulus.lean), [checkpoint scope](../results/adaptive-information-20261030/README.md) | `python tools/verify_adaptive_information.py` |
| Ordered stopping and local information | [OrderedInformationBound](ThresholdHC/StoppingProgram/OrderedInformationBound.lean), [checkpoint scope](../results/ordered-information-20261030/README.md) | `python tools/verify_ordered_information.py` |
| Actual information-ratio Bellman characterization | [BellmanTheorem](ThresholdHC/StoppingProgram/BellmanTheorem.lean), [checkpoint scope](../results/information-bellman-20261030/README.md) | `python tools/verify_information_bellman.py` |
| Reference absorption and midpoint modulus | [MidpointComparison](ThresholdHC/StoppingProgram/MidpointComparison.lean), [checkpoint scope](../results/reference-absorption-20261030/README.md) | `python tools/verify_reference_absorption.py` |
| Observable stopping-program upper bound | [ProgramUpper](ThresholdHC/StoppingProgram/ProgramUpper.lean), [CertificateRealization](ThresholdHC/StoppingProgram/CertificateRealization.lean), [checkpoint scope](../results/stopping-program-upper-20261030/README.md) | `python tools/verify_stopping_program_upper.py` |
| Finite flow mixtures and observable calls | [FlowMixture](ThresholdHC/StoppingProgram/FlowMixture.lean), [TableCall](ThresholdHC/StoppingProgram/TableCall.lean), [checkpoint scope](../results/stopping-flow-mixture-20261030/README.md) | `python tools/verify_stopping_flow_mixture.py` |
| Exact finite-law stopping program | [FiniteProgram](ThresholdHC/StoppingProgram/FiniteProgram.lean), [checkpoint scope](../results/finite-stopping-program-20261030/README.md) | `python tools/verify_finite_stopping_program.py` |
| Rarity support and fractional cutoff | [RarityTheorem](ThresholdHC/StoppingProgram/RarityTheorem.lean), [checkpoint scope](../results/rarity-support-20261030/README.md) | `python tools/verify_rarity_support.py` |
| Attained four-prior stopping dual | [StoppingProgram specification](ThresholdHC/StoppingProgram/Specification.lean), [DualTheorem](ThresholdHC/StoppingProgram/DualTheorem.lean), [checkpoint scope](../results/stopping-dual-20261030/README.md) | `python tools/verify_stopping_dual.py` |

The [combined full audit](../results/rare-event-full-20261031/README.md)
checks the current integrated proof sources, both frozen interfaces and
the canonical upper target: 518 rebuilt dependencies, 111 exact types and
1,789 declarations, with only the three standard axioms.

The arbitrary-law entropy-tail upper bound and closed-quantile upper formula
now have a [full local audit](../results/entropy-tail-upper-20261030/README.md).
The matching statistical lower bound remains separate work, so this does not
yet verify the two-sided minimax characterization. The stopping-program and
identification development has its own [current scope](../docs/ENTROPY_TAIL_FORMALIZATION.md#stopping-and-identification-ingredients).
Preserved manuscript verification sections describe their earlier checkpoints.

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
