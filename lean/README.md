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

The new general-law rare-event manuscript remains a paper proof; the existing
critical-law and optimizer formalizations do not certify its general claims.
See its [separate status](../paper/rare-event/README.md). The closed quantile law
of the [finite-gap manuscript](../paper/finite-gap-rare-events/README.md) is also a
paper proof; the Lean finite-gap entropy results above do not verify it.

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
