# Distribution-blind upper bound: construction checkpoint

The full upper theorem is **pending**. The completed components provide the
cutoff estimator's statistical bounds, its independent seed and coin-stream
law, and a concrete observable controller in the original Tier 6 algorithm
class. They do not yet prove that controller's uniform risk and budget bounds.

The unchanged [specification](../lean/ThresholdHC/BlindUpper/Specification.lean)
requires one budget-indexed algorithm family chosen before every gap law, with
`UniformBudget` and `maximalRMSRisk` from the existing experiment. Its
[recorded freeze](../tools/blind_upper_specification_freeze.json) preserves the
draft's exact source hash. No proof of that specification is asserted here.

## What is checked

| Component | Exact result and scope |
|---|---|
| Original observable experiment | [OriginalExperiment](../lean/ThresholdHC/ObservableSimulation/OriginalExperiment.lean) identifies the seed/transcript law with an independent population-tape simulation, including expected work and extended squared-risk identities. |
| Finite cutoff call | [PaddedCall](../lean/ThresholdHC/BlindUpper/PaddedCall.lean) supplies a stopped procedure whose cost and output are determined by the observed prefix; its cost lies between 1 and `N = 2^L`. |
| Calibration | [CalibrationBundle](../lean/ThresholdHC/BlindUpper/CalibrationBundle.lean) uses two independent first-success pilots and fresh production calls. With mean call cost `c` and variance `v`, expected total work is `4N-c`, and mean-square error is `vc/N + bias²`. Pilot work includes the successful marked calls. |
| Population and modulus bounds | [CutoffBatch](../lean/ThresholdHC/BlindUpper/CutoffBatch.lean) proves expected work at most `4N` and mean-square error at most `12751 ωμ(1/√N)²` under the actual independent call-array law, for every probability gap law and every measurable sign law. |
| Actual random seed | [SeedInput](../lean/ThresholdHC/BlindUpper/SeedInput.lean) proves that independent geometric levels, uniform marks, and population tapes give exactly the calibrated call-array law. Pair-number coin labels separate the two pilots and production. The seed contains no hidden magnitudes or signs. |
| Observable controller | [BatchMachine](../lean/ThresholdHC/BlindUpper/BatchMachine.lean) defines a measurable `AdaptiveEstimator BatchSeed`. [CallExecution](../lean/ThresholdHC/BlindUpper/CallExecution.lean) proves exact single-call transitions; [ControllerExecution](../lean/ThresholdHC/BlindUpper/ControllerExecution.lean) proves the full controller transition on the concatenated pilot and production words when both pilots terminate. [TerminalOutput](../lean/ThresholdHC/BlindUpper/TerminalOutput.lean) identifies its output at any observed halt. |

The construction pads a zero-cost cutoff call with one unused flip. Its output
stays unchanged. This ensures every call advances the observed history and
changes the mean-cost factor from 149 to 150. Consequently the mean-square
constant is 12751, rather than the paper construction's 12666. The frozen
statement asks for a universal constant; its quantifiers and algorithm model
are unchanged.

## What remains

1. Prove that the controller's path in the original population simulation is
   the concatenated call word, using the distinct labels and the per-call
   stopping proofs. Identify its actual total flips and terminal output with
   the calibrated quantities almost surely. The two pilot termination laws
   are already proved, but this final assembly is pending.
2. Choose the cutoff from the requested budget, handle small budgets, and
   transfer the calibrated mean-square bound to the frozen uniform RMS claim.
3. Complete the separate matching upper bound for the critical rare-event law
   and then synchronize the manuscript's formal references.

The first item is a proof obligation, not an assumption added to the theorem.
The verifier keeps both full-upper flags false and separately marks the
controller/population cost and output identities as pending.

## Reproduce

After the baseline, Tier 6, and critical-component builds listed in
[VERIFY](VERIFY.md), run:

```sh
python tools/verify_blind_upper_components.py
python -m unittest discover -s tools -p 'test_blind_upper_components.py' -v
```

The check rebuilds 35 registered modules and the existing `Tier6.HardPair`
prerequisite, audits all 301 registered declaration roots, rejects proof
escapes and nonstandard transitive axioms, preserves the frozen specification,
and hashes the complete local import closure before and after the audit.
Fresh logs and status go under `.runtime/blind-upper-components/`.
Previously published evidence is not overwritten.

The [first published construction audit](../results/blind_upper_components_001.json)
records the successful rebuild and axiom checks. It explicitly leaves the full
upper theorems and the controller cost/output identities unverified.
