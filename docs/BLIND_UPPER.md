# Distribution-blind minimax upper bound

The original RMS minimax law is now Lean-checked in both directions:

$$\frac1{64}\,\omega_\mu(B^{-1/2})\le R_\mu(B)\le512\,\omega_\mu(B^{-1/2}),\qquad B\ge1.$$

The [upper theorem](../lean/ThresholdHC/BlindUpper/Full.lean),
`distribution_blind_upper`, inhabits the unchanged
[frozen specification](../lean/ThresholdHC/BlindUpper/Specification.lean).
It chooses a single seed space and budget-indexed estimator family before
quantifying over every probability gap law. `minimax_upper_bound` gives the
displayed upper inequality. The [lower theorem](../lean/ThresholdHC/Tier6/Full.lean)
uses the same `minimaxRisk`. Neither coefficient is claimed optimal.

The policy and output observe only the random seed and requested flips. The
seed contains independent geometric levels and uniform marks. It contains no
hidden magnitudes or signs. Expected work counts the actual flips, and extended
squared risk retains infinite values. No classifier-performance, termination,
simulation-identity or integrability premise is added to the final theorem.

## Proof dependencies

| Step | Checked result |
|---|---|
| Original experiment | [OriginalExperiment](../lean/ThresholdHC/ObservableSimulation/OriginalExperiment.lean) identifies the original seed/transcript law with an independent population-tape simulation, including work and squared-risk integrals. |
| Finite calls | [PaddedCall](../lean/ThresholdHC/BlindUpper/PaddedCall.lean) gives a stopped cutoff procedure with observed-prefix cost/output and cost between 1 and `N = 2^L`. |
| Statistical calibration | [CalibrationBundle](../lean/ThresholdHC/BlindUpper/CalibrationBundle.lean) uses two independent first-success pilots and fresh production. [CutoffBatch](../lean/ThresholdHC/BlindUpper/CutoffBatch.lean) proves expected work at most `4N` and MSE at most `12751 ωμ(1/√N)²` under the call-array law. |
| Seed and controller | [SeedInput](../lean/ThresholdHC/BlindUpper/SeedInput.lean) gives exactly that independent call-array law. [BatchMachine](../lean/ThresholdHC/BlindUpper/BatchMachine.lean) implements the procedure as a measurable Tier 6 estimator. |
| Actual execution | [BatchPath](../lean/ThresholdHC/BlindUpper/BatchPath.lean) proves the complete population path is the concatenated call word when both pilots finish. [ActualBatch](../lean/ThresholdHC/BlindUpper/ActualBatch.lean) identifies its actual flips and terminal output. Distinct coin labels justify each fresh call. |
| Probability transfer | [BatchRealization](../lean/ThresholdHC/BlindUpper/BatchRealization.lean) derives almost-sure pilot termination, the work/output identities and the expected-work and squared-risk bounds in the original experiment. |
| Every budget | [BudgetChoice](../lean/ThresholdHC/BlindUpper/BudgetChoice.lean) chooses `N` with `4N ≤ B < 8N` for `B ≥ 4`, and uses a zero-work estimator on the same seed space below 4. [Full](../lean/ThresholdHC/BlindUpper/Full.lean) proves the uniform budget and RMS claims, including small budgets. |

Padding a zero-cost cutoff call with one unused flip preserves its output and
ensures the controller advances its observed history. This changes the
mean-cost factor from 149 to 150 and the MSE constant from 12666 to 12751.
The final coefficient 512 also includes conservative square-root and dyadic
rounding bounds. The frozen specification asks for a universal constant;
its algorithm model and quantifiers are unchanged.

## Verification and remaining scope

The [full audit](../results/blind_upper_components_002.json) records 49 successful
commands: three existing prerequisite builds, 45 registered modules, and the
final exact-type and transitive-axiom audit. All 373 declaration roots are
checked, including qualified execution lemmas. Only `propext`,
`Classical.choice` and `Quot.sound` occur. The verifier checks the frozen
specification hash and all local transitive source hashes before and after
the run. The [earlier construction record](../results/blind_upper_components_001.json)
remains preserved with its original incomplete status.

After the baseline, Tier 6 and critical builds in [VERIFY](VERIFY.md), run:

```sh
python tools/verify_blind_upper_components.py
python -m unittest discover -s tools -p 'test_blind_upper_components.py' -v
```

The confidence-radius characterization and uniform unbiasedness converse
remain paper proofs. The matching critical rare-event upper and the explicit
Psi comparison remain unfinished in Lean. This result does not complete those
separate claims. The synchronized v5 and review packet pin their formal
references to the completed-upper checkpoint `236eb2d`.
