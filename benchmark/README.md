# Direct-real threshold benchmark

This experimental method uses the original Giles–Haji-Ali observation generator,
real-valued sample means and sample variances, geometric randomization across
dyadic classifier caps, and independent two-success cost calibration. The final
output alone is clipped to [0,1]. The estimator does not receive the true target,
latent conditional mean, or latent sign.

`reference.py`, `data/training.json`, and `data/tuning.json` are byte-for-byte
copies of the original next-phase package's benchmark code and offline results.
The package is also preserved at `../inputs/next-phase/`. The old held-out files
were not consulted during development or selection. GHA is rerun with its original
held-out seeds and allocations, using the environment recorded in the lock file.

Four design rounds used tuning data only: single-term prefix coupling; antithetic
coarse blocks; randomized sums of coupled increments; and the average of four
independent calibrated randomized sums. Every tested cell is retained in
`results/real_tuning.json`, including unsuccessful designs. The final choice at
each budget minimizes clipped tuning RMSE. All cells use 100 tuning repetitions;
selection over many cells is optimistic and the held-out test is the assessment.

The sample-variance stopping boundary is a heuristic for this unbounded model.
No concentration guarantee, universal error rate, or improved analytic constant
is asserted. Two-success calibration controls expected work; it is not a hard cap.
Offline fitting and tuning costs must be reported separately. A constant zero
has RMSE 0.025 on this model.

## Reproduction

Use Python 3.12 and `python -m pip install -r benchmark/requirements.txt`.
On this workspace the runner also recognizes dependencies in `.runtime/python`.
Run commands from the repository root:

```
python benchmark/verify_real.py
python benchmark/verify_production.py
python benchmark/run_real.py train --n 2000
python benchmark/run_real.py tune --n 100
python benchmark/run_real.py lock
python benchmark/run_real.py test
```

Run the complete workflow in a fresh output copy: the checked-in lock prevents
further training/tuning, and the test-start marker prevents repeating the held-out
test. For independent reproduction, copy the source and original input data into
a new directory with an empty `results/`. Do not remove the experiment's lock or
test-start marker. The same final configuration set can be reproduced in one
training/tuning invocation; prior tuning snapshots document the actual rounds.

`verify_real.py`, part of the locked selection, compares tape copies of the
compiled coupling state machines against independent scalar finite-tape
classifiers, checks exact randomized telescoping, and checks that four-repeat
outputs/costs match four separately seeded production calls.
`verify_production.py`, added after the held-out test, replays the exact seeded
draws of the production routines themselves (`real_pair`, `antithetic_pair`,
`sum_term`, `real_term`, `real_estimate`, `real_replicates`) and compares every
value and cost with an independent scalar classifier, including the selected
configurations. These are implementation checks, not proofs of statistical
performance.

Seeds: training uses 12000+configuration index; tuning uses families 32000,
33000, 34000 and 35000 with the original budget index and recorded candidate
offset. Held-out uses the original formula 41000+100*budget_index+method_index,
with GHA index 1 and the new method index 4. Bootstrap intervals use 3000 resamples
from independent seeds 51000+100*budget_index+method_index; they are descriptive.
