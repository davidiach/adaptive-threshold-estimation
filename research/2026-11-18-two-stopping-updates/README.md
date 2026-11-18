# Two updates triggered by follow-up answers

At gap 1/5 with 18 pilot flips and seven distinct-label follow-ups, every policy that can replace its schedule at most twice has worst-case RMS **at least 0.186764460**. The fully adaptive witness stays **below 0.186752**. Both bounds use the original population experiment. The two-update theorem covers randomized plans and arbitrary measurable estimates of the seed and full ordered transcript.

The pilot selects the initial schedule. Before each follow-up, the policy can inspect all answers so far and decide whether to replace the remaining schedule. The second trigger and final schedule can also use the prefix where the first trigger occurred. A policy may use zero, one, or both updates. Each position has the same menu as the [one-update experiment](../2026-11-18-stopping-update/README.md).

## Exact calculation

The [rational checker](check.py) minimizes Bayes squared error over schedules, trigger decisions and terminal estimates. It uses sign probabilities 0, 3/10, 7/10 and 1 with respective masses 2/10, 3/10, 3/10 and 2/10. Each entry below rounds the optimal Bayes RMS **down** to twelve decimal places. The exact value is less than one unit in the last place above the entry.

| Available updates | Optimal four-point Bayes RMS, rounded down |
|---:|---:|
| 0 | 0.187358878065 |
| 1 | 0.186844275419 |
| 2 | 0.186764460020 |

At a prefix, continuing follows the current schedule's next action. The two possible answers inherit the **same prescribed suffix** and retain their update budget. Triggering chooses a replacement using the current history and spends one update. The estimator at a leaf is the posterior mean. The four-point optimum supplies a lower bound on worst-case RMS over all sign laws.

## Lean proof

[TwoUpdatePolicy.lean](TwoUpdatePolicy.lean) models the initial, intermediate and final stages and relates the decision at each prefix to the original transcript law. [TwoUpdateBellman.lean](TwoUpdateBellman.lean) stores losses for zero, one and two remaining updates at each ordered schedule. It adds the child losses for a common schedule before taking a minimum over replacements. [TwoUpdateBayes.lean](TwoUpdateBayes.lean) proves this recursion bounds every legal two-trigger policy and estimator.

[TwoUpdateCertificate.lean](TwoUpdateCertificate.lean) checks all 19 pilot head counts in integer arithmetic. It floors terminal mass-weighted losses in units of 10⁻²⁴. The total gives a Bayes MSE lower bound of **34880963526638591801106 / 10²⁴**. [TwoUpdatePopulation.lean](TwoUpdatePopulation.lean) transfers the result through the private seed to worst-case population RMS and proves strict separation.

## Replay

From this directory, with the pinned Lean toolchain and the [compiled project prerequisites](../2026-11-18-scheduled-update/README.md), run

```sh
python check.py
python verify.py /path/to/built/repository --lean /path/to/lean
```

The verifier rebuilds the research dependencies, checks the [public theorem types](AuditTwoUpdates.lean) and their transitive axioms, and replays each new module with `leanchecker`. The numerical certificate accounts for most of the replay time and is checked during compilation and again by `leanchecker`. The [audit record](audit.json) gives compiler and source identities. The existing research CI job checks those source hashes and reruns the exact rational calculation.
