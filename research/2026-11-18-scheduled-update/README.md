# One scheduled update after the pilot

At gap 1/5 and budget 25, every policy in the pilot's distinct-label follow-up menu with one scheduled update has worst-case RMS risk at least **0.186960371**. The existing adaptive policy has worst-case RMS below **0.186752**. Both risks use the original population experiment and take the supremum over sign laws.

After 18 fresh flips, the policy reads the full ordered pilot and chooses a split `k ∈ {0,…,7}` and the first `k` follow-up actions. After those answers arrive, it can use the entire ordered history to choose the remaining `7−k` actions. The split is fixed before the first follow-up answer. Both empty batches are allowed. The theorem covers randomized plans and any measurable real-valued estimate of the full tape and seed. Within the menu, each follow-up position can request its designated head label, tail label, or a fresh label. An unavailable revisit falls back to a fresh label. Choosing the update time in response to follow-up answers would define a larger policy class.

## Proof

- [ScheduledPolicy.lean](ScheduledPolicy.lean) defines the plan and proves its binary recursion computes expectations under the original ordered-transcript law.
- [ScheduledBounds.lean](ScheduledBounds.lean) and [ScheduledCertificate.lean](ScheduledCertificate.lean) certify the integer minima for every feasible first batch, each split and each pilot head count. The second-batch minimum is taken separately **inside** the sum over first-batch answers. The pilot head count indexes a common bound for all orders, even when the plan chooses different actions on different pilot orders.
- [ScheduledBayes.lean](ScheduledBayes.lean) proves the four-point Bayes bound for arbitrary terminal estimates. The sign probabilities are 0, 3/10, 7/10 and 1 with masses 2/10, 3/10, 3/10 and 2/10.
- [FixedHorizonRisk.lean](FixedHorizonRisk.lean) transfers a bound on complete words to the population experiment, integrating over the seed and allowing unbounded estimates. [ScheduledPopulation.lean](ScheduledPopulation.lean) proves `rms_lower` and `rms_separation` for maximal RMS risk.

## Replay

Use the repository's pinned Lean and a checkout with the preceding [feedback package's project dependencies](../2026-11-18-pilot-feedback/README.md) built. From this directory run:

```sh
python verify.py /path/to/built/repository --lean /path/to/lean
python check.py
```

The verifier checks the source hashes of the two earlier packages, rebuilds their research modules and this proof, checks the public theorem types and their transitive axioms, and runs `leanchecker` on each new proof module. The [audit record](audit.json) identifies the source hashes, compiler and dependency trees. The independent Python calculation groups outcomes by counts and rounds down in integer arithmetic. It gives a Bayes mean-square lower bound of 34954180699172566/10¹⁸. Lean checks its own per-word bounds at precision 10⁻²⁴.

For the recorded run, the compiled project checkout and the proof checkout have identical sources for the imported project modules. The latter tree also contains newer library modules and a revised Lean README. The `research-evidence` CI job verifies the audited proof-source hashes and reruns the independent integer calculation.
