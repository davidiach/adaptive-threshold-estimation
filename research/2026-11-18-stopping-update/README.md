# One update at a stopping time

At gap 1/5 and a budget of 25 flips, every policy in the pilot's distinct-label menu that can replace its follow-up schedule once has worst-case RMS risk **at least 0.186844275**. The existing fully adaptive witness has worst-case RMS **below 0.186752**. The updated lower bound applies in the original population experiment, including randomized plans and arbitrary measurable estimates that use the seed and the entire ordered transcript.

After 18 fresh pilot flips, the initial plan specifies seven follow-up actions. Before each next action, the policy may use all answers so far to decide whether to trigger. At the first trigger it chooses the entire remaining schedule from that history. Each follow-up position can request its designated pilot-head label, pilot-tail label, or a fresh label. An unavailable revisit yields a fresh flip. Triggering immediately, waiting until the final action, and never triggering are all allowed.

## Exact comparison

The [exact checker](check.py) minimizes four-point Bayes mean-square loss with rational arithmetic. The sign probabilities are 0, 3/10, 7/10 and 1, with respective prior masses 2/10, 3/10, 3/10 and 2/10. For a fixed ordered initial sequence, the recurrence compares two costs at each prefix:

- Trigger now. Minimize over legal committed suffixes using the current posterior. Within a committed suffix the likelihood factors commute.
- Continue. Use the next prescribed action and sum the two child losses, with the trigger still available to each child.

The checker minimizes over the initial sequence after computing its two alternatives. At the seventh action the policy can commit to any legal last move, so six prescribed positions suffice. At a leaf the posterior mean minimizes squared error. The resulting **optimal Bayes RMS** lies in **[0.186844275419, 0.186844275420)**. This prior yields a lower bound on worst-case RMS. The worst-case optimal value for the whole class remains open.

## Lean proof and replay

[StoppingPolicy.lean](StoppingPolicy.lean) records the first triggering prefix and proves it persists on every extension. Its expectation identity uses the original ordered-transcript law. [StoppingBounds.lean](StoppingBounds.lean) defines the finite recursion. [StoppingCertificate.lean](StoppingCertificate.lean) checks all 19 pilot counts and every legal ordered initial plan, rounding each leaf down at precision 10⁻²⁴. [StoppingBayes.lean](StoppingBayes.lean) proves the recursion bounds the loss of every stopping rule and terminal estimate. [StoppingPopulation.lean](StoppingPopulation.lean) transfers this to the population experiment and proves `rms_lower` and `rms_separation`.

Run these commands from this directory with the repository's pinned Lean and a checkout with the [prior research package's dependencies](../2026-11-18-scheduled-update/README.md) built.

```sh
python check.py
python verify.py /path/to/built/repository --lean /path/to/lean
```

The verifier rebuilds the research dependencies and checks the [public theorem statements](AuditStopping.lean), their transitive axioms and all five new modules with `leanchecker`. The [audit record](audit.json) identifies the compiler, source hashes and dependency trees. The recorded build reused compiled project imports whose sources match this checkout. CI checks the audited source hashes and reruns the rational calculation.
