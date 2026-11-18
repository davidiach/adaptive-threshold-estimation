# Feedback improves the 18-plus-seven policy at gap 1/5

At the single gap $d=1/5$, flip 18 distinct coins once. At follow-up position $k=1,\ldots,7$, choose a fresh coin, the $k$th pilot head, or the $k$th pilot tail. An unavailable candidate defaults to fresh. Estimate the positive-sign fraction $p\in[0,1]$ under squared loss.

| When the seven actions are chosen | Worst-case RMS |
|---|---:|
| All seven after the pilot, before any follow-up answers | At least **0.18735887** for every such policy |
| One after each preceding answer, using the existing adaptive policy | **≈ 0.186751999656** |

The gap exceeds **0.00060687 RMS**. Both experiments allow the estimate to use the entire ordered transcript and an independent random seed. The precommitted design may even inspect the order of the pilot. The lower bound concerns this fixed pilot and menu. The exact restricted minimax risk and the sharp unrestricted large-budget coefficient remain open. [Adaptive witness and its exact worst risk](../2026-11-17-rms-constants/AuditPilot.lean)

## Proof

Put prior masses $(2,3,3,2)/10$ on $p=(0,3/10,7/10,1)$. The maximum of the four mean squared errors bounds their prior average from above. Thus a lower bound for the best prior-averaged MSE applies to every estimator's worst-case MSE.

**1. Reduce the design to counts.** Let $j$ be the number of pilot heads. Write $h,t$ for the numbers of distinct pilot heads and tails revisited and $f=7-h-t$ for the fresh flips. The conditions are $h\le j$, $t\le18-j$, $h+t\le7$. Every such allocation can be realized with the original position-dependent choices. Schedule the less numerous pilot type's revisits first. The more numerous type has at least nine candidates, so it is available at every position where it is needed. The [exact checker](check.py) also enumerates the reachable count pairs position by position.

**2. Retain the information in the ordered transcript.** At fixed $p$, a fresh head has probability $s=0.3+0.4p$. Conditional on a fixed pilot word, a repeated pilot head has head probability $(0.09+0.4p)/s$, and a repeated pilot tail has head probability $0.21/(1-s)$. These follow by mixing the two latent coin types, whose head probabilities are $0.7$ and $0.3$. Distinct follow-up positions use distinct labels. Consequently, for each fixed schedule the three groups give independent binomial head counts $a,b,c$ with sizes $h,t,f$ and the respective head probabilities above. The pilot count itself is binomial with parameters $(18,s)$. [Single-coin law](../2026-11-17-rms-constants/RevisitKernel.lean) · [Distinct-label policy and transcript law](../2026-11-17-rms-constants/PilotPolicy.lean)

Fix the private seed. Each ordered word has probability equal to a product of one-step likelihoods. The factors depend only on the stage, action and observed bit. Two words with the same grouped counts therefore have the same probability at every $p$, even when different pilot orders trigger different schedules. Given the counts, draw uniformly among the compatible words and apply the original estimator. This recovers the expectation of every function of the ordered transcript, including indicators of output events. Lean checks the identity for every $p\in[0,1]$ and identifies the probability of each observed count vector in the original experiment. [Ordered likelihood](OrderedExperiment.lean) · [Uniform reconstruction and count probabilities](OrderedReduction.lean)

**3. Minimize the Bayes loss.** For fixed $j,h,t$ and a grouped outcome, let $w_i$ be its joint probability with prior point $p_i$. The smallest contribution to the prior-averaged MSE is attained by the posterior mean and equals

$$
\min_x\sum_i w_i(x-p_i)^2
=\frac{\sum_{i<\ell} w_i w_\ell(p_i-p_\ell)^2}{\sum_i w_i}.
$$

Sum these contributions over $a,b,c$, minimize over the feasible $h,t$ separately at each $j$, then sum over $j$. The 516 combinations of $(j,h,t)$ give an exact finite calculation. The posterior-mean implementation using Python fractions puts the optimal Bayes MSE in $(0.0351033491898652,0.0351033491898653)$. One minimizing design for this prior revisits as many of the less numerous pilot type as it can, fills the remaining positions with fresh coins, and uses seven fresh coins when the pilot is tied.

**4. Compare the risks.** A separate Lean implementation computes the joint masses from single-flip and paired-flip likelihoods. It rounds each minimum loss contribution down to a multiple of $10^{-16}$ and certifies a common bound for all allocations in each pilot row. The row bounds sum to **0.0351033484**, which exceeds $0.18735887^2$. For the earlier adaptive policy the exact maximum over all $p$ is $348763093753675683898541718818533/10^{34}$ in squared-error units. Its square root is less than $0.186752$.

## Verification scope and replay

The grouped calculation certifies the four-point lower bound using the joint probabilities of single flips and pairs. A second certificate operates on ordered words. At the four prior points every one-step conditional probability has denominator dividing 1450. Interchanging adjacent precommitted actions preserves the sum of the leaf bounds over all suffix answers. This reduces the check to the 516 pilot counts and allocations. Each per-word contribution is rounded down in units of $10^{-24}$. The pilot recursion permits a different schedule for each ordered pilot word. [Grouped calculation](FeedbackTable.lean) · [Permutation and integer certificate](OrderedCounts.lean) · [Ordered Bayes bound](OrderedBayes.lean)

The final theorem compares both policies using the repository's original population experiment and squared-risk definition. The precommitted estimator may use any measurable output of its private seed and full tape. Lean proves that the first 25 answers recover the stopped tape almost surely, integrates over the seed, and uses the four-point average as a lower bound on worst-case squared error. Clipping reduces squared error at each prior point, so the argument also covers estimators with unbounded output. [Original-experiment lower bound and strict inequality](OrderedPopulation.lean) · [Exact theorem statements](AuditFeedback.lean)

From this directory run:

```sh
python check.py
python verify.py /path/to/built/repository --lean /path/to/pinned/lean
```

The first command needs only Python's standard library. The second requires the project's compiled Lean and Mathlib imports. It rebuilds the 15 research modules identified by the [pilot audit](../2026-11-17-rms-constants/pilot-audit.json), compiles the ten feedback modules from source, checks the theorem statements and their transitive axioms, and runs the independent kernel checker on all ten modules. [Replay record](audit.json)
