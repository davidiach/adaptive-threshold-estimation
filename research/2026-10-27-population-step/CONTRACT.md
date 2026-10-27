# Follow-up contract: obstruction audit and population-level attack

Start: 27 October 2026, HEAD a8a8dc49115aabdd1fba8d53d3390eb0a5eee864 on research/rare-minimax-20261027. The user authorizes verification, mathematical work, local commits and pushing verified work. No researcher contact or publication submission is authorized. Existing critical-two and Tier5 work is concurrent inherited material, to be read and snapshotted, not edited or silently adopted as this run's discoveries.

Principal question: in the hidden iid Bernoulli reservoir, known mu and rho, arbitrary measurable q with integral q<=rho, does the candidate Psi give the unrestricted minimax RMS law under uniform expected work? Algorithms may be biased, depend on B, and interleave or combine multiple coins. No latent D/sign access, selected-magnitude query or true-q posterior is provided.

First obligation: independently audit the proposed rho L(1+log L) lower bound for the product of separate uniform variance and work suprema of unbiased single-coin procedures at the exact quadratic law a=1/4. A valid restricted theorem is not an unrestricted minimax lower bound. Verify all thinning, localization, entropy-window, stopping and source assumptions.

Second obligation: materially attack the unrestricted population problem. A controlled-bias extension, a mathematically justified multi-coin construction, or a counterexample to a proposed reduction may be useful partial progress, but must be labelled with its exact class. Neither failure of a construction nor a finite numerical optimum proves the full minimax claim.

New formal targets require separate specification locks before proof. This pass creates no new Lean statistical specification by default. Old definitions, locks, results and acceptance criteria are unchanged. Paper proofs may be developed and reviewed, with explicitly post-proof checkpoints distinguished from prior specification locks.

## Fixed finite-horizon diagnostic specification

Before running the new diagnostic, fix the following experiment. Mu is a known finite atomic law; the unknown q is drawn once from a finite prior chosen for the diagnostic. Conditional on that one q, fresh latent coins are iid from the stipulated reservoir. Every observed bit costs one. Neither D nor S is observed. There are no free informative draws.

For deterministic horizon B=1,...,8, compute the minimum Bayes squared error over all adaptive choices of a new coin or a previously observed coin, followed by any estimator. Include the independent seed if randomization is allowed; randomization cannot improve a finite Bayes minimum over actions. The posterior mean is the Bayes-optimal terminal estimate. Coin histories can be represented by sorted (heads,tails) counts because posterior likelihoods factor by coin; this is a derived sufficient statistic, not an assumption of known q. Compare with the best policy using only one coin and with always taking fresh coins. Validate total probability and the posterior-variance recursion exactly using rational arithmetic.

This is a finite-hypothesis **Bayes** problem with a **deterministic cap**, not the unrestricted global-q expected-budget minimax problem. Its result cannot be used as a lower bound for the larger expected-budget algorithm class. No Monte Carlo or floating dynamic program certificate will be claimed. The chosen support/prior and implementation hash are locked before evaluation; no favorable-case selection after viewing results.

Planned cases: two scales with masses1/8,7/8 and gaps1/32,1/4; three scales with masses1/16,3/16,3/4 and gaps1/32,1/8,1/2. Rho=1/8. In each case the prior is uniform over q=0, a single-coordinate allocation of theta=rho/2 or theta=rho whenever feasible at each support atom, and q identically rho. Duplicate q vectors are removed. All targets are in[0,rho]. These are synthetic diagnostics.

Acceptance: exact finite arithmetic identities pass; any observed advantage is reported only for this finite prior/horizon. All failures remain recorded. Source audit and independent paper review are required before accepting new mathematical statements; no novelty or external-review claim follows.
