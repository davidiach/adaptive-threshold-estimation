# Observable procedures and finite diagnostic

All procedures use the hidden iid reservoir from CONTRACT.md. A genuine flip costs one, including pilot observations. Internal arithmetic and parameter-independent randomization are free. Knowing mu means its integrals and distributional representation can be used; it does not reveal a sampled magnitude. No procedure is given q. Reference-law simulation in the information reduction is a mathematical comparison experiment, not an oracle granted to the actual estimator.

## Exact finite-prior allocation diagnostic

The prior draws q once for the entire experiment from the finite list in FINITE_LOCK.json. Fresh coins are conditionally iid given that q. For a coin history with h heads and t tails, its likelihood at q is

`sum_i mass_i [q_i(1/2+d_i)^h(1/2-d_i)^t +(1-q_i)(1/2-d_i)^h(1/2+d_i)^t]`.

The transcript likelihood is the product of these coin likelihoods. Adaptive scheduling has no parameter-dependent likelihood factor because each action is determined by the independent seed and observed history. Thus the sorted list of per-coin counts is sufficient. Coins with the same counts are interchangeable. Sorting does not introduce a binomial coefficient: these are probabilities of individual ordered histories, not probabilities of a count class. The posterior predictive probability of an observed bit is the ratio of the updated and current mixture likelihoods. The two ratios sum to one.

At horizon zero the posterior mean of theta minimizes squared error, with posterior variance as its conditional risk. At each preceding state, enumerate a fresh coin and each distinct existing history, average the two successor risks using predictive probabilities, and minimize. This Bellman recursion is exact for all adaptive allocation policies in the stated finite-prior, deterministic-cap problem. Randomizing the choice cannot improve the minimum. Using all remaining observations weakly decreases Bayes risk, so permitting earlier stopping would not change the result. A fresh coin means an iid draw; no gap is selected.

`finite_bayes.py` implements this recursion using Python Fraction arithmetic. Its inputs and implementation were locked before the first evaluation. It covers horizons1 through8. The comparisons always use the same posterior-optimal terminal estimator, with acquisition restricted either to one coin or to fresh coins. The displayed policy files contain observable count histories and actions, never D or S. Their prior-specific posterior is implementable in the diagnostic because that finite prior is specified; it is not the unknown-q posterior for the unrestricted minimax problem.

`verify_finite.py` independently enumerates labeled coins with their ordered bit tapes, without importing the canonical implementation. All10 risk values through horizon5 agree exactly. Probability identities, prior-average conditional risk identities and monotonicity are checked by the production recursion. Exact rational arithmetic certifies these finite computations; it is not a Lean proof of the implementation or a statistical theorem about unbounded algorithms.

| Locked synthetic case | B | Optimal adaptive Bayes MSE | Best restricted Bayes MSE | MSE reduction |
|---|---:|---:|---:|---:|
| Two scales | 8 | 0.00211178300124 | 0.00214594085928 (single coin) | 1.5917% |
| Three scales | 8 | 0.00170672908411 | 0.00179713806587 (fresh coins) | 5.0307% |

These are rounded displays of exact fractions in FINITE_RESULTS.json. There are no Monte Carlo seeds, confidence intervals, measured work tails, or coverage claims. All policies use exactly B genuine flips. The production calculation took0.333seconds and the independent check0.580seconds on this checkout; these are single wall-time measurements, not comparative performance claims. This is not a new held-out practical benchmark or an expected-budget minimax lower bound.

## Radial screening rule

For the exact quadratic law with a=1/4, solve `E min(1,b^2/D^2)=rho` using the known law. Set `M=ceil(8a/b)`. Starting at zero, add `2X-1` for each observation of one genuine coin. Stop at -1 or M and output whether M was hit. The paper proof establishes termination and bounded expected work on the specified radial submodel, and gives a lower bound on its directional Fisher information. For a finite-cap version stop after N observations and output one only if M has already been hit. This binary output is a statistical test, not an estimator unbiased for theta under arbitrary q. No practical superiority or uniform error guarantee is claimed for it.

## Explicit independent-pilot construction

`upper/proof.tex` and `upper/` implementation define exact three-flip, two-gap polynomial features Y,Z using only observations and the known two-atom law. On m fresh pilot coins compute `beta_hat=average(YZ)/Var(Z)`, then return `average(Y-beta_hat*Z)` on n independent production coins. The procedure terminates after exactly3(m+n) charged observations and is unbiased for every global-rarity allocation. Its variance formula includes the pilot estimation term. A proved saddle-point result shows that this pilot cannot improve worst-case raw MSE over the best fixed coefficient for these fixed features, even before charging pilot work. Clipping, pilot-dependent acquisition, and nonlinear aggregation are outside that result.

## Reproduction without overwriting historical outputs

Use Python3.12.2 with no third-party packages for the finite diagnostic. From the repository root, copy `finite_bayes.py`, `verify_finite.py`, `CONTRACT.md`, and `FINITE_LOCK.json` into a new empty temporary directory; run `python finite_bayes.py run` there and then `python verify_finite.py`. Compare the exact rows and policy JSON against this checkpoint, ignoring elapsed time. Do not rerun the lock command or replace the committed output. `check_checkpoint.py` performs this replay automatically when available in the final package.

The unchanged repository validator regressions were run through `regressions.py`; raw logs and commands are in regressions/. Paper arithmetic checks and the isolated Tier5 replay have separate scripts and logs in audit/. The Tier5 archive and restoration instructions preserve the concurrently authored proof sources required for reproduction. None of these formal checks proves the new statistical statements.
