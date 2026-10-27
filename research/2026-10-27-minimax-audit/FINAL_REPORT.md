# Research outcome

**The arbitrary-law rare-event minimax problem is not resolved.** This run neither proves a universal upper bound matching Psi nor disproves Psi. It produces a new reviewed critical-margin upper bound, a rigorous stopping-scope obstruction, a bounded-channel extension, a fair negative practical result, and a more precise account of the inherited lower bound. Priority remains unresolved.

## Strongest new theorem

For every law satisfying `F(x)<=(x/a)^2`, known `a,rho`, and only the global constraint `integral q dmu<=rho`, an observable unbiased single-coin estimator has

`E Y² <= (165/56) rho`, and `E T <= 1350 a^-2 L(1+log L)`, where `L=1+log(1/rho)`.

Independent Poisson replication and clipping give

`R(B) <= min{rho/2, sqrt(5400 rho L(1+log L)/(a²B))}`.

Bias, moments, uniform expected work, termination, and confidence amplification are proved in `RESEARCH_NOTE.tex` / `theorem/critical.tex`. The construction observes neither individual gaps nor q. It even works when the particular law is unknown inside the supplied envelope. The bounded-observation extension uses real observations directly and includes a derived uniform-noise example.

For the exact quadratic power law, the audited inherited lower functional is comparable to `min{rho,sqrt(rho L)/(a sqrt B)}`. The remaining factor is `sqrt(1+log L)`. This is a uniform joint statement in rho and B, not an assertion that fixed-rho asymptotics settle rare-event optimality. No necessity or removal of that factor was established.

Status: **PROVED-ON-PAPER with separate adversarial agent review; not Lean-checked, not externally reviewed.** The lower comparison imports the separately audited inherited Lee–Valiant reduction. No new result is represented as an externally reviewed or novel theorem.

## Strongest new negative result

One-law finite mean work does not transfer almost-sure termination across an unbounded fresh-coin reservoir. With D=1/2, fresh sign priors5/8 versus3/8, and stopping at the first +1 hit of the observed random walk:

`E_plus T=4`, while `P_minus(T=infinity)=2/5`.

There is also an interior-gap example. The full transcript can even have finite KL while the second law has nontermination mass. The unchanged finite-coin Lean theorem remains valid. This counterexample rules out a naive stronger bridge specification; it does not refute the minimax lower bound, whose uniform budget supplies admissibility under both laws. The note gives the correct finite-prefix-to-terminal-testing argument. Concurrent Tier5 work already limits its stopping conclusion appropriately and is not accused of this error.

The cross-state regression example separately demonstrates why a linear marginal gap density cannot imply a logarithmic lower bound when observed covariates share a learnable parameter.

## What was inherited versus established here

Inherited: v4 and continuation; Psi statistical lower and variational optimizer; matching power-margin paper results below two; dirty route-a alpha>2 construction; completed Tier1/2/3/4 and713 components; unknown-rarity impossibility; historical negative benchmarks. Those were inspected and re-audited, not claimed as this run's original achievements.

New: critical upper theorem and complete proof; arbitrary-law finite constructive bracket without a matching claim; bounded-channel extension and explicit structured boundary; stopping counterexample and corrected limit principle; a qualified known-gap unknown-rarity estimator with computable conservative CI; source comparison and corrections; exact baseline resimulation; locked seven-model direct-observation experiment and raw data.

The complete confidence procedure in the theoretical note is distinct from the heuristic practical candidate, for which coverage is not claimed.

## Literature and significance

The inherited squared-log nested lower bound's defensible contribution is an all-algorithm expected-work obstruction on one fixed **unstructured observed-state class** satisfying GHA's density and conditional-moment assumptions with accuracy-independent constants. Its hard member can change with accuracy inside that fixed class. This is not a lower bound for a fixed finite cell set, the particular known Gaussian GHA model, smooth regression classes, or a rare-event class.

LV v3 Lemmas17–18/Cor19 were inspected with their actual smallness/expected-work hypotheses. Section7's known sign-conditional laws and depth restriction do not directly solve the present global-rarity problem. The audit adds Blum–Hu's adaptive good-arm counting predecessor and records the limitations of comparisons with Broadie–Du–Moallemi, Gordy–Juneja, Lee–Glynn, Haji-Ali–Spence–Teckentrup, Giles, smooth nested simulation, kernel quadrature, and established inverse-sampling/debiasing methods. It corrects an inherited Hellinger-normalization statement explicitly.

No inspected explicit match is a search observation, not proof of novelty. Source access, unfinished citation tracing and original-paper limitations are listed. Specialist questions and correspondence are drafted in `REVIEW_PACKET.md` and were **not sent**.

## Practical outcome: reject general-improvement claim

The four historical cells reproduced all2,000 output/work pairs exactly. The historical candidate still loses to tuned GHA. New testing used42 locked cells,5,376 runs and52,720,432 original inner observations, with analytic truth, raw/clipped risk, bias, variance, accuracy misses, work quantiles, outer counts and timings retained.

The asymmetric candidate beats the symmetric ablation by RMS point estimate in only5/14 comparisons. At budget16,384 on near-threshold negatives, its RMS is0.43268 at mean work14,818.9 against truth0.05; the symmetric variant has RMS0.40934. At the published GHA model the two are0.02952 versus0.02876. There are favorable cells, but no stable matched-accuracy gain. Bootstrap intervals are descriptive, not a certified separation.

The new GHA comparator uses published inner sampling in an explicitly altered, calibrated single-level driver. It is not substituted for the original tuned comparator when making significance claims. All methods see the same real observations; no Bernoulli conversion was used. New fitting/tuning costs are zero. Historical training costs, verification/reproduction expense, one-shot limitations and undefined break-even workload are explicit in `ALGORITHMS.md`. No confidence coverage or practical speedup is claimed.

## Verification actually completed

- Fourteen baseline integrity/numerical/regression gates passed on a current-byte snapshot; historical results and freeze files were preserved.
- 51 cache-aware Lean module builds and fresh exact-type/transitive-axiom checks of398 roots passed. The scoped closure has67 unchanged local sources and exactly the standard allowlisted axioms. This was not a cold rebuild of Mathlib.
- An earlier whole-directory checkpoint remains `valid=false` because five unrelated Tier5 files changed concurrently. The separate scoped audit is not a redefinition of that global check and certifies no Tier5 work.
- Exact finite diagnostics and implementation tests passed; their finite arithmetic scope is recorded separately from the paper theorems.
- The new TeX note compiled to PDF. Visual export checks and final preservation/source-lock results are recorded by the acceptance files.
- The final whole-preservation gate remains **false** for two concurrently updated, initially uncommitted Route A generated files (build.log and status.json). The same gate's independent artifact, data, v4 and lock checks pass. It was not weakened to hide this change; details and both hashes are in ACCEPTANCE.json. This task did not write those files.

No new complete Lean statistical theorem was added. The user-owned concurrent Tier5 and critical-two developments are outside this task's new deliverables and must be assessed by their own actual evidence.

## Exact remaining obligations

1. Prove arbitrary-law upper `R <= C Psi`, or construct a rigorous counterexample with a replacement lower/upper characterization. Finite diagnostic grids do not discharge this.
2. Remove the critical `1+log L` work factor or prove it necessary; neither direction is known here.
3. Establish sharp qualified adaptation with unknown mu/rho. The known-gap additive floor is sufficient only; the qualitative impossibility does not determine a sharp penalty.
4. Assemble a genuine countable iid reservoir realization, consistent prefix semantics and the rare-prior statistical information theorem in Lean. Current completed old tiers do not already do this.
5. Obtain specialist proof/priority review; finish the explicitly unresolved primary-source comparisons.
6. Find a practical method with stable gains at matched accuracy against a fully validated comparator, including all overhead. The present candidate is rejected on its test set.

These are checkpoint limits. No unbounded computation, paid service, publication, push or external communication was launched, and no unfinished work is represented as continuing in the background.
