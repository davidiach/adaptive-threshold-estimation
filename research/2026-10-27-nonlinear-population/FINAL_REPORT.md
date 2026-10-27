# What the nonlinear attack established

The unrestricted arbitrary-law rare-event minimax rate remains open. This pass nevertheless establishes a genuine feedback advantage over the full rarity class in one finite experiment, a necessary depth condition for unrestricted algorithms, and a faithful finite approximation framework for the actual expected-budget problem. It also implements and tests a concrete nonlinear feedback estimator.

## Exact feedback advantage over the full class

For mu=(delta_(1/4)+delta_(1/8))/2 and rho=1/4, impose a deterministic total cap of two flips. Flip one coin; after a tail use a fresh coin, after a head revisit. A specified rational output table has worst-case MSE below 0.015443 over **every** feasible allocation q, whereas every preselected independent local-acquisition design has minimax MSE above 0.015475, even with shared seeds, local stopping and arbitrary nonlinear terminal estimation. The strict gap exceeds 0.000032 MSE.

This is PROVED-ON-PAPER with independent exact rational certification. The full continuum maximum is proved using convexity in the target and positive polynomial curvature on all three edges of the parameter triangle; it is not inferred from a grid. The dominating fixed-design Bayes lower bound covers optimal nonlinear estimates. The earlier two-profile certificate is preserved.

The result shows that acquisition feedback cannot always be removed without loss. It does **not** compare algorithms with expected work two, since those may occasionally exceed two flips. It does not establish a growing or asymptotic rate advantage. A separate all-mu two-flip information calculation explains the gain, but its small-rarity Bayes improvement is only order rho^4 against a leading rho^2 risk.

## A depth obstruction that includes arbitrary feedback

For the exact quadratic law on (0,a], choose K>=1 and h=a sqrt(rho). An explicit normalized odd-Legendre construction gives two feasible globally rare profiles supported on d<=h, with target separation

`Delta_K = rho / ((K+1)(2K+1))`.

Every coin word of length at most 2K has identical probability under the two profiles. Therefore any population procedure using at most 2K observations per coin has identical transcript laws under them, regardless of how it uses pilots, interleaves coins or combines outputs. Its worst RMS is at least Delta_K/2, even with unlimited total work. At K=2 this is a four-flip-per-coin floor of rho/30.

For an unrestricted procedure with RMS at most epsilon at both profiles, let p_K be the probability that some coin exceeds2K observations. This probability is identical under the two profiles, and

`p_K >= 1 - 4 epsilon^2 / Delta_K^2`.

In particular Delta_K >= 4 epsilon forces p_K>=3/4 and expected work at least (2K+1)p_K under each law. This is a necessary condition for unrestricted acquisition, proved using a common no-exit submeasure. Each K uses a different hard pair; the tails cannot be summed under one fixed population to manufacture a logarithmic lower bound.

These are reviewed paper proofs. Exact checks cover polynomial identities for K=1..16, 31 local words and 2,048 complete feedback/depth-tail transcripts; the written proof covers all K and all policies. The candidate pilot-profile recalibration failed because matching shallow word probabilities does not control `integral(q-qhat)(g-1)dmu`, its actual bias residual. Deeper production remains possible.

## A justified finite route to the unrestricted problem

Write V=R^2. Round known gap magnitudes within eta, round q downward on a grid of spacing gamma, retain all adaptive policies with total cap N, and keep the **same uniform expected budget B**. IfG is the resulting finite minimax value, then

`|V_mu(B)-G(B)| <= rho^2 B/N + rho^2 N(eta+gamma) + 2rho gamma + rho^2 N^2(eta+gamma)/(4[B+N^2(eta+gamma)])`.

The proof controls transcript coupling errors, preserves global rarity, and restores budget exactly through an explicit independent-activation step whose risk penalty appears in the bound. Choosing eta=gamma=N^-3 proves convergence for fixed mu,rho,B. The finite problem has a convex perspective/decision-flow formulation that includes arbitrary acquisition feedback and continuous terminal outputs.

This is a PROVED-ON-PAPER approximation theorem, not a numerical solution or a sharp rate. Exact bin-mass access and arithmetic are explicit theoretical conventions; arbitrary laws need not have computable representations. The finite trees may be enormous. No general finite convex program was solved in this pass. This result supplies the missing justification for finite approximation without confusing its output with an exact unbounded minimax value.

## Actual nonlinear experiment

Implemented a finite-prior posterior estimator that selects each next coin to maximize one-step posterior target-variance reduction. Its policy sees only observed histories and known mu,rho. It can change acquisition using information from other coins, so it leaves the fixed-design/additive class. The prior is a design approximation and need not describe the true q.

The locked synthetic suite ran 7,680 replicates across two gap laws, two rarity levels, five profiles, three budgets and four sampling policies. One profile in every law/rarity case lies outside the finite prior. All pilot, observation, output and cost limitations are recorded. Feedback had lower MSE point estimates in 40 of 60 comparisons against the best fixed acquisition alternative, and lower maximum tested MSE in all 12 law/rarity/budget groups. It beat the rarity-midpoint point estimate in 46 of 60 cells. Full RMS, bias, variance, raw/clipped outputs, miss probability and bounded-loss uncertainty are retained.

These numbers are **NUMERICAL**, using float64 and seeded pseudorandom streams.32 replicates yield wide cellwise uncertainty; the maximum spans only five tested profiles. Fixed-block alternatives are not published optimized comparators. No confidence procedure, coverage claim, stable speedup, break-even claim, arbitrary-q guarantee or uniform rare-event optimality is accepted. The method was not tuned after these results. One predesignated replicate in each of 240 cells reproduced outputs and acquisition counts.

## Verification, positioning and next mathematical obligation

Separate agent review accepted the exact stated scopes. The independent full-class replay checked 153 direct latent-mixture points, independently reconstructed all edge polynomials and verified the rational Bayes inequalities; the proof of continuum convexity is separate. All 34 original validator regressions and 50 original-input checks passed. Original locks are rechecked before commit. No new Lean theorem, external review or novelty claim is made.

Lee–Valiant's known-conditional-population acquisition optimization suggests a route, but a learned profile must be controlled in the response-weighted norm that enters calibration. Simply fitting q or its target is insufficient. The clipping analysis gives a conditional bounded-kurtosis transfer and an explicit counterexample to inferring clipped risk from raw variance without a tail premise.

The central remaining work is to control pilot-dependent acquisition and nonlinear estimation uniformly over nuisance profiles, or derive a lower bound that couples those operations. The finite approximation theorem now gives a faithful computational route, and the exact feedback separation proves that a blanket removal-of-feedback argument would be wrong. None of these results settles whether Psi is the unrestricted minimax law.
