# Prior-art audit: adaptive threshold estimation, next phase

**Date:** 26 October 2026. **Status:** source comparison, not a proof of priority.
The baseline v4 is unchanged. Proved results, conjectures, and measured evidence are separated in `report/research_note.pdf`. No novelty claim is made for either v4 or this continuation.

## What was actually compared

The entries below record inspection depth, not merely whether a title appeared in search. “Not found in the inspected statements” is not equivalent to “does not exist anywhere in the literature.” Web-rendering/access failures and abstract-only comparisons are listed rather than silently filled in.

### A. Adaptive nested simulation and the squared-log lower bound

**Giles and Haji-Ali (2019), _Multilevel nested simulation for efficient risk estimation_.**
Primary source: https://arxiv.org/pdf/1802.05016v2
DOI: 10.1137/18M1173186.

Inspected: adaptive upper-bound statements, Algorithm 1; numerical Section 3, equation (3.2), conditional moments; antithetic coupling (3.5); coarsest-level optimization (3.6). Relevant PDF pages were rendered through the web screenshot tool. This is the exact source of the model and comparator components used here.

Known overlap: adaptive inner sampling, MLMC, the critical O(epsilon^-2 log^2(1/epsilon)) upper complexity, and improving the coarsest level. The shifted-start construction here does not claim invention of coarsest-level optimization. The inspected statements do not supply an all-adaptive minimax matching lower bound. This does not certify that no later or less directly indexed paper does.

**Chen, Naslidnyk and Briol (ICML 2025), _Nested Expectations with Kernel Quadrature_.**
Primary full text: https://arxiv.org/html/2502.18284v2

Inspected: problem statement, regularity/oracle setting, Section 6 conclusion. The conclusion explicitly treats meaningful two-stage minimax lower bounds as open. Their smooth-kernel/function-evaluation setting is different from the discontinuous threshold and unstructured sample oracle. This is evidence that lower bounds are a recognized issue, not evidence that v4 resolves their full problem.

**Wenjia Wang, Yanyuan Wang and Xiaowei Zhang, _Smooth Nested Simulation: Bridging Cubic and Square Root Convergence Rates in High Dimensions_.**
Primary record: https://arxiv.org/abs/2201.02958 (v6, revised 11 October 2023).
Published DOI: 10.1287/mnsc.2022.00204.

Inspection limit: primary abstract and bibliographic record only in this run. Kernel ridge regression exploits smoothness in the observable conditioning variable. The full minimax implications were NOT checked; this remains an outstanding comparison.

**Conclusion for area A:** the known critical upper rate is not a contribution of v4. No matching all-algorithm lower theorem was located in the specific inspected primary statements, but there is no certified priority clearance. Smooth cross-state information and alternative oracles cannot be conflated with the latent-coin model.

### B. Threshold mass, margin assumptions, and active level sets

**Lee and Valiant, _Uncertainty about Uncertainty: Optimal Adaptive Algorithms for Estimating Mixtures of Unknown Coins_, SODA 2021.**
Primary full text: https://arxiv.org/html/1904.09228v3

Inspected: fixed-gap upper/lower statements; Lemmas 17–18 and their decomposition proofs; Corollary 19; Section 7 including Theorems 4–5 and the per-coin depth restriction.

Known overlap: the rare fixed-gap rate rho epsilon^-2 Delta^-2 log(1/delta); fully adaptive information decomposition; single-coin history-averaged information; optimization for known positive/negative conditional laws. The general lower theorem in this continuation explicitly USES Corollary 19. Its bounded-relative-change decomposition follows the same mechanism as Lemma 18 and is not presented as an independent new principle.

Exact imported input: when u, v, d and v/u are sufficiently small, the single-coin squared Hellinger distance between sign weights u and u+v divided by expected work under u is O(v^2 d^2/u). Their Hellinger normalization differs by a harmless constant. The note extends only the large-d range by revealing the sign at the first query, and then proves the magnitude-dependent perturbation argument. The general lower bound concerns iid fresh coins; it is NOT asserted for arbitrary selected magnitudes.

Difference requiring further specialist assessment: only an integrated positive-mass constraint, with an unknown sign function at every magnitude and no minimum gap. Known conditional laws would be a different experiment. No claim that the entire variational characterization follows from the present work: its general upper half is conjectural.

**Brennan, Vinayak and Jamieson (2020), _Estimating the Number and Effect Sizes of Non-null Hypotheses_.**
Primary full text: https://arxiv.org/abs/2002.07297
Proceedings PDF: https://proceedings.mlr.press/v119/brennan20a/brennan20a.pdf

Inspected: Section 1.1 observation model, Theorem 2.1 and associated estimation discussion. It estimates mass above thresholds simultaneously and conservatively using iid latent effects with observed test statistics. The inspected experiment does not grant unrestricted sequential revisiting with a counted total coin-flip budget. This is substantive neighboring work, not a title to dismiss. Its stated lower bounds were not identified as the rare-event adaptive law here.

**Gotovos, Casati, Hitz and Krause (IJCAI 2013), _Active Learning for Level Set Estimation_.**
Primary PDF: https://www.ijcai.org/Proceedings/13/Papers/202.pdf

Inspected: Section 2, including a page screenshot. Output is classification of points in a finite domain using a GP model. It is not merely a scalar mass estimate from unrelated latent coins. Cross-point structure matters.

**Hanneke and Yang, _Minimax Analysis of Active Learning_.**
Primary record: https://arxiv.org/abs/1410.0996

Inspection limit: abstract-level verification. VC/hypothesis-class and Tsybakov-noise assumptions are relevant vocabulary, but the complete reduction or exclusion was NOT verified. It is not responsible to infer absence of overlap from the abstract.

**Conclusion for area B:** rare fixed-gap optimality and adaptive decomposition are established. The exact global-rarity power-law statement and the variational lower bound were not located in the inspected statements; that is a limited search outcome, not an originality verdict. The matching arbitrary-law upper bound remains conjectural.

### C. Infinitely-armed / reservoir bandits

**Maryam Aziz, Jesse Anderton, Emilie Kaufmann and Javed Aslam (ALT 2018), _Pure Exploration in Infinitely-Armed Bandit Models with Fixed-Confidence_.**
Primary PDF: https://research.cs.cornell.edu/conferences/alt2018/A/aziz18Paper.pdf

Inspected: Sections 2.2 and 3, Theorem 1, relevant page screenshots and author page. The reservoir/revisiting access model overlaps. The objective is to return an arm in a prescribed top-alpha quantile: alpha is an input, not an unknown fraction to estimate. Its lower bound cannot be substituted for a fraction-estimation theorem without a reduction.

**Emmanuel Pilliat (2025), _Adaptive Algorithms for Infinitely Many-Armed Bandits: A Unified Framework_.**
Primary record: https://arxiv.org/abs/2510.27319

Inspection limit: primary abstract. Recommendation/regret objectives rather than a verified fraction-estimation theorem. Full theorem comparison remains outstanding.

**Conclusion for area C:** Lee–Valiant is the directly relevant fraction-estimation predecessor. Reservoir search and good-arm identification have related information tools, but a different output objective. The audit does not assert that all reservoir fraction-estimation work has been exhausted.

### D. Inverse-binomial sampling and Monte Carlo budget allocation

**Luis Mendo, _Asymptotically Optimum Estimation of a Probability in Inverse Binomial Sampling under General Loss Functions_.**
Author PDF (25 April 2012): https://oa.upm.es/10749/1/asympt-opt16completo.pdf

Inspected: parsed full-text introduction, equation (1), related references. PDF screenshot requests failed in the web renderer; no visual inspection of this particular source is claimed. Equation (1) gives (r-1)/(K-1), explicitly attributed to Haldane (1945). At r=2 this is v4's reciprocal-count identity. The original 1945 article was not newly read in full during this run; this attribution is supported through Mendo's primary paper.

**Mendo and Hernando (2008), _Improved Sequential Stopping Rule for Monte Carlo Simulation_.**
Primary record: https://arxiv.org/abs/0809.4047

Inspection limit: primary abstract. Inverse/negative-binomial stopping for Monte Carlo probability estimation is established; the full stopping-rule lineage was not exhaustively traced.

**van Opheusden, Acerbi and Ma (2020), _Unbiased and Efficient Log-Likelihood Estimation with Inverse Binomial Sampling_.**
Primary record: https://arxiv.org/abs/2001.03985
Attempted full text: https://pmc.ncbi.nlm.nih.gov/articles/PMC7758077/

Inspection limit: primary abstract; full PMC retrieval was blocked. The work concerns unbiased log-likelihood estimation, not a verified exact match to the v4 marker-plus-independent-production wrapper. No absence claim follows from that access limitation.

**Safa C. Medin, John Murray-Bruce, David Castanon and Vivek K. Goyal (2019), _Beyond Binomial and Negative Binomial: Adaptation in Bernoulli Parameter Estimation_.**
Primary full text: https://arxiv.org/html/1809.08801v2

Inspected: abstract; Sections I and III-B/III-C; conclusion. It optimizes adaptive Bernoulli trial allocation under mean-work constraints, including Beta-prior stopping-rule designs, and explicitly discusses inverse-binomial history. It reinforces that adaptive expected-budget allocation is established. The inspected formulas concern individual parameter/function estimation and Bayes-risk allocation, not the exact v4 cost-marker wrapper identities. This is not a priority clearance for that wrapper.

A final search also located the review _Stopping Rules for Monte Carlo Methods_ (arXiv:2510.22688). It is recorded as a follow-up bibliographic lead, not used as primary evidence for a theorem or claimed fully checked.

**Conclusion for area D:** the inverse-count identity, inverse-binomial Monte Carlo, and adaptive mean-budget allocation are established. Whether the precise marker-plus-fresh-production wrapper already appears elsewhere remains unresolved. No novelty claim is made.

## Search scope and exclusions

The search covered combinations of: adaptive nested simulation probability lower bounds; threshold mass under general margins and Tsybakov conditions; active level-set estimation; reservoir fraction/good-arm estimation; inverse-binomial Monte Carlo stopping and allocation. A final exact-query sweep used:

- `"adaptive" "nested simulation" "lower bound"`
- `"estimating" "mass above" "threshold" "adaptive"`
- `"reservoir" "estimating" "fraction" "arms"`
- `"inverse binomial" "Monte Carlo" "allocation"`

These broad searches also returned irrelevant Bayesian nested sampling, unrelated threshold applications, and secondary bibliographic pages. They were not counted as matching theoretical evidence. A recent adaptive multilevel rare-event text-generation paper uses nested observable score events, not the same hidden-threshold conditional-mean experiment; the search excerpt alone was not treated as a full comparison.

## What remains unestablished

1. A matching arbitrary-law upper bound for Psi, particularly screening of negatives across irregular scales.
2. A complete prior-art exclusion for the v4 critical all-adaptive lower theorem.
3. Full comparisons with abstract-only sources, older stopping-rule work, and recent reservoir work.
4. Publication priority for the rare-event power theorem or exact cost wrapper.

The report proves specific mathematical claims; the audit does not certify that any of them is first.
