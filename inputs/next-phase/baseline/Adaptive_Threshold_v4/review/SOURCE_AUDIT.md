# Targeted source verification for v4

This is an integration and attribution audit, **not** an exhaustive publication-priority search. It records what was checked and what each source does or does not support. The new theorems are proved in the manuscript; the references do not independently certify them.

## Central comparisons

### Giles and Haji-Ali (2019)
- Primary source: https://arxiv.org/pdf/1802.05016v2
- Published metadata: SIAM/ASA Journal on Uncertainty Quantification 7(2):497–525; DOI https://doi.org/10.1137/18M1173186
- Checked the actual PDF, including rendered pages 5 and 6 (zero-indexed pages 4 and 5).
- Assumption 2.1: the normalized absolute conditional mean divided by conditional standard deviation has a density bounded near zero.
- Assumption 2.4: for some q>2, the conditional standardized q-th central absolute moment is uniformly bounded.
- The new continuous subclass uses X∈{−1,1}, D uniform on (0,1/4], and arbitrary cell signs. Its normalized magnitude has density 1/[2a0(1+z²)^(3/2)]≤2, and conditional standardized q-th moments are ≤3^(q/2). These calculations are in the paper and the density transformation is also checked symbolically.
- The abstract establishes the adaptive MLMC upper complexity O(ε⁻²|log ε|²). Our claimed lower bound concerns the stated sample-oracle hard subclass. It does not certify the entire broader literature's optimality or preclude additional observable smoothness and alternative information.

### Lee and Valiant (2021 / extended version)
- Primary source: https://arxiv.org/html/1904.09228v3
- Fully adaptive fixed-gap coin-mixture estimation and its mixture-fraction dependence are prior work.
- The v4 fixed-gap envelope specialization recovers the balanced worst-case rate. A supremum over all sign functions does not recover a rare-event-localized theorem.
- This is a focused comparison, not a claim that every consequence of their more general machinery has been ruled out as prior art.

### Haldane (1945) and inverse-binomial sampling
- Publisher metadata: https://academic.oup.com/biomet/article-abstract/33/3/222/216056
- Bibliographic confirmation: https://pubmed.ncbi.nlm.nih.gov/21006837/
- J. B. S. Haldane, “On a method of estimating frequencies,” Biometrika 33(3):222–225; DOI https://doi.org/10.1093/biomet/33.3.222
- The original full article was not accessible in this session. Metadata was verified, and the inverse-binomial attribution is also explicitly stated in Luis Mendo's primary research article https://arxiv.org/html/1009.2022v3 (Section 1), which discusses stopping after a prescribed number of successes and the associated unbiased estimator.
- The identity E[1/(K−1)]=p for a two-success stopping count is independently reproved in the manuscript. Neither that identity nor negative-binomial sampling is claimed as new.

## Additional positioning references

- Broadie, Du, and Moallemi (2011): https://www.columbia.edu/~mnb2/broadie/Assets/nested_sim_ms_2011.pdf . Title page and introduction inspected, including screenshot. Establishes sequential inner allocation, contrasts it with uniform allocation, and credits Lee (1998), Lee–Glynn (2003), and Gordy–Juneja (2010). DOI and pages confirmed.
- Lee and Glynn (2003): https://web.stanford.edu/~glynn/papers/2003/LeeG03.html . Author-hosted record used for the title and discrete-conditioning scope.
- Gordy and Juneja (2010): https://www.federalreserve.gov/pubs/feds/2008/200821/index.html . Author/institution-hosted working paper and publisher metadata used for the nested-risk-estimation context.
- Haji-Ali, Spence, and Teckentrup (2022): https://arxiv.org/abs/2107.09148 and DOI https://doi.org/10.1137/21M1447064 . Broader adaptive MLMC probability framework; no assertion here that our result supersedes all of it.
- Giles (2023): https://arxiv.org/html/2301.02882v2 . Survey of discontinuous-function MLMC and high-kurtosis corrections. The manuscript distinguishes its second-moment confidence argument from empirical variance calibration.
- Kaufmann, Cappé, and Garivier (2016): https://jmlr.org/papers/v17/kaufman16a.html . Credited for standard sequential change-of-measure context, not as an exact statement of our latent-mixture lemma.
- Blanchet and Glynn (2015): https://web.stanford.edu/~glynn/papers/2015/BlanchetG15.html . Author's abstract states finite work-normalized variance under regularity including local twice differentiability; this supports the contrast with a discontinuous outer threshold.

The v3 references to Rhee–Glynn, Vihola, Syed–Wang, Brennan–Vinayak–Jamieson, and Chen–Naslidnyk–Briol were retained for their established roles. This revision's audit does not claim a new exhaustive rereading of each one.

## Priority and review boundary

The supplied Argon and Opus reports are AI reviews of component versions. They are not external specialist certification. The consolidated v4 preserves modest novelty positioning and explicitly leaves proof/priority review outstanding. No referee, journal, or institution has endorsed this manuscript through this package.
