# Route A primary-source refresh — 27 October 2026

This is a targeted comparison by the adversarial-review agent. It is not a priority clearance or external specialist review. The agent did not author the construction or formal specification it reviews. Model diversity among agents is not guaranteed. Imported baseline sources remain unchanged.

## Direct predecessor

**Lee and Valiant, SODA 2021, arXiv:1904.09228v3.** [Primary full text](https://arxiv.org/html/1904.09228v3).

Reinspected Theorem 2, Corollary 19, Lemma 18's likelihood factorization, Section 5.2's stopping reductions, Appendix B's final-row argument, and Theorems 4–5. Corollary 19 bounds single-coin squared Hellinger distance divided by either baseline or midpoint expected work by O(v²d²/u), assuming u,v,d,v/u are sufficiently small. Its arbitrary-stopping reduction pads to dyadic times and reveals the sign after a constant multiple of d⁻² flips. This is the actual imported input in the continuation. Theorem 2 treats an unknown heterogeneous population separated by a minimum gap and achieves the familiar rarity-dependent rate. Section 7's optimized linear estimators instead assume known positive/negative conditional laws and a per-coin depth cap. Those assumptions are stronger than knowing only the unconditional magnitude law while allowing every measurable q with integral at most rho. They do not establish Route A. The proof audit found no mismatch in the continuation's use of Corollary 19 at finite prefixes; its extension to large gaps is a separate elementary argument.

## Nested simulation

**Giles and Haji-Ali (2019), arXiv:1802.05016v2.** [Primary PDF](https://arxiv.org/pdf/1802.05016v2), DOI [10.1137/18M1173186](https://doi.org/10.1137/18M1173186).

Reinspected Assumptions 2.1/2.4, Theorem 2.7, and its work/variance proof. With d=|E[X|Y]| and sigma²=Var(X|Y), d/sigma must have a density bounded near zero; conditional standardized moments of some order q>2 are uniformly bounded. Theorem 2.7 uses estimated d and sigma, with 1<r<2-(sqrt(4q+1)-1)/q, and gives E N_l=O(2^l) and classification-error variance O(2^-l). Adaptive MLMC then has O(epsilon^-2 log² epsilon) complexity. This is a conditional-sampling construction using the sampled outer state, not a theorem uniform over the integrated rare-sign class. Its critical complexity and adaptive sampling are established overlap, not new achievements of this project.

**Haji-Ali, Spence and Teckentrup, arXiv:2107.09148v1.** [Primary full text](https://arxiv.org/html/2107.09148).

Reinspected the hierarchy oracle, assumptions surrounding Theorem 3.8, that theorem, and the optimal-starting-level discussion. Theorem 3.8 gives work epsilon^-2 when beta>gamma, epsilon^-2 log² epsilon when beta=gamma, and a slower explicit power otherwise, under their distributional regularity assumptions. Their alpha/beta/gamma index approximation convergence, and must not be identified with this project's margin exponent. The paper generalizes adaptive refinement for probability estimation; it supplies neither a global-rarity minimax converse nor an arbitrary-law Psi upper bound in the hidden-coin experiment. Shifted starting levels already appear in this lineage.

## Follow-up leads inspected beyond the old audit

**Vihola, arXiv:1512.01022v4 (2017 revision).** [Primary full text](https://arxiv.org/html/1512.01022v4).

Inspected Condition 2, Theorem 3, Examples 8–9, and Section 6's cost identities. Theorem 3 (attributed there to Rhee–Glynn) gives the single-term estimator Delta_R/p_R, unbiasedness, and second moment sum E[Delta_i²]/p_i when the latter is finite and R is independent. Its stated Condition 2 takes independent increments across levels; this can be arranged using independent copies of each coupled adjacent-level difference without changing the law of the one sampled increment. Example 8 explicitly covers independent Poisson level counts and variance equal to the same second-moment sum divided by intensity. Section 6 charges expected work by the probability-weighted level costs. These are direct overlaps with both the random-level correction and Poisson budget calibration in the new note. Neither device is new here. The new work to assess is the asymmetric observable classifier, its global-rarity moment/work guarantees, and the resulting margin-regime theorem. No claim is made that this focused inspection exhausts earlier or later debiasing work.

**Chen, Naslidnyk and Briol (ICML 2025), arXiv:2502.18284v2.** [Primary full text](https://arxiv.org/html/2502.18284v2).

Reinspected Theorem 1, Corollary 1 and the conclusion. The bound uses Sobolev kernels on compact Euclidean domains, smooth conditional densities/integrands, and a smooth outer function with bounded derivatives. The theorem controls two approximation errors by powers of the inner and outer sample counts (up to logs), and counts function evaluations. A discontinuous outer threshold with arbitrary unstructured q does not satisfy these assumptions. Their conclusion still identifies meaningful two-stage minimax lower bounds as unresolved in their setting; this does not imply priority for this project's different oracle.

**Wang, Wang and Zhang, arXiv:2201.02958v6.** [Primary full text](https://arxiv.org/html/2201.02958v6).

Full text is now accessible, extending the earlier abstract-only audit. Inspected the regression oracle, Section 4.2.3, Theorem 4.9 and Appendix L's proof. It explicitly treats indicators: with a margin bound Pr(|f(X)-z0|<=t)<=Ct^alpha (alpha<=1 in their framework), error is O_P(Gamma^-kappa (log Gamma)^(alpha/2)). Here kappa=nu alpha/[2(nu+d)] for nu>=d/alpha and alpha/[2(alpha+1)] otherwise. The proof bounds misclassifications by the empirical mass within the maximum regression error of the threshold. The inner conditional mean f is smooth in observed covariates, and cross-state kernel regression is available. Thus the title's word smooth does not exclude threshold overlap, but the oracle and function-class assumptions differ materially from arbitrary hidden-coin q. No integrated-rarity minimax theorem was identified in this inspected statement. The underlying KRR technical estimates were not independently rederived.

**Pilliat (2025), arXiv:2510.27319v1.** [Primary full text](https://arxiv.org/html/2510.27319v1).

Full theorem inspection extends the earlier abstract-only audit: Definition 2 and Theorem 2.1 characterize detectable reservoir ranks through a sample-complexity function and give high-probability rank guarantees for the recommended arm, up to a polylogarithmic factor. This is a recommendation objective. It is not estimation of the mass above a fixed threshold, and no reduction supplying Route A was established. The proof was not rederived.

## Access and search limits

The above arXiv HTML/PDF pages were accessible through the web tool. A direct PowerShell download of Lee–Valiant failed with DNS resolution failure; no local full-text copy from that command exists. Broad exact-title/date searches for later coin-mixture and adaptive nested rare-event work returned mostly the original paper and unrelated material; search indexing dates were not treated as publication dates. No exhaustive citation-graph search or external contact occurred. Abstract-only items in the preserved prior audit that are not listed above remain unchecked. No statement here certifies novelty.
