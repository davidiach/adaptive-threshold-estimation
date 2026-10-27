# Nonlinear critical construction ledger

Final outcome: the common-pair and full-model steps below subsequently passed
independent adversarial review as the complete theorem in `unrestricted.tex`.
`CHECKPOINT.md` is the current result and evidence record; provisional entries
below retain the sequence of attempted arguments.

## Target and ownership

Known quadratic law with a=1/4, known rho, global integral q <= rho. Principal full-population Psi conjecture remains the target. This construction role owns only `construction.tex` and this ledger in this directory. Old critical-two sources, reviews, locks, population-step work, and Tier 5 files are preserved.

## New candidate

The current TeX gives a complete analytic candidate: arbitrary nonlinear aggregation cannot improve the sharp rho L(1+log L) variance-work scale for (i) a deterministic finite set of independent, possibly heterogeneous single-coin procedures with private seeds, or (ii) an independent Poisson count of repetitions of one fixed procedure. In both classes local stopping may be unbounded and the terminal output may be clipped. All constants are universal at fixed a=1/4. Full cross-coin feedback and a shared random choice of local experiment remain outside the theorem.

Dependency chain: prior committed additive lower -> finite convex-experiment RMS comparison -> finite partition approximation of actual stopped transcripts -> same-work additive output -> lower for arbitrary aggregation. The upper uses the prior unbiased kernel with private activation or Poisson replication.

## Attempts and failures

1. Inspected the other owner's population-step summaries. Their radial information obstruction is refuted, and their calibrated radial estimator attains Psi on a known one-dimensional profile. Neither result proves the arbitrary-q minimax claim. Their fixed-feature scalar pilot result does not overlap the new arbitrary-aggregation comparison.
2. Investigated Juditsky--Nemirovski 2009 directly, including its assumptions, finite categorical and Poisson examples, multiple independent observations, confidence theorem, exponential-envelope proof, and Hellinger saddle representation. A confidence guarantee alone is insufficient for RMS. The new note proves RMS explicitly by bounding the saddle temperature through the diagonal objective and integrating the resulting tails; a universal factor 12 is sufficient.
3. A whole product law is not affine in q. The correct argument uses affine marginal probabilities and an additive log-MGF. No mixture-of-products shortcut was used.
4. Uniform expected-work truncation looked possible, but was unnecessary. A better extension uses the reference q*=rho, giving one-coin law domination by 1/rho and fixed-product domination by rho^-n. Finite product partitions approximate a clipped terminal output uniformly in q while preserving the original local stopping work. The formal-foundations agent supplied this simplification.
5. Shared random selection of the local design does not automatically satisfy the convex-family hypotheses; the independent adversarial reviewer supplied a counterexample to the required log-MGF concavity. This extension is parked rather than asserted.
6. Parent suggested a separate Poisson-count route: use reference intensity lambda/rho and marks from q*=rho. Its finite likelihood-ratio bound permits uniform finite count-partition approximation; count intensities are affine in q, so Poisson exponential-family convexity applies. The TeX includes the complete proof. This addresses clipping of the existing Poisson upper, without extending to arbitrary random counts or shared designs.

## Evidence and scope

Initial status: paper-proof candidate, submitted to independent agent review. No new Lean statement or numerical theorem is claimed. The affine-estimation principle is existing literature; this note claims its application and the resulting stronger restricted critical characterization, not discovery of that principle. The earlier additive proof is pinned to commit d75c775 and its exact SHA256 in the TeX. Agent review is not external specialist review, and model diversity is not guaranteed.

## Question exposed by the intermediate result

The intermediate result left open whether shared pre-observation random selection of local experiments, or true cross-coin feedback, can attain the smaller unrestricted Psi rate at alpha=2. The direct comparison establishes neither possibility nor impossibility. Its strongest failed step is log-MGF concavity after general design randomization. The subsequent universal-pair argument below supplies a different route; the canonical strongest result and its current status are in `unrestricted.tex`, not this historical attempt paragraph.

## Subsequent full-model route (conditional, under review)

Parent identified that the previous entropy argument charges all work at q=0. The formal-foundations agent checked a stronger small-bias bound V E_0 T >= c rho L H on the capped parameter set 0 <= q <= 1/2. At parent's request, this construction role now also owns the shared `affine_comparison.tex` fragment. It contains the finite-experiment proof and a conditional extraction of a common hard pair for every capped one-coin policy.

The extraction uses actual Hellinger saddle duality, not an inference from RMS alone. For a fixed policy, repeat it n times and use the base-cost additive reduction to force a separated pair of high affinity. Choose n proportional to rho L H/(delta^2 E_0 T). For any finite collection of policies, reveal a mixture index and apply the result to that capped mixture; finite-simplex minimax gives a pair hard for the collection. Weak-star compactness and the finite intersection property give one pair for every capped policy. The full observed seed/stopped history reduces exactly to the finite sufficient statistic (stopping time, head count), establishing continuity and retaining the true observable experiment. Parent owns the fresh-coin population reduction and unrestricted theorem; this fragment alone does not establish that result.

The independent source review also identified Polyanskiy--Wu arXiv:1902.05616v2 Theorem 1/Proposition 4 as direct quadratic-risk affine-estimation prior art. The TeX now credits it explicitly; no general RMS comparison novelty is claimed.

The shared affine fragment at SHA256 `c243a6ad355aeabb2fea3df195166faf066b95b4e5778e3bc02512d61a80f7c2` received separate mathematical passes from the adversarial and formal-foundations agents, with no blocking finding. The latter authored the independent base-cost input and reviewed only the new comparison/minimax bridge. Neither pass is external specialist review or Lean verification.

A further finite-prefix direct-sum proof was supplied to parent for independent audit: for each compatible observable leaf and fixed policy seed, factor endpoint probabilities into local-word probabilities p_i^- and p_i^+. The midpoint qbar gives local factor m_i=(p_i^-+p_i^+)/2. If z_i=sqrt(p_i^-p_i^+)/m_i, the global affinity integrand is (product m_i)(product z_i), and the hybrid-i affinity integrand is (product m_i)z_i. The elementary inequality 1-product z_i <= sum(1-z_i) gives a direct Hellinger sum bound. Parent owns its final observational-model statement, implementation and proof; this ledger does not certify those remaining steps.
