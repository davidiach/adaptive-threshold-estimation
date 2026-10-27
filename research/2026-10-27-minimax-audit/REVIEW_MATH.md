# Adversarial mathematical review

Reviewer: the distinct `adversarial_formal` agent in this run. This is not external
peer review; independence of model or training is not asserted. Review was of
current working-tree sources at HEAD `ddf950122776a059e62c808021bbd2b59c39f0b0`,
including preexisting uncommitted Route A research. No historical source was edited.

## New critical-alpha=2 construction

**PROVED-ON-PAPER after agent review, not FORMALIZED.** The theorem agent's
`theorem/RESULT.md` was reviewed equation by equation. No blocking error was found
in the claim, for `L=1+log(1/rho)` and `H=1+log L`,

`E Y=theta`, `E Y² <= (165/56)rho < 4rho`,
`E T_Y <=1350 a^-2 L H`,

uniformly over the global rarity constraint and the alpha=2 margin envelope.
The reviewer independently checked these vulnerable steps:

- The event of a wrong answer at the deterministic majority cap is a subset of
  the full-tape wrong-majority event. Integrating `exp(-2ND²)` costs at most
  `1/(2Na²)` under the envelope. No conditional independence of stopping and
  majority error is used.
- For `x=min(d,a)>=N^-1/2`, the chosen reference index lies in the finite tested
  family. The true-sign drift is at least `(2/3)x²`. At smaller gaps the cap alone
  gives the proposed work envelope.
- Rearrangement bounds the positive work using `integral q<=rho`; it does not
  substitute the invalid pointwise condition `q<=rho`. Concentrating all positives
  at the smallest gaps is included.
- The factors 7 and 5 in the scalar inequalities, then 225/2 per classifier,
  225 per increment, and 1350 after averaging the geometric level, are valid
  deliberately loose universal bounds.
- The second moment is exactly bounded by `(35/16+85/(16*7))rho=165rho/56`.
  Absolute summability is established before interchanging signed expectations.
- Independent Poisson replication gives variance `E Y²/lambda`, not
  `Var(Y)/lambda`, and expected work still adds when Y and its own work are
  dependent. Clipping does not preserve unbiasedness.
- The exact alpha=2 candidate calculation, including saturation and joint
  rho,B behavior, has the stated universal comparisons.

The reviewer requested an explicit argument that the second observation block,
which starts after a random bounded stopping time of the first block, has the
same iid conditional law given `(D,S)`. The author added the correct finite
stopped-prefix conditioning proof. Merely saying "disjoint blocks" would not
by itself have justified that step. The confidence procedure should explicitly
choose the constant branch when its deterministic radius is smaller.

The upper/lower RMS gap is `sqrt(1+log(1+log(1/rho)))`, conditional on the inherited
arbitrary-law lower bound. The logarithm is not a universal constant and has
not been proved necessary. Neither alpha=2 matching nor arbitrary-law matching
is established.

The finite-level arbitrary-law upper bracket appended to that file was also
reviewed. The bounded functions make all integrals finite even with infinite
inverse moments; fractional cutoff allocations handle atoms; Poisson allocation
produces the stated variance-work product. This is a valid constructive bracket,
not a new complete characterization or priority claim.

The subsequent bounded-channel extension was reviewed as well. For X in [0,1],
the multiplicative factors `1 +/- 2r(2X-1)` are positive; the wrong factor has
mean `1-4rd`, while log concavity places the correct log factor above its
endpoint chord and gives the same drift lower bound. The upper proof therefore
transfers. It does not transfer a Bernoulli minimax lower bound: deterministic
observations of the conditional mean reveal the sign immediately. The derived
uniform-noise example has variance 1/48. The observed-state parametric example
has `Var(Z-8(X-1/2))=1/12`, hence target-estimator variance `1/(48n)` at cost
2n. Its gap cdf is exactly 8t near zero (for t<=1/16 uniformly over the given
parameter interval), so it supplies a concrete boundary to interpreting a
linear marginal gap law as an unstructured lower bound.

## Inherited arbitrary-law lower argument

**PROVED-ON-PAPER with a published external input; no counterexample found.**
Inspected the actual argument in
`inputs/next-phase/report/research_note.tex`, from the single-coin lemma through
the hybrid decomposition and `thm:PsiLower`. Also inspected Lee--Valiant v3 HTML,
Lemma 18 and its proof, Corollary 19 and the following reduction (27 October 2026):
<https://arxiv.org/html/1904.09228v3>.

The original-prior expected-work version of Corollary 19 is indeed stated.
Its small prior, increment, gap, and relative-increment restrictions are met by
`u=bw`, `v=c0 min(w,h sqrt(w)/d)` after fixed universal choices. The extension
to gaps bounded away from zero reveals the sign at the first requested flip
and is the repository's own data-processing argument. It is not part of the
literal small-gap source assertion.

At a finite prefix the local hybrid likelihood ratios are uniformly bounded,
have mean one under the baseline, and multiply to the full likelihood ratio.
Adaptive local sequence lengths do not destroy this factorization: a fixed
path has fixed queried labels and outcomes, so integration factors by latent
coin. Canonical indexing by first observation is necessary to limit the sum
to at most n iid coins. Conditioning on one coin's D and simulating all other
coins under the baseline gives parameter-independent external randomness in
the single-coin comparison. Summing its expected local observations recovers
total work. No free selected-magnitude oracle is invoked.

The proof remains external to Lean. In particular the existing symmetric
`1/2 +/- eta` information theorem is not the rare-prior Corollary 19.

## Inherited optimizer and power regimes

**Optimizer: exact FORMALIZED scope is in FORMAL_COVERAGE.md.** The paper's
cutoff existence, atom conventions, and piecewise objective agree with the
actual `Tier3.ArbitraryLawOptimizerStatement`. The optimizer supplies no
statistical algorithm or minimax upper bound. For rho bounded away from zero,
constant feasible allocation gives the stated comparison with the v4 modulus;
fixed-gap reduction and saturation agree.

**Power margins below two: PROVED-ON-PAPER; no blocking gap found.** Reviewed the
integrated envelopes, dyadic starting-level rounding, both moment sums, and the
two-success wrapper in the imported note. In the wrapper, pilot values must be
discarded and fresh production samples used. A coupled increment costs no more
than its maximum cap, because both classifiers use the same observed prefix;
the looser sum-of-mean-costs bound is compatible with this cap. Constants depend
on alpha and cannot be held fixed as alpha approaches its boundaries.

**Power margins above two: inherited PROVED-ON-PAPER; no blocking gap found.**
Reviewed the preexisting Route A construction, drift/overshoot estimate,
finite computability of likelihood tests, global-rarity layer-cake estimate,
separate moment/work bounds, and fixed-gap simulation reduction. The controlling
quantity `rho^(1-2/alpha) log(1/rho)` is uniformly bounded for each fixed alpha>2;
this does not extend to alpha=2. The Poisson replication works even below one
expected replicate. Its constants depend on alpha, and the new run did not
originate that theorem.

## New negative result: the naive countable stopping extension is false

**DISPROVED by a complete paper counterexample.** Extending the current Tier 3
conclusion "finite expected work under plus implies termination under both"
to an unbounded reservoir is invalid. Fresh deterministic-gap coins with sign
priors 5/8 and 3/8, stopped at the first +1 random-walk crossing, give
`E_plus T=4` but minus nontermination probability `2/5`. An interior-gap variant
gives `E_plus T=8` and minus nontermination probability `2/9`.

The proof and corrected finite-prefix-to-terminal-testing bridge are in
`formal/stopping_bridge.tex`. Separate finite-work assumptions under both laws
suffice for the minimax application. This correction does not disprove the
existing finite-family theorem, the candidate Psi, or the inherited minimax
lower theorem, whose uniform budget supplies both-law admissibility.
The random-walk identities themselves are classical, not claimed as new.
After this counterexample was derived, concurrent external Tier 5 source work
was observed; its `CreationStopsStatement` already correctly makes only a
one-law stopping conclusion. The example supplies an explicit boundary for
that scope rather than a newly discovered defect in the Tier 5 specification.

`formal/check_stopping_counterexample.py` checked 202 finite-horizon exact
rational identities through cap 101, retaining unresolved mass. Infinite-horizon
probabilities and the mean 4 come from the paper generating-function proof,
not that finite calculation. No Monte Carlo seeds are involved.

## Nested lower-bound quantifiers

Inspected v4's `prop:continuous` directly. Its scale-dependent partitions and
sign priors can all be placed inside the fixed class of deterministic conditional
Bernoulli models on U uniform in [0,1], with the pushforward of D exactly uniform
on (0,1/4] and no cross-state regularity constraint. The number of cells is not
bounded by the class definition. Thus the valid quantifier order is: fix this
one class; for each requested accuracy choose a finite hard subfamily inside it;
then bound every uniformly valid algorithm on that subfamily. It would be false
to advertise this as a fixed finite-partition asymptotic or as a lower bound
for an added smooth-regression class. The source comparison of the moment and
density assumptions is recorded separately by the literature agent; the formal
source tree contains no complete Lean counterpart of this observed-state proof.

## Remaining obligations

The parent's supplemental known-fixed-gap/unknown-rho deconvolved-majority
construction in `adaptation.tex` was also checked. With odd
`m>=log(2B)/(2d²)`, the false-positive probability is at most `1/(2B)`; in the
nontrivial branch `B>=2m`, deconvolution variance is at most
`8m theta/B+4m/B²`. Its confidence interval follows from iid Bernoulli
Hoeffding bounds and is computable from the known gap and observed majority
bits, subject to certified arithmetic for the binomial probability. This is a
sufficient qualified guarantee only; neither logarithm nor additive floor is
claimed optimal. The deterministic endpoint genuinely escapes the inherited
unknown-rarity impossibility.

No proof of the arbitrary-law matching upper bound; no proof that the critical
iterated-logarithm loss is necessary; no completed Lean iid countable-reservoir
realization; no formalized rare-prior single-coin inequality; no external
specialist review; no cleared priority claim. The old finite-family stopping
assumption must not be silently generalized when creating new specifications.
