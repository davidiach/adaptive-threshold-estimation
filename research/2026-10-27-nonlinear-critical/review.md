# Nonlinear aggregation: adversarial review

Status: source triage and failure tests; no candidate theorem accepted yet. This reviewer owns only this file and `sources.md`, and does not write the principal specification or proof. Prior locks and reviewed sources are preserved. Reviews are by agents; model diversity and external specialist independence are not guaranteed.

## What the source actually supports

The Juditsky--Nemirovski product-experiment result is relevant to a deterministic finite collection of independent coin experiments, including heterogeneous local policies and independent local seeds. Their term affine means a sum of arbitrary allowed component functions, rather than a function linear in the raw flips. This distinction makes their comparison potentially useful for the inherited additive lower bound. The exact source assumptions and accessible statements are recorded in `sources.md`.

The published confidence-risk conclusion alone is insufficient. An estimator can have excellent fixed-confidence accuracy and arbitrarily large or infinite second moment. A valid RMS transfer must explicitly extract tail or moment bounds from the proof's exponential-moment construction, including control of its scale parameter. Clipping that constructed sum would remove the moment difficulty but would also leave the additive class, so cannot silently replace this step.

## Failure tests for overly broad imports

1. **Joint convexity is not automatic.** Each coin transcript law is affine in q, but a product of two such laws is generally quadratic, and the joint family need not be convex as a set of measures. Donoho--Liu cannot simply be applied to that joint family as though it were an affine mixture. Juditsky--Nemirovski instead uses its explicit product construction and concave log moment-generating functions.
2. **Shared seeds are a real additional case.** A mixture of good product experiments need not remain good. For example, let U be fair. If U=0, collect no data and take the seed-dependent offset log(10). If U=1, observe two independent Bernoulli(p) variables and take log(2) times their sum. The exponential moment is G(p)=5+(1/2)(1+p)^2. Its logarithm has second derivative [5-(1/2)(1+p)^2]/G(p)^2, strictly positive on [0,1]. Thus the requisite concavity fails. This example even embeds in the present model along q(d)=t: at a=1/4 the first flip of each fresh coin has p(t)=1/3+t/3. It refutes closure of the imported assumption, not affine near-optimality or the population conjecture itself.
3. **Conditioning is not uniform derandomization.** A bound on sup_q E_U loss does not yield a seed value with small conditional loss simultaneously for every q; the same issue applies to conditional expected cost. A random global count or design cannot be conditioned away without a separate theorem. Independent local randomization is different and may be included in each component transcript.
4. **Finite-dimensionality and positivity need proofs.** The nuisance class is infinite-dimensional. A finite transcript partition gives a finite vector of affine probabilities, but the image together with theta must be shown compact and convex. Zero cells must be removed or handled, and positive probability under one reference cannot simply be assumed to imply a uniform positive lower bound without an argument based on the actual finite-prefix experiment.
5. **Pointwise approximation is insufficient.** Removing transcript truncations or finite partitions requires uniform risk control over all q. A fixed finite product admits useful common-reference domination; an unbounded or common-seed count does not inherit its fixed product constant. Any limiting argument must state exactly which count and seed restrictions it preserves.
6. **Cost must stay in the original experiment.** The statistical comparison changes terminal postprocessing of already acquired transcripts. If it instead changes a stopping policy or selects a q-dependent design, the original uniform expected-work bound need not survive. No deterministic cap may replace an expected budget without accounting for its effect on risk and cost.
7. **Identification should not be presumed.** Different q may have identical selected transcript probabilities and different theta. Encoding theta as part of the convex signal coordinate allows a noninjective observation map; treating theta as an automatically well-defined functional of the observable law would miss this case.

## Current acceptance gate

The smallest plausible extension is a complete RMS comparison for fixed finite independent stopped-coin experiments, with local seeds, unbounded finite-mean stopping, arbitrary terminal nonlinear aggregation, and exactly the original expected-work bound. It must include the finite-dimensional image argument, positivity or smoothing, moment control and a uniform extension from finite transcript partitions. The resulting sharp rate may then be inherited from the reviewed additive theorem. Shared global designs, random counts and cross-coin feedback require separate treatment; no acceptance is implied for those cases.

## Proposed Poisson extension: preliminary audit

The parent subsequently proposed a special random-count extension: independent Poisson replication of one fixed iid marked single-coin experiment. This is distinct from the general shared-design mixture whose goodness fails above. The proposed domination and reduction pass the following checks, but acceptance still requires the written source.

For the reference single-coin law P_rho obtained from q identically rho, the affine mixture representation gives P_q<=P_rho/rho. For actual Poisson mean lambda, compare ordered marked observations with a reference having count mean lambda/rho and marks P_rho. The count likelihood contributes exp(lambda/rho-lambda)rho^N; the mark likelihood is at most rho^-N. Thus the actual observation law is uniformly dominated by the reference with constant exp(lambda/rho-lambda). This constant can be large, but is only used to make a chosen approximation sufficiently accurate. The reference experiment is not executed by the candidate algorithm and must not be charged as, or silently replace, its actual work.

After clipping an arbitrary original output to [0,rho], iid exchangeability permits averaging over all orders at each finite count. This averaging uses no unknown q. Finite mark partitions yield independent Poisson counts with affine intensities, fitting the separate good-Poisson example. An affine function of those counts is a constant plus a finite-valued function of each actual coin transcript, and so belongs to the inherited additive class. The finite weights and finite Poisson mean imply its component square-sum integrability, while the acquisition policies and expected work remain the original ones. Uniform approximation, positivity, compactness and measurability still need to be present in the complete proof.

The iid mark condition is essential to this particular argument. It does not cover a general count law, a count-dependent family of local policies, shared design randomization, or feedback across coins. No such extension is accepted from this preliminary calculation.

## Complete intermediate dependency reviews

Read the full proposed Poisson extension in `alternative.md` at SHA-256 `8abdcad87225dcb042399f8ff08471f57081cc8207bd9fbd1e2b43a9e093287e`. Its constant-21 RMS comparison, uniform reference domination, finite mark partitions, artificial Poisson smoothing, and removal of artificial counts by averaging have no blocking finding. The fixed iid kernel and standard Borel assumptions are explicit. A joint-in-parameter Radon--Nikodym version is unnecessary; the density calculation may be performed separately for each q. This is acceptance of that stated intermediate mathematical argument, not its unproved final section about a universal hard pair.

Read the complete strengthened entropy lemma in `base_cost.md` at SHA-256 `58a235efbd06757826ad688f246a0f03d9ea92a965444136c270d00cea19f969`. **Accepted on this paper-proof review:** over X_rho={0<=q<=1/2, integral q<=rho}, every single-coin procedure with uniform bias at most rho/64, finite uniform second moments and finite uniform work has M E_0T >= c rho L H; likewise with V in place of M. The work in the conclusion is genuinely all-negative work.

The adaptation preserves the variance floor because q identically rho remains admissible. Conditioning on the first-query event gives m<=4MW_0 and m(W_0/p)<=4MW_0 without introducing a supremum of work. The capped nuisance class is used through q=(1/2)1_E on sets of mass 2rho. This bounds the two additional exceptional sets by 2rho each, giving total bad mass 70m; annulus mass 140m then retains half its mass. The restart and annulus constants, finite conditional work under both signs, and final all-rarity extension check. The inherited finite-grid entropy lemma remains the specified reviewed paper dependency. This review does not itself establish universal hard pairs, interchange a minimax optimization, or transfer the result to population interaction.

## Universal-pair proposal: unresolved acceptance gate

The parent subsequently proposed a possible unrestricted lower bound using the strengthened all-negative cost. This is not accepted from a sketch. The required new steps are: a hard pair of prescribed target separation for every capped one-coin policy with the correct E_0T normalization; a single pair working for all such policies; a finite-prefix adaptive direct sum; and passage to unbounded finite-mean stopping. The pair must remain in X_rho so its midpoint dominates the all-negative law by a factor two. The midpoint simulation used by a hybrid procedure must be an independent proof seed fixed under both endpoint hypotheses, never actual latent access.

For the minimax interchange, a finite-policy simplex followed by compactness and the finite-intersection property avoids an unspecified topology on all randomized procedures. Bounded-depth stopping trees have finitely many leaves, so their Hellinger distances depend continuously on finitely many affine q-moments. The policy-specific hard-pair premise, including constants and small-separation range, remains essential and is not implied by convexity alone. The primary Lee--Valiant input and its exact limitations are recorded in `sources.md`.

## Complete hard-pair dependency review

**Accepted on this paper-proof pass:** `base_cost.tex` at SHA-256 `6c02a467ac9a8b989ccb3e3618a9bb567e332ed1d3830d70fca27c01e5e3265a`, and `affine_comparison.tex` at SHA-256 `c243a6ad355aeabb2fea3df195166faf066b95b4e5778e3bc02512d61a80f7c2`.

The base-cost TeX was read completely, including its reproduced finite-gap entropy proof. It faithfully states and proves the reviewed Markdown adaptation. The deterministic-prefix KL comparisons, stopping-window overlap, good-gap selection and all-rarity extension contain no blocking defect.

The affine fragment was also read completely. Its finite-experiment RMS comparison follows from the stated continuous convex--concave saddle problem. The likelihood-ratio minimizer lies in the additive function space. The affinity modulus uses the full product law; the same constructed estimator has exponential tails with scale at most R/log(2), so no confidence guarantee is silently substituted for RMS. The constant 12 is conservative: the proof bounds the squared comparison factor by 136<144. Nonattainment is handled by arbitrary positive slack.

For a capped one-coin policy, the full seed and stopped word are conditionally ancillary given (T, number of heads): every seed/word cell with those values has the same q-dependent likelihood multiplier. Thus the finite statistic preserves Hellinger affinity exactly, rather than merely decreasing it. Its positive probabilities and base cost are affine continuous functions of finitely many q-moments. This validates continuity and convexity on the weak-star compact parameter pair space.

The hard-pair proof applies the all-negative product bound to a genuine one-coin index reduction, with base cost exactly E_0T_A and variance at most (7/3)n times the additive risk squared. Bounded component functions justify all moments. The zero-cost case is now handled before division. The saddle lower bound, integer choice n=floor(beta^2 J/(4 delta^2 w)), separation at least 2delta in that branch, and the large-cost trivial branch all check with c_delta=beta/2 and C_H=8/beta^2.

For the universal pair, revealing a finite mixture label makes both Hellinger distance and all-negative work affine in the mixture weights. The finite-simplex minimax orientation is correct, and the pair constraints are closed in a nonempty compact space. The finite-intersection argument therefore yields one pair before all capped policies. This is stronger than choosing a different pair for each policy and does not exchange arbitrary infima without justification.

The accepted fragment's universal-pair lemmas are conditional on the exact base-cost input, now supplied by the separately reviewed TeX. Acceptance here does not yet certify the parent's full population wrapper, its observational model, the adaptive reduction, the unbounded-stop limit or the claimed comparison with Psi. Those require the final integrated proof.

## Full population proof: mathematical acceptance

**Accepted on this independent agent paper-proof review:** the complete `unrestricted.tex` proof at SHA-256 `9ecff9c7534ba883bd6d1fdfc6340c70956486ac666f219ed991dba879d188d6`, with the accepted base-cost and affine fragments above and `upper_bound.tex` at SHA-256 `e4d8fd72f87fe0bf590b1cbbf8a61d9736f1402ba5e6a364df834cc810737fbc`. This acceptance concerns the mathematical content; the draft's provisional status wording and explicit prior-art credit were requested to be updated before the final checkpoint. Any such final source identity will be recorded below.

Read the entire wrapper and upper appendix. The strongest statement is now, for the single fixed law mu(dd)=2d/a^2 dd on (0,a] with a=1/4,

`R_(mu,rho)(B) = Theta(min{rho, sqrt(rho L H/B)}),`

where L=1+log(1/rho), H=1+log L, uniformly for 0<rho<=1/4 and B>=1. Here R ranges over all measurable observable algorithms in the ordinary iid fresh-coin experiment, including nonlinear outputs and data-dependent creation, revisiting and interleaving, subject to a separate uniform expected flip budget. This supersedes the earlier open-status entries for this exact critical-law question; those entries accurately record the earlier research stage. No analogous claim for arbitrary other laws follows.

The decisive review checks were:

- Numbering coins by first observation preserves the iid reservoir when selection and free creation cannot inspect latent states. At a K-flip prefix there are at most K observed coins; no globally fixed coin limit is imposed.
- Conditional on the original seed, each finite leaf probability factors by the actual observed word of each coin, even with interleaving. The midpoint and every one-coin hybrid define normalized finite experiments. The product inequality therefore gives the Hellinger direct sum with factor one, using H^2=1-affinity.
- The hybrid simulation's larger seed is independent of its genuine coin and is fixed under both endpoint hypotheses. The actual hybrid transcript is a measurable function of that seed and the genuine stopped observations. Data processing thus has the required upper-bound direction. The universally hard pair precedes every capped policy and therefore covers these pair-informed proof reductions; no actual unknown endpoint is passed to a policy.
- The cap q<=1/2 applies only to the lower-bound adversary. Its midpoint latent law dominates half the all-negative law, so each hybrid's null cost is at most twice its midpoint cost. Summing the latter charges each genuine flip of the original midpoint experiment exactly once. The bound uses the original uniform expected budget at this admissible midpoint.
- The same pair works at every cap. The terminal-event approximation uses endpoint almost-sure termination and vanishing tail probabilities, without differentiating an infinite transcript law or invoking an unbounded-stopping KL chain rule. The chosen separation gives prefix H^2<=1/8, terminal TV<=1/2, and RMS at least delta/4 by the two-point test.
- The reproduced upper retains its separately finite moment and work bounds and uses one genuine coin for the adjacent-level decisions. Poisson replication has exact expected work at most B, and the known constant-output alternative supplies saturation for all budgets.
- The quadratic-law variational formula was checked directly. With u=1+2log(a/t), rho=u exp(1-u) and L=u-log u, one has L<=u<=2L. Its saturated and unsaturated branches give Psi(B^-1/2)=Theta(min{rho,sqrt(rho L/B)}). Along rho_n=exp(-exp(n)), B_n=rho_n^-2 both risks are eventually unsaturated, and the ratio is bounded below by a positive constant times sqrt(H_n), which diverges.

No blocking mathematical defect remains in this complete proof. It therefore provides a rigorous counterexample to the proposed universal C Psi upper bound, conditional only on the standard analytic theorems explicitly used in the self-contained argument. The hard pair is obtained nonconstructively by compactness; no explicit pair formula or practical constant is supplied. The proof does not conflict with the neighboring radial-submodel result, because it does not identify that radial direction as the common hard pair.

Evidence status remains **paper proof with independent agent review**. It is not Lean-checked, independently replayed in an external proof system, externally specialist-reviewed, or certified novel. The parent authored the population wrapper, the construction agent supplied the convex hard-pair argument, and the alternate agent supplied the all-negative-cost adaptation; this reviewer audited the complete argument and requested corrections. Model diversity is not guaranteed.

## Final exact bundle acceptance

**Accepted:** the final complete paper-proof bundle below. Re-read the amended main source, including its evidence status, theorem scope, attribution and bibliography. The final changes add the requested Juditsky--Nemirovski and Polyanskiy--Wu credit and update provisional wording; the reviewed mathematics and dependency files are unchanged. No unresolved mathematical finding remains.

| Source | SHA-256 |
| --- | --- |
| `unrestricted.tex` | `b00b608ca1012148934e5717d2b10ee1d1379fa312a9f5bf06a0ac1e0e6fb853` |
| `base_cost.tex` | `6c02a467ac9a8b989ccb3e3618a9bb567e332ed1d3830d70fca27c01e5e3265a` |
| `affine_comparison.tex` | `c243a6ad355aeabb2fea3df195166faf066b95b4e5778e3bc02512d61a80f7c2` |
| `upper_bound.tex` | `e4d8fd72f87fe0bf590b1cbbf8a61d9736f1402ba5e6a364df834cc810737fbc` |

This acceptance covers the unrestricted critical-law minimax characterization and the divergent-ratio counterexample to the proposed universal Psi upper bound, with all observation and expected-cost restrictions stated in the main source. It does not certify novelty, supply explicit hard-pair formulas or useful numerical constants, characterize other magnitude laws, or formalize the theorem in Lean. The parent reports a successful built-in TeX compilation; this mathematical reviewer did not treat typesetting success as proof verification.
