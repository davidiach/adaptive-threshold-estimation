# Independent adversarial review: quadratic margin

This reviewer owns this file and `sources.md`, and does not author the principal specification or proof. The review is an independent agent pass, not Lean checking or external specialist review; model diversity is not guaranteed. The preceding alpha>2 result is preserved unchanged.

## Target under review

The proposed target is a universal-constant upper bound

    R_(mu,rho)(B) <= C min{rho, sqrt[rho(1+log(1/rho))]/(a sqrt B)}

for the exact law mu((0,d])=(d/a)^2, 0<d<=a<=1/2, 0<rho<=1/4 and B>=1. The algorithm may know a,rho,B but observes neither a coin's magnitude nor sign. The class contains every measurable q with integral q dmu<=rho; theta is not supplied. Work means the uniform expected number of requested Bernoulli observations, allowing creation, revisits, interleaving and unbounded stopping.

**Population target status:** conjecture/open. No impossibility for all eligible algorithms has been established in this review. A sharp theorem for the entire unbiased single-coin class is reviewed below; it is a distinct, restricted conclusion.

## Analytic checks and hostile cases

1. **Target and saturation.** The existing variational formula gives rho=(t/a)^2 u, u=1+2log(a/t), hence u=1+log(u/rho). Writing L=1+log(1/rho), one has L<=u<=2L. For h<t, Psi(h)=h t(u+1)/a^2-h^2/a^2; for h>=t it equals rho. Thus the proposed scale and transition B of order L/(a^2 rho) are consistent with Psi, jointly in a,rho,B. This algebra does not produce a statistical algorithm.
2. **Small-gap concentration.** q=1 on (0,a sqrt rho] is admissible. In particular, the inequality E[q/D^2]<=rho E[D^-2] is unusable, and E[q/D^2] actually diverges in this example. Every finite-work claim must use a capped or otherwise integrable quantity before taking real expectations. A known upper bound on theta cannot be substituted for theta itself.
3. **Long interval of hard scales.** The variational extremizer w(d)=min(1,t^2/d^2) spreads equal rarity mass per logarithmic scale above t. This tests constructions only tuned to the bottom-rho region. For critical rho->0 there are order log(1/rho) relevant dyadic scales, even though a is known.
4. **Joint limits.** At B=1 or as a->0 with B fixed the zero-work estimate rho/2 gives the saturated answer. At fixed rho>0 and B->infinity, the desired rate is B^-1/2 without a logarithm in B. A proof with a growing log B factor does not establish the target. At a=1/2 the exact law has no endpoint atom; an envelope extension admitting endpoint atoms needs a separate endpoint check.
5. **Separate uniform quantities.** A per-q product estimate cannot replace separately uniform work and second-moment estimates. Poisson replication must use a proven deterministic work bound and its variance involves E[Y^2], not Var(Y). The low-intensity case must remain covered.

## Scale-discovery attacks and their limits

The alpha>2 proof cannot simply be integrated at alpha=2: its inverse-square and inverse-square-times-log moments diverge. The concurrently present `research/2026-10-27-minimax-audit/theorem/critical.tex` supplies a capped-classifier upper bound of order sqrt[rho L(1+log L)/(a^2 B)]. This reviewer read that file as context and neither modified it nor inherited its stated review status.

Uniformly correct single-coin sign classification has a real scale-discovery obstruction. The finite gap-entropy theorem of Chen--Li--Qiao is stronger for this purpose than an informal invocation of the law of the iterated logarithm; see `sources.md`. It threatens attempts to remove log L merely by changing likelihood-grid weights while retaining pointwise correctness on every relevant scale. It does **not** refute the population target: an eligible estimator need not classify individual coins correctly, may use signed corrections and the known all-negative baseline, may have gap-dependent error, and may depend on B and rho. No reduction from general population estimation to a uniformly correct SIGN test has been supplied. Restricted-family optimization or failure must remain explicitly restricted.

## Acceptance gate

A matching claim will require the actual observable procedure, all parameter dependence, measurable realization, finite expectations before signed interchange, exact budget calibration and control of the global-rarity extremizers. Any lower bound asserting an extra iterated logarithm must apply to all admissible fresh-coin algorithms, rather than only a classifier family. Numerical searches alone cannot supply either conclusion. A final source hash and findings will be appended after a complete candidate is shared.

## Complete-proof pass: sharp unbiased single-coin product

Read `construction.tex` in full at SHA-256 `9fdcba82787262597fc38cecf097fc68de01947a22c45d3d54d255356cc7da6e`. No blocking mathematical defect was found. The claim is now stronger than a bound for one classifier family or one normalization of its moments: at the fixed exact quadratic law with a=1/4, the infimum over all admissible unbiased single-coin procedures of either VW or MW has order rho L(1+log L), where L=1+log(1/rho), M is the separate supremum of raw second moments, and V is the separate supremum of variances. Constants are universal; the procedure may depend on rho. This is a paper-proof review, not a Lean result.

Checks in this pass:

- The admissible class explicitly forbids additional genuine reservoir coins and latent information, while permitting arbitrary signed outputs, independent seeds, unbounded observable stopping and no-observation thinning. Thus it includes much more than the likelihood-dictionary family, but it excludes general population algorithms.
- The choices q=0 and q identically rho establish integrated second moments and work for both signs. Scaled indicators of arbitrary measurable sets are admissible and imply the pointwise conditional response identity m_+-m_-=1 almost everywhere. No pointwise rarity assumption is used.
- Conditioning on the seed event of requesting a first observation is valid. The active procedure Z=pY+c retains unbiasedness; its second moment obeys the completed-square bound pM+(1-p)theta^2. The inequalities m<=4pM/3, mW_Z<=4MW/3 and MW>=3rho/4 follow. This removes a real thinning loophole and makes the theorem apply to every variance/work allocation.
- The top-rho set argument bounds the positive conditional-moment exceptional set. The negative exceptional set has mass at most 64m. On their complement, the two conditional output means lie on opposite sides of 1/2 with margin at least 3/8. At most 513m/rho same-coin restarts produce the claimed constant-error sign test. Conditional independence and finite work are justified using unused iid suffixes, without replacing the latent magnitude between restarts.
- The entropy lemma is proved for the needed finite separated Bernoulli gaps, rather than assumed from a Gaussian theorem. It uses only deterministic finite-prefix KL, Pinsker, Markov and a bounded overlap count for stopping windows. The fair-coin reference can fail to stop. The numerical constants, including the implication for K>=ceil(exp(32)), check; that very large threshold affects only the universal lower constant.
- Each selected annulus retains at least half its mass after removing the exceptional set. Selecting one finite-cost gap per annulus gives the displayed integrated-work bound. The coefficient 3648 and the implicit bound in equation (10) were recomputed. Splitting MW above/below sqrt(rho), then extending over the remaining compact rarity interval using MW>=3rho/4, proves the stated all-rho order. The comparison M<=4V/3 transfers the lower bound to variance.

Requested precision correction: define the signed conditional mean only after the nonnegative second-moment bounds prove it finite almost everywhere, assigning an arbitrary value on the null complement. Calling a potentially undefined signed expectation an extended moment is unnecessary. The algorithm convention should also make explicit that nontermination corresponds to T=infinity. These are statement/definition clarifications, not a counterexample to the displayed argument. Final acceptance and the final source hash follow after amendments.

## Independent check of the upper dependency

Independently read the relevant upper-proof sections in `research/2026-10-27-minimax-audit/theorem/critical.tex` and recomputed its constants at SHA-256 `0e8b9eaf762b3b09fa0d92ce1a036c2ceea8c12d00a5eea8286b852f36a81536`. That file belongs to concurrent pre-existing work and was not modified by this reviewer. Its prior review label was not taken as a substitute for this pass.

The capped finite classifiers have integrated error at most (5/2)rho epsilon_j. The global-rarity work bound uses the top-rho integral of a capped inverse square; no divergent inverse-square moment is converted into a finite real quantity. For adjacent levels, two successive observation blocks belong to the same latent coin. Their disagreement is controlled by their respective errors about that same sign. The single-term telescope therefore has M<=165rho/56 and separately W<=1350a^-2 L(1+log L), with integrability established before the signed telescope. These are admissible single-coin bounds. At a=1/4 they provide the universal-constant upper product required for the sharp theorem. Poisson aggregation in the imported file is not needed for this product conclusion. Reuse must retain attribution and pin the dependency, or reproduce the needed argument in the new note with attribution.

## Review of the parked reduction discussion

Read `alternative.md` and checked the finite-trigger positivity proof and telescope constants. The final reviewed text at SHA-256 `d9db87a971133037f49ff66cceead60a9ab8dcd306fd0225e9ce26c53b9cd32b` corrects the earlier impossible request for a gap-independent positive separation produced solely by a vanishing-mass component. The finite-trigger lemma follows from nonnegative finite-word probabilities and interior Bernoulli full support. It is familiar Bernoulli-factory mathematics; the primary-source overlap is recorded in `sources.md`.

The discussion properly limits dictionary-weight optimization to its proof certificate and limits the trigger obstruction to a fixed simulator valid at arbitrarily small gaps. It does not rule out a simulator tailored to a known finite gap set. Neither that discussion nor the single-coin theorem supplies an all-algorithm minimax impossibility.

## Separately reviewed extension: small uniform bias

Read the complete separate extension in `construction-notes.md` at SHA-256 `a9b27c6939374a95ee120b7355a36abc80ce15f4a518a79304a21a1ce6d0304f`. **Accepted on this paper-proof pass**, with no blocking mathematical finding. It broadens the product characterization to single-coin procedures with uniform absolute bias at most rho/64; it does not change the observation model or authorize an all-algorithm conclusion.

The conditional response need no longer equal one. Comparing q identically rho with q=0 instead gives its integral at least 31/32. Total variance therefore gives V>=2rho/3, and the stated M<=3V/2 follows uniformly for rho<=1/4. Active normalization preserves the actual expectations and the bias guarantee, with m=pM+2rho^2, m<=4pM, mW_Z<=4MW and MW>=rho/6. The proof should explicitly state p>0: a no-observation output has the same expectation under theta=0 and theta=rho and cannot satisfy the two bias requirements.

The new response exceptional set is controlled by choosing q to be the indicator of any rho-mass subset, so the argument still uses the global rarity class. The combined exceptional mass bound 67m, threshold 3/8, repetition bound 1282m/rho, annulus mass 134m, and safe final coefficient 30000 all check. Applying the already proved finite-grid lemma and the same compact-rarity extension yields the claimed product lower bound; the unbiased construction provides the upper bound in the enlarged class.

For a fixed-count unprojected average or independent Poisson sum, the separate uniform product lower bound does imply the stated worst-case variance obstruction at its expected budget. It does not automatically survive clipping or nonlinear aggregation. The extension correctly excludes those conclusions. A distinct theorem in the TeX note is preferable to leaving this strongest mathematics only in the attempt log; any such transcription will be checked before final source acceptance.

## Lee--Valiant transfer audit

Reinspected the primary Theorems 4--5 and Section 7 optimization and comparison proofs; see `sources.md`. No applicable cost-preserving reduction from the entire fixed-mu nuisance class was found. A simple obstruction to directly using their scalar path is that fixed conditional magnitude laws nu_+,nu_- cannot keep t nu_+ +(1-t)nu_- equal to the same mu at two distinct t unless nu_+=nu_-=mu. That special path has constant q. Their two averaged response constraints do not imply the almost-everywhere response used by this proof, and their hard per-coin cap is a separate restriction. This is a diagnosis of the attempted import, not a proof that no more general reduction can exist.
