# Adversarial review — 27 October 2026

Reviewer: a separate AI agent that did not author the proposed main theorem, construction, or formal specification. Agent/model diversity is not guaranteed. This is not external specialist review. This file records findings as they arise; a provisional audit is not acceptance of an unreceived proof.

## Imported arbitrary-law lower bound

Reviewed the continuation's published single-coin input, bounded-ratio decomposition, and arbitrary-law lower-bound proof against the primary Lee–Valiant text (see [source audit](sources.md)). No counterexample or fatal mismatch found in that argument during this pass.

Specific checks:

- The imported expected-work bound is history-averaged, not a false history-uniform predictive-information claim.
- For large gaps, revealing the sign on the first query upper-bounds information by Pr(first query) times Bernoulli-prior Hellinger distance. The first-query event uses only external randomness and is independent of that coin's sign. This includes d=1/2.
- At a finite prefix there are at most n first-observed coins. Their transcript likelihood factors by coin even when queries are interleaved. Each hybrid density is bounded by the latent density-ratio bounds, and has baseline expectation one. This justifies cancelling its linear term in the KL comparison.
- Conditional on a reviewed coin's magnitude, the other coins can be simulated under the common baseline using parameter-independent external randomness. The lower-bound argument may reveal that magnitude for an information upper bound; no claimed upper algorithm is granted this access.
- Where w=0 the priors agree, so the apparent v²/u expression is never evaluated there. Where w>0, q0=bw and q1=bw+c min(w,h sqrt(w)/d) stay inside the integrated class after choosing universal b,c.
- Infinite stopping should be read through bounded observation prefixes and increasing sigma fields. A finite expected total observation count implies almost-sure finite observation stopping under both candidate q's because the admissible budget is uniform over the class. Any free unbounded computational delay is outside the cost-counted observational policy convention.

The result retains **paper proof using an imported theorem** status. The existing finite-coin Tier 4 proof does not formally certify this fresh-coin extension, measurable realization, or lower-bound import. The source proof's long technical single-coin estimates were inspected selectively, not independently reproduced line by line.

## Attacks on the conjectured upper bound

No all-algorithm counterexample has been established. The most plausible extra obstruction is hidden-magnitude nuisance: Psi's lower argument is allowed to reveal D, whereas an upper algorithm cannot. In particular, a two-scale law with mass epsilon at a tiny gap a and the remainder at b has a regime a<h<t where Psi is of order epsilon+h sqrt(rho)/b. A construction must tolerate the small-gap population with bias O(epsilon) without letting its screening work or false positives destroy the rarity gain. A classifier whose false-negative probability varies with d cannot be debiased by assuming a known positive conditional law.

For power margins alpha>2, the conjectured unsaturated rate is of order sqrt(rho)/(a sqrt(B)). Reusing the balanced estimator leaves negative-population noise. Symmetric confirmation of every negative introduces an avoidable-looking log(1/rho) cost, but no theorem here proves it avoidable for arbitrary q. Asymmetric screening and exact correction are the central tests for any proposed construction.

## Conditional formal bridge specification

Independently inspected `lean/ThresholdHC/ResearchRouteA/SeparateBoundsSpec.lean` before its lock, including the imported `Uniform713/Specification.lean` definitions. It states separate second-moment/work bounds and a family-level passage to separate real suprema. No blocking specification defect found in this pass.

The estimator and work functions ignore the latent first coordinate, reading only the observation sequence and independent random level. The kernel, observation map, magnitude and sign maps precede the family of latent laws in the quantifiers. The family index is nonempty; boundedness of both real ranges and nonnegativity of their suprema are conclusions. The observation assumptions include positive magnitudes and integrable inverse magnitude. The separate-moment theorem explicitly concludes square integrability and integrability of actual work before interpreting its real expectations.

This is only a bridge within the existing conditional-kernel model. It does not prove fresh-coin realizability or all-q family realization, identify K_blind without that realization, or improve the constant 713. The family theorem can refer to the companion separate-moment theorem for per-member integrability; repeating it in the family conclusion would improve standalone readability but was not judged necessary.

Post-lock audit: independently recomputed the specification SHA-256 `d114a2734cfd0164def475115d0ebb25d1ba49c7f87bb96fa45e441c3eb40dbe` and lock SHA-256 `1b8115cf053e978f35d28854544b9ed01d871a5c7bc4eedf936c13ceebe9d4c9`. Reviewed `Sanity.lean`, the proof source and `status.json`. The sanity model is nonvacuous for every 0<d<=1/2 and either sign: observations are deterministic real values 1/2±d. It is Bernoulli at d=1/2, but is not a general interior Bernoulli realization. The specification is unchanged since pre-lock review. The recorded replay at source commit `12e73e5963bb313250b87aaed0fc700cb4ee9e00` checks both exact target types and all five public roots, with only propext, Classical.choice and Quot.sound. Both recorded commands exited zero. This reviewer read that record and checked its scope/hashes; it did not claim a second independent compiler execution. No blocking issue remains within this explicitly restricted bridge scope.

## Main upper construction: first complete-proof pass

Read `construction.tex` in full. The proposed theorem supplies an observable, unbiased single-coin output with second moment at most (153/56)rho and separate expected work at most w_alpha/a² for every alpha>2 margin envelope and every measurable q satisfying only the integrated rarity constraint. Compound-Poisson replication then gives exact uniform expected budget B, including B below one-copy cost. This is a substantive resolution of a previously open regime in this repository if the paper proof survives review; it is not a new universal arbitrary-law theorem or a new Lean theorem.

No blocking defect was found in the upper proof. Checks included:

- The apparently infinite likelihood dictionary is exactly finite at every observation prefix: indices k>=n cannot cross either threshold. This is an actual observable implementation, not access to a hidden magnitude or an infinite oracle calculation.
- Wrong-sign likelihood processes are nonnegative supermartingales. Bounded-horizon first-crossing bounds, followed by a countable union with summable weights, establish the asymmetric errors.
- For x=min(d,a), the selected reference gap lies between x/4 and x/2. The drift lower bound (2/3)x² and bounded upper overshoot are valid, including a=d=1/2. The stopping expectation identity is applied at a bounded horizon before monotone convergence establishes finite expected work.
- Both boundaries increase by the same factor at the next level. Thus the higher stopping time contains the lower stopping prefix even if their final labels differ. The difference can be computed on the same coin without extra hidden samples.
- The global rarity step uses the correct rearrangement bound E[q/x²]<=alpha/(alpha-2) a^-2 rho^(1-2/alpha). Replacing it by rho E[x^-2] would be false, and the proof does not do so. The bottom-rho mass is the extremizer for the exact power law.
- The series coefficient 153/56 and the expected-work coefficient w_alpha were independently recomputed. Nonnegative second moments are summed first, giving integrability before the signed telescope. The Poisson variance identity uses E[Y²], not Var(Y), and is valid for every positive intensity.
- The class allows mass above a. Use of min(D,a) handles it correctly. Constants diverge as alpha approaches two, which is stated rather than hidden.

Requested clarifications: give explicit iid-uniform realization for arbitrary mu,q; derive the localized fixed-gap RMS lower bound for every admitted B,rho,a instead of appealing only to an informal rate statement; use an admissible population in the unbounded-work sanity example; fix a harmless layer-cake typesetting typo. These requests do not identify a failure of the upper mathematical argument. Final acceptance of the matching theorem and source hash follows after the revised note is read.

Read the exact finite-prefix diagnostic code as well. It enumerates stopped probability masses using rational arithmetic, retains unresolved mass at cap 80, and does not turn that cap into an infinite-horizon conclusion. Its 18 parameter cases are diagnostics rather than evidence for all admissible algorithms. The upper theorem rests on the analytic proof.

## Final matching-theorem review

**Accepted on this paper-proof review pass**, with no unresolved blocking finding, at SHA-256 `fc198251e6b3df21c1203b26e5b0591136742417ff7d8c1534070cee54deb62e` for `construction.tex`. This is an agent review, not Lean checking, external specialist review, or a novelty certificate.

The revised note resolves all requests above. It constructs the experiment explicitly from iid latent magnitudes and independent uniforms, keeps all policy decisions observable, and explains canonical first-observation numbering/deferred iid draws. Its fixed-gap lemma derives the full saturated RMS lower bound from precise Lee–Valiant inputs rather than silently importing a high-confidence asymptotic rate. In the primary text, Corollary 19 explicitly supplies the baseline-prior expected-work bound, and Lemma 18 has the required KL orientation. The small-prior choices meet the source hypotheses; the separate sign-revelation argument handles large gaps and D=1/2; bounded prefixes and expected work justify passage to unbounded stopping. The midpoint test and Pinsker constants give the stated conservative lower coefficient. The simulation into the exact power law preserves each coin's hidden D across revisits and is conditionally iid given both that D and its sign.

The strongest accepted conclusion is the complete rate

    R_mu,rho(B) ≍_alpha min(rho, sqrt(rho)/(a sqrt(B)))

for exact power margins with alpha>2, jointly in every B>=1, 0<rho<=1/4 and 0<a<=1/2. The upper bound is stronger: one algorithm for each supplied (alpha,a,rho,B) handles the whole corresponding margin-envelope class without knowing mu or q. The underlying single-coin estimator has separately bounded second moment (153/56)rho and expected work w_alpha/a². These are algorithm-level paper statements; the new Lean bridge certifies a different, existing 713 construction.

The arbitrary-law universal-constant conjecture and the critical alpha=2 regime remain open. The note's proof constants diverge as alpha decreases to two. Sequential likelihood testing, single-term debiasing, and Poisson calibration are established ingredients: the refreshed Vihola audit confirms direct overlap, including its Example 8 Poisson construction. The advance established here is relative to the repository's previously unresolved regime; publication priority is not established.

Final source amendment review: independently recomputed SHA-256 `f05b297a9885a9cd24c203256ce11b0da29eb7f98433f0561f448652d1dbb4fc` and read the amended passages. They add explicit attribution to Vihola Theorem 3 and Example 8 and split the constant and margin-inequality displays for layout. The mathematical formulas and conclusions are unchanged. The acceptance above therefore applies to this final source hash; `fc198251...` records the earlier complete-proof review, not the final deliverable.

Compilation correction: independently checked that equation (4)'s closing literal brace is now correctly escaped as `\}` and recomputed the current source SHA-256 `ff70296efd76f7b1fd0ac50d12eff1a22361b5bb566dc97c82836833640b3d00`. This is a TeX delimiter correction with no mathematical change. The accepted, compiled deliverable uses this latest hash; the two preceding hashes retain the review sequence.
