# Independent paper-proof audit, 27 October 2026

**Verdict: no blocking mathematical defect found in the exact statements audited below.** The sharp order theorem is PROVED-ON-PAPER, with a separate adversarial agent pass. It is not Lean formalized, externally reviewed, or a solution of the unrestricted population minimax problem. This reviewer did not write either principal proof. Agent separation does not establish external independence or model diversity.

## Source identity and scope

The checkout HEAD at this audit was `a8a8dc49115aabdd1fba8d53d3390eb0a5eee864`. The `critical-two` directory and several Tier5 proof helpers were untracked concurrent work; this reviewer did not modify them. The principal proof initially read was `research/2026-10-27-critical-two/construction.tex`, SHA-256 `d85f58c1201fcd20e8769161ec27bfd51283f574fe9b0a9649f2f7b1974041a8`. It contained the unbiased theorem and complete upper appendix. During review, its owner added the small-bias theorem and proof, producing SHA-256 `29463b56bfcbcf35b0e9be2347d824489240d091fd26003bf17515e1b930affe`. This added material was separately read, not accepted merely because the older hash passed review. The latter version is the accepted checkpoint. There was **not** one unchanged source snapshot throughout this entire review.

The previously existing upper source `research/2026-10-27-minimax-audit/theorem/critical.tex` was freshly read at SHA-256 `0e8b9eaf762b3b09fa0d92ce1a036c2ceea8c12d00a5eea8286b852f36a81536`. Its bytes remained unchanged. The small-bias argument was already present in `critical-two/construction-notes.md`, SHA-256 `e7ed80e9a470f61e73f1f8899b028c16eddabb68e72b57b6e893b0e5da3efc66`; this is inherited concurrent work, not a theorem first discovered by this reviewer. `arithmetic.json` records all six inspected source hashes before and after its own run. Later source changes require a new audit checkpoint.

Fix `a=1/4`, `mu(dd)=2d/a^2 dd` on `(0,a]`, and `0<rho<=1/4`. Each procedure sees one genuine hidden Bernoulli coin, has a q-independent seed, and is measurable in that seed and the coin's observed history. It may depend on the known law and rho, return a signed real value, and use an unbounded stopping time, including zero observations. Computation and independent randomness are free; genuine flips are charged. The unknown q ranges over the **global** class `0<=q<=1`, `integral q dmu<=rho`.

For separate suprema `V=sup_q Var_q(Y)` and `W=sup_q E_q T`, the audited theorem is

`inf_A V W asymp rho L (1+log L)`, where `L=1+log(1/rho)`.

The same statement holds for `M=sup_q E_q Y^2` in place of V. It holds in the unbiased class and, separately, in the larger class with uniform absolute bias at most `rho/64`, assuming finite V and W. Constants are universal because a is fixed. The proof provides extremely loose constants and an extremely small asymptotic cutoff; it is an order theorem, not a useful numerical lower bound at practical rarity levels. No attainment of the infimum is asserted.

## Finite-gap entropy lemma: attempted failures and checks

The lemma uses a single common policy at finitely many interior gaps, separated by factors at least two. Correctness is required only at those signed gaps. The fair law is a comparison measure, not an input where the test must terminate or succeed.

1. The early event is measurable in the seed and a **deterministic finite prefix** of length `floor((1/1024)/d^2)`. Adding unused flips after stopping is legitimate. KL from minus to plus is at most `1/48`, and Pinsker gives total variation less than `1/8`. Since outputting minus is an error at plus, the early minus-output probability is at most `1/10+1/8`.
2. At the deterministic horizon `ceil(4 E_-tau)`, Markov leaves at most probability `1/4` after the horizon. Subtraction leaves window probability at least `17/40`, stronger than the asserted `1/4`. The degenerate case `E_-tau=0` cannot meet the two correctness requirements; the same inequalities would already contradict it.
3. KL **from the minus prefix to the fair prefix**, with this finite horizon, is at most `16c_j+1`, where `c_j=d_j^2 E_-tau`. Binary data processing and `kl(p,z)>=p log(1/z)-log2` imply the stated fair-law window probability `exp(-64c_j-8)`. No optional-stopping assertion at the fair law is used.
4. For at least half the indices `c_j<=2 cbar`. The corresponding windows have endpoints proportional to `d_j^-2`, whose ratios are at least four. Their deterministic overlap multiplicity is at most `1+log_4(1024(16cbar+2))`. One fair-law path has one terminal time, so the sum of its window indicators is bounded by that multiplicity. A nonterminating path belongs to none of the finite windows.
5. The concluding constants also work. Under the proposed contrary bound `cbar<log K/512`, put `x=log K>=32`. The left side exceeds `0.5 exp(3x/4-8)>=0.5 exp(x/2)>=x^2/16`. The right side is less than `6+x/4`. This last comparison follows from `4^(5+x/4)>=1024(1+x/4)>2048+32x` for `x>=32`, using `log4>1` and `exp t>=1+t`. Finally, for `x=32+y`, `x^2/16-6-x/4=50+(15/4)y+y^2/16>0`. This is an analytic all-x argument, not a floating-point grid check.

Thus the finite-gap statement with `c_s=1/512`, `K_s=ceil(exp32)` survives the attempted fair-law, stopping, rounding, and gap-selection objections.

## Single-coin reduction

All nonnegative conditional second moments and work functions can be constructed directly from the iid Bernoulli kernel and independent seed. Integrability under q=0 and q identically rho supplies one common full-measure set for both signs. Signed conditional expectations are defined only after that step. There is no intersection of null sets indexed by all q.

All-q unbiasedness implies `m_+-m_-=1` almost everywhere: test each measurable set E with `q=min(1,rho/mu(E))*1_E`, and subtract the q=0 identity. This uses the actual global class. Conditional Jensen at constant q=rho gives `M>=rho`, `V>=rho(1-rho)`, and `M<=4V/3`. In particular these are separate supremum bounds; the proof does not replace `(sup Var)(sup work)` by `sup(Var*work)`.

The zero-observation event is seed-measurable and has the same probability p for every latent state. Its expectation contribution c is q-independent. Conditioning on activity and returning `Z=pY+c` preserves every population expectation and gives `W_Z=W/p`. The exact second-moment identity is

`E_q Z^2 = p E_q[Y^2 1_A]+2c theta-c^2`.

Cauchy--Schwarz on the inactive event yields the subtraction `c^2/(1-p)`, giving `E_q Z^2<=pM+(1-p)theta^2`. The p=1 case is handled directly. Therefore `pM>=rho(1-rho)` and, for `m=pM+rho^2`, both `m<=4pM/3` and `mW_Z<=4MW/3`. Random refusal to take any observations cannot invalidate the product argument. Constants p,c may be granted to this lower-bound reduction; an effective way to compute them from arbitrary policy code is unnecessary for the claim that a test in the larger allowed mathematical class would exist.

The negative second-moment exceptional set has mass at most `64m`. A set on which `M_+-M_->2m/rho` cannot have mass rho: the nonatomic law permits an exactly rho-mass subset, whose indicator is admissible and contradicts the moment bound. Removing these sets leaves conditional means on opposite sides of a common threshold. This is where the exact nonatomic quadratic law matters; no arbitrary-law extension is proved by this argument.

Restarts use independent seeds and successive unused blocks of the **same** conditional Bernoulli tape. Conditional finite expected work at the selected signed gaps implies termination there. Conditioning on finite stopped prefixes and integrating over seed events proves that the unused suffix remains iid. Consequently the repeated outputs are independent at each fixed signed gap, and expected work adds exactly. The latent gap is never supplied to the policy. Chebyshev and `n=ceil(256(1+m/rho))<=513m/rho` give error below 1/10.

The annuli `(a4^-j/2,a4^-j]` have mass `(3/4)16^-j`; the selected cutoff makes each at least `130m`. At least half of each annulus remains good. Choosing a point whose negative work is at most four times the full-annulus average is valid and can exclude all null sets. Active work is at least one, eliminating a spurious zero-average case. The resulting gaps are separated by more than two and below 1/128. Summing gives the exact coefficient `(16/3)*513*(4/3)=3648`. The split `MW>=sqrt(rho)` versus `MW<sqrt(rho)`, followed by the compact-rarity bound, covers **all** moment/work allocations, not merely M of order rho.

## Small-bias extension and further proof refinement

The inherited extension replaces the pointwise response identity with a global test-set argument. If uniform bias is at most rho/64, then `integral(m_+-m_-)>=31/32`; total variance at q=rho gives `V>=rho(1-rho)(31/32)^2>=2rho/3`. Also `M<=3V/2`. Active normalization preserves the actual expectations and gives `m=pM+2rho^2<=4pM`, with `pM>=rho/6`. A set of mass rho where the response is below 3/4 contradicts the two bias bounds. Removing it as well as the two moment exceptions loses at most `67m` mass. Threshold 3/8, `n<=1282m/rho`, annulus mass `134m`, and product coefficient `30000` are valid. The same entropy proof completes the order lower bound. These checks were made against both the notes and the later TeX section.

The separately authored `lower/proof.tex` was also read in full. Its improved localization, `mu{g<7/8}<=16 epsilon<=rho/4`, is justified by first excluding mass at least rho and then applying the response identity to that set itself. The tighter constants `V>=2883rho/4096`, `m=max(rho,pM+(rho+epsilon)^2)<=5pM/2`, exceptional mass `66m`, threshold `7/16`, and final coefficient `6840` all check. Its deterministic arithmetic-average corollary follows from the exact bias--variance decomposition and `nW<=B`. This is a refined proof of the already available small-bias extension and a clearly stated consequence, not a priority claim. The first checked hash appears in `small_bias_arithmetic.json`; the later provenance-only edit was read and the final hash is in `small_bias_recheck.json` and `FINAL_PROOF_HASHES.json`.

## Matching upper proof, freshly checked

The inherited capped likelihood classifiers need no access to D or q. Wrong-sign likelihoods are nonnegative supermartingales, and a union bound over their finite dictionary supplies the crossing errors. A forced majority error is contained in the unconditional full-tape majority error event; no false independence from stopping is used. Integration under the quadratic law gives the required decaying error, including q concentrated entirely on the bottom-rho gaps.

For the correct reference, `r/d` lies in `[1/4,1/2]` and the drift is at least `2d^2/3`. The stopped log likelihood is bounded above by its crossing level plus a bounded overshoot; before crossing it is below the level. The finite stopped-sum identity followed by monotone convergence therefore proves finite expected crossing time. This does not require assuming in advance the very integrability being proved.

The positive work contribution uses the integral over the largest rho mass of a decreasing capped function. This is valid for the global rarity class; it does not use the false bound `E(qf)<=rho E f`. The geometric level has finite expected cost after the polynomial level bound. On one common latent coin, different classifier decisions imply at least one sign error even though their observations use separate blocks. The second moment is exactly bounded by `35rho/16+(85rho/16)/7=165rho/56`; expected work is bounded by `1350 a^-2 L(1+log L)`. Absolute summability is established before signed telescoping. Thus the inherited upper construction genuinely belongs to both audited classes.

## Primary-source comparison

Chen, Li and Qiao, [arXiv:1608.06031v2](https://arxiv.org/pdf/1608.06031v2), 24 May 2017: Definitions 1.4--1.5, p.3; Lemma 4.1, pp.7--8; Appendix D, pp.50--54; Remark D.4, p.54, were inspected in the primary HTML/PDF. Lemma 4.1 treats Gaussian SIGN tests, delta<0.04, and finitely many dyadic gaps with a weighted entropy lower bound. Appendix D transfers stopping-window events to the zero-gap law and controls overlap. Remark D.4 explicitly includes interior Bernoulli families via quadratic KL. **OVERLAPPING / PRIOR-ART:** the scale-entropy mechanism and Bernoulli applicability are established. The local proof supplies its selected-gap-only correctness, arbitrary separated gaps, delta=0.1, and finite-prefix constants. The source is not a population-mass minimax theorem. The response/moment reduction and sharp single-coin product require the additional argument audited above. Priority of that resulting theorem remains unresolved; this focused comparison is not an exhaustive search or priority certification.

## Limits and reproducibility

No conclusion about arbitrary population algorithms follows from a one-coin response identity. In particular, clipping, nonlinear aggregation, cancellation between unequal kernels, adaptively chosen replication, and genuine cross-coin interaction are outside the derived averaging consequences. A lower bound on raw variance is not automatically a lower bound on clipped RMS risk. The candidate Psi minimax law is neither proved nor disproved here.

Commands actually run from the repository root:

```powershell
python research/2026-10-27-population-step/audit/check_arithmetic.py
python research/2026-10-27-population-step/audit/replay_tier5.py
```

The first produced 22 passing exact rational/integer checks under Python 3.12.2, with no seeds or floating-point assertions. They check local arithmetic, not all real inequalities or statistical semantics. The second is separately described in `TIER5_COVERAGE.md`; it does not formalize this theorem. Original locks, original status records, paper sources, and concurrent proof files were not edited by this reviewer.

The immutable snapshot used by the parent is `inherited/construction.tex`, hash `29463b56bfcbcf35b0e9be2347d824489240d091fd26003bf17515e1b930affe`, matching the fully reviewed expanded source. The initial `d85f58...` review remains part of the chronology; it is not misidentified as that copied file's hash. Later snapshots of `construction-notes.md` and `second-review.md` preserve concurrent provenance records, not additional proof premises.

At final packaging the arithmetic scripts were made portable by reading preserved `inherited/` snapshots and by writing separate `*_recheck.json` files. Their original executed source bytes are retained under `historical_scripts/*.py.txt`; the earlier JSON records were not overwritten. All three current scripts were then actually run: 22 original arithmetic assertions, 11 refined small-bias assertions, and the population checks described in `POPULATION_AUDIT.md` passed. The final proof identities are pinned in `FINAL_PROOF_HASHES.json`.
