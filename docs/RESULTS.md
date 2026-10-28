# Results and verification scope

Start with the [consolidated v5 manuscript](../paper/v5/paper.pdf) for the
current theory in one document: main statements in sections 2, 7 and 11,
formal scope in section 12, and full rare-event arguments in appendices A–C.
Its [source and editorial record](../paper/v5/README.md) preserves the original
proofs and makes the Psi correction explicit.

This guide gives the exact Lean specifications and remaining paper-proof
boundaries. Historical source pointers below refer to the unchanged
[v4 paper](../paper/paper.pdf), its [TeX](../paper/paper.tex), and the
[rare-event continuation](../inputs/next-phase/report/research_note.pdf).

## Paper review scope

The [response to the final Opus review](../inputs/next-phase/baseline/Adaptive_Threshold_v4/review/RESPONSE_TO_OPUS.md) records agent review of components incorporated into v4, including the budget-only algorithm and symmetric-KL converse. It explicitly says that the consolidated manuscript has not received independent specialist review. “Paper proof” therefore does not imply external peer review or a complete Lean proof. The later 713 argument, bias counterexample, and unknown-rarity obstruction have a separate [independent agent review](../proposals/RESEARCH_REVIEW.md), whose author did not write those arguments.

## Minimax law and unbiasedness

[Theorem 1 in §2](../paper/paper.tex#L239) defines the minimax RMS risk

$$R_\mu(B)=\inf_{\mathcal A:\,\sup_q\mathbb E_{\mu,q}T\le B}\ \sup_q\bigl(\mathbb E_{\mu,q}(\widehat\theta-\theta)^2\bigr)^{1/2}.$$

For every probability law $\mu$ on $(0,1/2]$, $B\ge1$, and $0<\delta\le1/4$, it proves

$$R_\mu(B)\asymp\omega_\mu(B^{-1/2}),\qquad r_\mu(B,\delta)\asymp\omega_\mu\!\left(\sqrt{\log(1/\delta)/B}\right),\qquad \omega_\mu(h)=\mathbb E_\mu\min\{1,h/D\}.$$

Here $r_\mu(B,\delta)$ is the minimax uniform error radius at failure probability at most $\delta$, with the same expected-budget constraint. The constants are universal. The algorithms depend only on $B$, or on $(B,\delta)$, and observe neither magnitudes nor their law. The proof is in §5. The RMS characterization now has Lean proofs in both directions. The confidence-radius statement retains paper-proof status.

The [full upper theorem](BLIND_UPPER.md), `distribution_blind_upper` in
[Full.lean](../lean/ThresholdHC/BlindUpper/Full.lean), proves one budget-indexed
observable algorithm family chosen before every magnitude law. It satisfies
the uniform expected budget and has maximal RMS risk at most
`512 * modulus μ (1 / Real.sqrt B)` for every `B ≥ 1`. The corresponding
`minimax_upper_bound` uses the same minimax risk as the lower theorem below.
The original simulation law, actual controller cost/output identities,
almost-sure pilot termination and budget selection are proved. The
[full audit](../results/blind_upper_components_002.json) checks the unchanged
frozen specification and all 373 declaration roots; coefficient 512 is not
claimed optimal.

The RMS lower-bound side is now formalized end to end. `ThresholdHC.Tier6.minimax_lower_bound` in [Full.lean](../lean/ThresholdHC/Tier6/Full.lean) proves

$$R_\mu(B)\ge\frac1{64}\omega_\mu(B^{-1/2})\qquad(B\ge1).$$

The [algorithm model](../lean/ThresholdHC/Tier6/AlgorithmModel.lean) takes the infimum over all measurable random-seed spaces and adaptive estimators, with expected work uniformly bounded over every measurable sign law. It permits unrestricted natural-number coin creation, revisits, interleaving, and unbounded stopping. The iid hidden magnitude environment is independent of algorithm randomness and is not visible to policy or output. Squared error and RMS use extended-real values, retaining infinite risk. `process_realization` constructs the infinite probability laws and proves their cylinder identities; realization, KL, absolute continuity, and testing bounds are not assumptions of the final minimax theorem. An immediate-stopping estimator proves the class nonempty and its minimax RMS risk at most one. See the [exact specification](../lean/ThresholdHC/Tier6/Specification.lean), [complete audit](../results/tier6_status.json), and [verification record](TIER6.md). Optimality of the coefficient $1/64$ is not asserted.

[Theorem 2 and §6](../paper/paper.tex#L272) quantify over every measurable sign function $q$ at a fixed $\mu$. Put $I=\mathbb E_\mu[D^{-1}]$, $V=\sup_q\operatorname{Var}_{\mu,q}(Y)$, and $\overline W=\sup_q\mathbb E_{\mu,q}W$. An estimator unbiased for all such $q$ can have $V,\overline W<\infty$ exactly when $I<\infty$, and every such estimator satisfies $V\overline W\ge I^2/16$. These are uniform bounds, not a lower bound for each individual population. The theorem and converse remain paper proofs. The fixed-gap example attaining the lower coefficient is in §6, equation `eq:fixed-gap-sharp`; it does not identify the optimum for every nondegenerate law.

## The 713 construction

`ThresholdHC.Uniform713.full_bound_713` in [FullBound.lean](../lean/ThresholdHC/Uniform713/FullBound.lean) inhabits [FullBound713Statement](../lean/ThresholdHC/Uniform713/Specification.lean). For classifier parameters $(k_1,k_2)=(1/4,1)$ and the geometric single-term estimator, it proves square integrability, finite expected actual work, unbiasedness, and

$$\operatorname{Var}(Y)\mathbb E W<713\left(\mathbb E[D^{-1}]\right)^2.$$

Its assumptions describe an arbitrary magnitude/sign probability space, a conditional observation kernel, independent measurable observations in $[0,1]$ with means $1/2\pm D$, $0<D\le1/2$ almost surely, and an integrable inverse magnitude. Bernoulli observations are included. No classifier error, moment, work, or unbiasedness conclusion is an assumption. The random level has unbounded support. See the [kernel audit](../results/uniform713_status.json) and [paper argument](../proposals/constants/UNIFORM_PRODUCT_BOUND.md).

The additive, separately locked `ThresholdHC.ResearchRouteA.separate_moment_bounds` exports $\mathbb E Y^2\le23I$ and $\mathbb E W\le31I$, including integrability. `uniform_family_bounds` proves bounded separate suprema and their product at most $713I^2$ for a nonempty family of latent laws sharing $I$, with the kernel and estimator fixed before the family. This supplies the formal separate-supremum bridge, not a fresh-coin realization or a new constant. See the [specification, hashes and local replay](../research/2026-10-27-route-a/formal-audit.md). Five public roots were checked with only the permitted axioms. The integrated Linux replay also passed in [run 40488398325](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/40488398325) on main commit `b3f88e6`.

## Information and stopping

Fix a finite set of $m$ coins with magnitudes $0<d_i\le1/2$. The hypotheses have sign probabilities $q_\pm(i)=1/2\pm\eta_i$, where $0\le\eta_i\le1/8$, $h>0$, and $d_i\eta_i\le h/8$. Policies adapt to observation history. Write $T_n$ for actual work by finite horizon $n$.

- `ThresholdHC.Proofs.stopped_transcript_kl` in [Transcript.lean](../lean/ThresholdHC/Proofs/Tier2/Transcript.lean) proves $\operatorname{KL}(\mathsf P_{+,n},\mathsf P_{-,n})\le(128/225)h^2\mathbb E_+T_n$ for the explicit laws in [Statements2.lean](../lean/ThresholdHC/Statements2.lean).
- `ThresholdHC.Tier3.randomized_information_bound` in [RandomizedBase.lean](../lean/ThresholdHC/Tier3/RandomizedBase.lean) proves the average conditional information bound for an arbitrary common measurable random seed. `ThresholdHC.Tier3.randomized_marginal_kl_bound` and `ThresholdHC.Tier3.randomized_testing_bound` in [Randomized.lean](../lean/ThresholdHC/Tier3/Randomized.lean) handle the seed-marginal transcript and tests allowed to observe the seed. See [RandomizedModel.lean](../lean/ThresholdHC/Tier3/RandomizedModel.lean) for assumptions.
- `ThresholdHC.Tier3.unbounded_stopping` in [StoppingBase.lean](../lean/ThresholdHC/Tier3/StoppingBase.lean) derives almost-sure halting under both hypotheses from finite expected actual work under the plus hypothesis alone. `ThresholdHC.Tier3.unbounded_testing` in [Stopping.lean](../lean/ThresholdHC/Tier3/Stopping.lean) proves $\operatorname{kl}(1-\delta,\delta)\le(128/225)h^2\mathbb E_+T$ for $0<\delta<1/2$ when both terminal-test errors are at most $\delta$. [StoppingModel.lean](../lean/ThresholdHC/Tier3/StoppingModel.lean) requires finite-prefix laws to realize the explicit experiment; it does not assume termination or the information bound.
- `ThresholdHC.Tier3.unbounded_example` in [Examples.lean](../lean/ThresholdHC/Tier3/Examples.lean) supplies a geometric-seed experiment with finite expected work and positive probability of exceeding every finite cap.

The stopping theorem above concerns terminal testing; the [audit record](../results/tier3_status.json) lists its exact targets. The subsequent `ThresholdHC.Tier4.infinite_kl_bound` in [Full.lean](../lean/ThresholdHC/Tier4/Full.lean) proves the same information/work inequality for the actual joint law of the seed and entire infinite observation tape, using Mathlib's `InformationTheory.klDiv`. Its [model](../lean/ThresholdHC/Tier4/Model.lean) retains the finite coin set, the same prior and magnitude constraints, arbitrary measurable seeds, and finite expected actual work under the plus hypothesis. It assumes the joint finite-prefix experiment laws, not an entropy identity or bound.

`ThresholdHC.Tier4.finite_prefix_kl_identity` in [FiniteBase.lean](../lean/ThresholdHC/Tier4/FiniteBase.lean) identifies joint seed/prefix KL with the conditional finite-sum information. `ThresholdHC.Tier4.infinite_kl_eq_iSup` in [StoppedFull.lean](../lean/ThresholdHC/Tier4/StoppedFull.lean) proves that full KL equals the supremum of prefix KL values. The theorems `infinite_kl_finite` and `observable_kl_bound` in [Full.lean](../lean/ThresholdHC/Tier4/Full.lean) derive absolute continuity, integrability of the log-likelihood ratio, and the same bound for every measurable statistic of the seed and tape. See the [complete audit](../results/tier4_status.json) and [development record](TIER4.md).

Tier 5 extends the full information/work bound to unrestricted adaptive coin creation. `ThresholdHC.Tier5.creation_infinite_kl_bound` in [Full.lean](../lean/ThresholdHC/Tier5/Full.lean) allows any natural-number coin label at each observation, arbitrary revisiting/interleaving, and coordinate-measurable common random magnitude/prior environments. Its [exact model](../lean/ThresholdHC/Tier5/Model.lean) specifies independent latent-sign cylinder laws; normalization and consistency are proved. The cap used to define each finite cylinder is derived from the finite decision tree and may vary without bound with the seed.

Only plus-hypothesis finite expected work is required. Minus-hypothesis nontermination is permitted; absolute continuity and the full-KL prefix-supremum identity are derived. `creation_observable_kl_bound` covers every measurable statistic, and `creation_infinite_kl_bound_extended` also permits infinite expected work with an extended-real right-hand side. A countable independent-coin example has finite expected work and positive probability of exceeding every deterministic creation cap. See the [complete audit](../results/tier5_status.json) and [scope and verification record](TIER5.md). This closes the fixed-family restriction for the KL/work component of [paper §3, Proposition 6](../paper/paper.tex#L425); it does not claim a Lean formalization of the entire paper or a canonical process-existence theorem for every environment.

## Rare-event optimizer

For any magnitude law $\mu$ on $(0,1/2]$, $0<\rho<1$, and $h>0$, define

$$\Psi_{\mu,\rho}(h)=\sup_{\substack{v\text{ measurable},\ 0\le v\le1\\\mathbb E_\mu v(D)\le\rho}}\mathbb E_\mu\min\{v(D),h\sqrt{v(D)}/D\}.$$

`ThresholdHC.Tier3.arbitrary_law_cutoff` and `ThresholdHC.Tier3.arbitrary_law_optimizer` in [Optimizer.lean](../lean/ThresholdHC/Tier3/Optimizer.lean) prove a unique $t\in(0,1/2)$ satisfies $\mathbb E_\mu\min\{1,t^2/D^2\}=\rho$, and $v_*(d)=\min\{1,t^2/d^2\}$ is an optimizer for every $h>0$. They prove saturation at $\rho$ for $h\ge t$ and, for $h<t$,

$$\Psi_{\mu,\rho}(h)=\Pr(D\le h)+h\mathbb E[D^{-1};h<D\le t]+ht\mathbb E[D^{-2};D>t].$$

The [specification](../lean/ThresholdHC/Tier3/OptimizerModel.lean) permits atoms and singular laws and assumes no finite inverse moment. It formalizes the identity in [continuation §3.3](../inputs/next-phase/report/research_note.tex#L218). The proposed matching arbitrary-law statistical upper bound is refuted by the reviewed critical-law paper proof below; the variational identity remains valid. The matching rare-event construction in the preserved continuation's §4 covers power margins $F(d)=(d/a)^\alpha$ on $(0,a]$ for $0<\alpha<2$, not $\alpha\ge2$.

## Rare-event power margins above two

The separate [27 October research note](../research/2026-10-27-route-a/construction.tex), Theorem 1 and its exact-power corollary, supplies a **paper proof with two separate agent reviews** of

$$R_{\mu,\rho}(B)\asymp_\alpha\min\{\rho,\sqrt\rho/(a\sqrt B)\},\qquad \alpha>2,$$

for $F_\mu(d)=(d/a)^\alpha$ on $(0,a]$, all $0<a\le1/2$, $0<\rho\le1/4$, $B\ge1$, and every measurable $q$ with $\int q\,d\mu\le\rho$. The upper algorithm observes only coin flips and an independent seed. It knows $a,\rho$ (and $\alpha,B$ for budget calibration), and its upper guarantee also holds uniformly over laws with $F_\mu(d)\le(d/a)^\alpha$ for $d<a$, without knowing the law itself.

The new construction uses asymmetric sign-test errors and a randomized telescope. Its unbiased single-coin output has $\mathbb E Y^2\le(153/56)\rho$ and separately $\mathbb E T\le w_\alpha/a^2$, with explicit finite $w_\alpha$ in the note. The central integration step is $\mathbb E[q(D)\min(D,a)^{-2}]\le[\alpha/(\alpha-2)]a^{-2}\rho^{1-2/\alpha}$; this uses the global constraint, not $q(d)\le\rho$. Compound-Poisson replication enforces the exact expected budget, and a constant estimate covers saturation. The matching lower proof imports Lee–Valiant Corollary 19 and Lemma 18, then gives an explicit fixed-gap simulation reduction.

The [adversarial review](../research/2026-10-27-route-a/review.md), [second analytic review](../research/2026-10-27-route-a/second-review.md), [primary-source comparison](../research/2026-10-27-route-a/sources.md), and [baseline ledger](../research/2026-10-27-route-a/BASELINE.md) record the evidence. Reviewers did not author the main proof; model diversity is not guaranteed. The theorem is **not Lean-checked or externally specialist-reviewed**, and worldwide novelty is unverified. At that checkpoint, the arbitrary-law conjecture and $\alpha=2$ were unresolved. The later critical-law theorem below resolves the specified quadratic law and refutes the matching-Psi conjecture. A sharp replacement for arbitrary laws and a universal two-atom characterization remain open. Constants diverge as $\alpha\downarrow2$. The preserved paper and imported continuation are unchanged.

## Critical power margin: full minimax characterization

For the one fixed law $F(d)=(4d)^2$ on $(0,1/4]$, the
[full critical note](../research/2026-10-27-nonlinear-critical/unrestricted.tex)
proves, with universal constants, for all $0<\rho\le1/4$ and $B\ge1$,

$$R_{\mu,\rho}(B)\asymp\min\{\rho,\sqrt{\rho L(1+\log L)/B}\},\qquad L=1+\log(1/\rho).$$

The minimax class is every observable iid fresh-coin algorithm with uniform
expected work at most B. It includes nonlinear biased output, arbitrary
independent seeds, adaptive creation/revisiting/interleaving and unbounded
stopping. The algorithm may know mu, rho and B. The supremum ranges over all
measurable q in [0,1] with integral q at most rho; the lower proof's cap q<=1/2
is only an adversarial subclass. Neither individual magnitudes nor signs are
observed. The upper uses the pre-existing critical construction.

The new lower bound combines a strengthened all-negative-cost entropy
theorem, a rigorously justified common hard pair, and a finite-prefix adaptive
Hellinger reduction with an endpoint termination limit. Thus it covers the
previously unresolved nonlinear and interactive estimators. At this law
Psi(B^-1/2) has order min{rho,sqrt(rho L/B)}. Taking rho=exp(-exp(n)), B=rho^-2
forces R/Psi to diverge, refuting a universal C Psi upper even with known mu
and rho. This supplies no characterization for arbitrary other laws.

Status: **the critical minimax rate is Lean-checked in both directions**.
The explicit comparison with Psi retains paper-proof status. The original
[paper checkpoint](../research/2026-10-27-nonlinear-critical/CHECKPOINT.md)
preserves the four-file source bundle, independent adversarial agent review,
replay evidence and attribution. The later formal proofs are detailed below.
No explicit hard-pair formula, external specialist review or priority
certification is claimed.

The critical single-coin base-cost theorem (BC1) is Lean-checked in
[BaseCost.lean](../lean/ThresholdHC/CriticalEntropy/BaseCost.lean):

$$V\,\mathbb E_0T\ge c\rho L(1+\log L),\qquad L=1+\log(1/\rho).$$

One universal `c>0` works for every `0<rho<=1/4`. The same observable
procedure and independent seed law serve every measurable `q<=1/2` with
`integral q<=rho`. Its assumptions are uniform bias at most `rho/64`, a
uniform extended-variance bound `V`, and finite expected work under each
such prior. Finite extended variance implies square integrability; infinite
work and moments are retained in the definitions. Per-prior finite work
suffices, so the paper's stronger uniform finite-work hypothesis is covered.
The raw-second-moment version is also proved.

The proof derives activation normalization, population moment identities,
good-gap selection, observable iid restarts, sign-testing entropy, and the
rarity-dependent number of scales from those guarantees. In particular,
[FiniteGap.lean](../lean/ThresholdHC/CriticalEntropy/FiniteGap.lean) proves
the BC2 bound `sum_j d_j^2 E_-j T >= K log(K)/512` for one observable test
serving every specified gap and sign. It constructs the information bounds
and stopping windows and does not assume fair-coin termination.
The [model and dependency audit](CRITICAL_AUDIT.md#current-formal-boundary)
gives the exact intermediate hypotheses and source-specific evidence.
The capped finite-observation reduction is also proved in
[ObservationInformation.lean](../lean/ThresholdHC/CriticalEntropy/ObservationInformation.lean).
For an arbitrary measurable independent seed and a procedure stopping by a
deterministic cap, the statistic consisting of stopping time and head count
reconstructs the full seed/word law through population-independent conditional
measures. It preserves canonical Hellinger affinity and actual expected work.
Zero-probability cells are independent of the sign prior.

[CriticalGeometry.lean](../lean/ThresholdHC/CriticalEntropy/CriticalGeometry.lean)
also proves a compact convex representation of the entire admissible population
class, with every measurable prior covered up to almost-everywhere equality.
Its finite observation probabilities and target integral form an affine compact
convex image. Active probability coordinates have uniform positive lower bounds.
The separated population-pair set is nonempty, compact and convex before any
policy is selected; each capped policy supplies a continuous convex canonical
Hellinger distance taking values in `[0,1]` on that set. The formal construction
uses the weak dual of `L²` and proves its correspondence with actual populations.

[CriticalRisk.lean](../lean/ThresholdHC/CriticalEntropy/CriticalRisk.lean)
now applies the finite convex RMS comparison to this actual experiment.
It constructs one observable estimator, proves its square integrability and
uniform bias and extended-variance bounds, and preserves the original stopping
rule and actual work. The minimax selection, exponential moments, and RMS bound
are proved rather than assumed.

One universal `c>0` works for every capped policy. For `0<rho<=1/4`,
a nonnegative radius `epsilon`, and a repetition count `n`, write `w=E_0 T`.
Whenever `3 epsilon<=rho/64` and
`9 n epsilon^2 w<c rho L(1+log L)`, an actual admissible population pair has
target separation at least `2 epsilon` and canonical affinity to the power `n`
at least `1/2`. The pair may depend on the policy. This is the precise
policy-specific conclusion, before selecting a common pair.

[CriticalCommonPair.lean](../lean/ThresholdHC/CriticalEntropy/CriticalCommonPair.lean)
now proves the statistical common-pair statement. One universal `C>0` works
for every `0<rho<=1/4` and `0<=delta<=rho/96`: there are two actual measurable
priors in `[0,1/2]`, each with mass at most `rho`, whose target separation is
at least `delta`, and **the same pair** satisfies
`(1-Aff) rho L(1+log L) <= C delta^2 E_0 T` for every capped observable policy.
The pair is selected before the arbitrary seed space, seed law, output space,
policy and stopping cap. Affinity is the canonical affinity of the full
seed/transcript laws; work is measured under the all-negative population.

The proof derives a normalized bound without dividing by work, including zero
null work. Revealed finite mixtures are constructed as actual policies with
independent product seeds. Component seeds and caps may differ; both canonical
affinity and expected work average exactly. These identities discharge the
statistical hypothesis of the compact-convex common-point theorem.

[CriticalPopulationFinite.lean](../lean/ThresholdHC/CriticalEntropy/CriticalPopulationFinite.lean)
transfers that common pair to the actual finite adaptive population experiment.
One pair is chosen before every finite coin-family size, deterministic horizon,
and policy. The policy may revisit and interleave coins. The bound is
`(1-Aff) rho L(1+log L) <= C delta^2 E_mid T_n`, where the right-hand side
counts the simulator's observed flips under the same midpoint population.

The proof constructs a legal one-coin simulation for each label, using independent
auxiliary tapes for the other labels. It proves the full simulator's law equals
the existing Tier 2 transcript law after integrating latent magnitudes and signs,
including coin-specific hybrid priors. Local expected costs sum exactly to the
population flip count. A finite likelihood decomposition and canonical Hellinger
data processing transfer the common-pair bound; midpoint domination pays at
most twice the midpoint work. Impossible transcripts and zero work are retained.

[CriticalMinimax.lean](../lean/ThresholdHC/CriticalEntropy/CriticalMinimax.lean)
now proves the full critical minimax **lower** bound:

$$R_{\mu,\rho}(B)\ge c\min\{\rho,\sqrt{\rho L(1+\log L)/B}\},\qquad L=1+\log(1/\rho).$$

One universal `c>0` works for `0<rho<=1/4`, `B>=1`, and the quadratic law
with density `32d` on `(0,1/4]`. The infimum uses the existing Tier 6
observable adaptive estimators and constructed infinite creation experiment.
It permits arbitrary measurable independent seeds, unrestricted natural-number
coin labels, revisits, interleaving, and unbounded stopping. Neither policy nor
output can observe latent magnitudes or signs. The budget and risk range over
every measurable `[0,1]`-valued prior of mean at most `rho`; the half cap belongs
only to the hard-pair subclass. Squared error remains extended-real.

The proof transfers the common pair through each seed-dependent finite decision
tree, integrates the hidden iid magnitudes, and bounds finite-prefix affinity
by actual midpoint expected work. Finite work proves termination separately
under both endpoints. Each stopped tape is eventually equal to its padded
prefix, so bounded-event convergence gives terminal affinity without any
continuity assumption on the estimator's output. Direct Hellinger testing and
separation optimization give the rate, including saturation at `rho`.
A zero-work estimator proves budget nonemptiness and minimax risk at most `rho`.

The [sixteenth record](../results/critical_components_016.json) checks forty-three
exact targets and all 674 public declarations. The
[fifteenth record](../results/critical_components_015.json) preserves the finite
population checkpoint. Specifications were introduced alongside these proofs.
That lower-bound record retains its original scope. The matching critical
upper is now separately proved and audited below. The explicit comparison
refuting the matching-Psi conjecture remains a paper proof. The original
[distribution-blind upper](BLIND_UPPER.md) is also complete.

The [critical upper component checkpoint](CRITICAL_AUDIT.md#upper-construction-checkpoint)
adds an observable asymmetric classifier, its actual Bernoulli-tape error and
flip bounds, integration under every measurable prior with total mass at most
`rho`, and actual population bias and second-moment bounds. This dyadic
classifier is an alternative to the paper's likelihood-bank construction.
The [second component checkpoint](../results/critical_upper_components_002.json)
adds rarity-dependent calibration and an observable unbiased random-level
single-coin estimator. Its actual population mean is the sign mass, its
extended second moment is at most `28*rho`, and its expected flip count is at
most `112000000*criticalLogFactor(rho)`.

The [full upper theorem](../lean/ThresholdHC/CriticalUpper/Full.lean) now adds
independent fresh-coin aggregation, a measurable controller, exact actual
work/output identities, and transfer to the original Tier 6 experiment. Its
budget rule uses a fixed call count at large budgets and zero output at small
budgets. One universal coefficient `100000` gives
`R_{mu,rho}(B)<=100000*min(rho,sqrt(rho*L*(1+log L)/B))`
for every `0<rho<=1/4`, `B>=1`, and all measurable priors with global mass at
most `rho`. The coefficient is not optimized. The
[third record](../results/critical_upper_components_003.json) certifies both
unchanged frozen full statements and all declarations in 26 modules. It does
not certify the explicit Psi comparison.

## Population and nonlinear feedback follow-ups

The [population-step report](../research/2026-10-27-population-step/FINAL_REPORT.md)
contains reviewed paper proofs of a conditional information reduction, a
counterexample to one proposed radial information bound, and a calibrated
upper bound for that specified radial submodel. The counterexample rules out
that proof route; it does not refute the later full critical-law theorem above,
whose hard pair is not the radial proposal. Its finite Bayes calculations use
deterministic observation caps and do not settle the expected-budget minimax
problem.

The [nonlinear-feedback report](../research/2026-10-27-nonlinear-population/FINAL_REPORT.md)
adds a reviewed paper proof of strict acquisition-feedback advantage for a
two-gap experiment at a deterministic two-flip cap, an arbitrary-feedback
bounded-depth obstruction, and a finite approximation theorem that preserves
the uniform expected budget. Exact rational certificates support the finite
examples; no general finite convex program was solved. The 7,680-replicate
synthetic experiment is numerical evidence with 32 replicates per cell, not
a uniform risk guarantee, practical superiority claim, or confidence result.

These packages retain their original statements and source locks. Statements
that the matching-Psi conjecture was unresolved describe their historical
scope; the full critical-law paper result above supplies the counterexample.
A sharp arbitrary-law replacement remains open. See the
[research index](../research/README.md) and [replay commands](VERIFY.md).

## Earlier critical power margin: additive-class obstruction

At the single fixed law $F(d)=(4d)^2$, the new
[critical-regime note](../research/2026-10-27-critical-two/construction.tex)
proves, with universal constants and $L=1+\log(1/\rho)$,

$$R_{\rm add}(B)\asymp\min\{\rho,\sqrt{\rho L(1+\log L)/B}\}.$$

This restricted minimax class permits known $\mu,\rho,B$, a common independent
seed, an almost-surely finite seed-preselected coin count with finite mean,
and heterogeneous per-coin policies with unbounded stopping. Conditional on
the seed, components use independent genuine coins and local randomness;
each policy sees only its own observations. The output is an additive sum
plus a seed-dependent constant, with the square-sum and uniform moment/work
conditions stated in the note. Feedback across coins, data-dependent counts
and nonlinear terminal postprocessing are not covered.

The core theorem gives $\inf_A V(A)W(A)\asymp\rho L(1+\log L)$ for all
single-coin estimators with uniform bias at most $\rho/64$, including exact
unbiasedness. A component-selection reduction proves the population-class
lower bound without requiring identical kernels or predetermined finite
stopping horizons. The upper reuses the already available
[critical construction](../research/2026-10-27-minimax-audit/theorem/critical.tex).

Status: **paper proof with two separate agent reviews**. The [checkpoint](../research/2026-10-27-critical-two/CHECKPOINT.md)
links the complete proof, exact source hashes, prior-art comparison and checks.
No new Lean statistical theorem, external review or novelty certification is
claimed. Since $\Psi(B^{-1/2})\asymp\min\{\rho,\sqrt{\rho L/B}\}$ at this law,
the new result rules out a uniform matching-Psi guarantee in the specified
additive class. The later full critical-law theorem above resolves the
nonlinear/interactive gap; this earlier checkpoint's restricted statement and
evidence are preserved.

## Unknown rarity and numerical evidence

The [unknown-rarity obstruction](process/TRACK_D.md#an-obstruction-to-completely-uniform-adaptation-to-unknown-rarity) concerns a budget-indexed estimator family independent of the rarity bound. For a known fixed $0<d<1/2$ and almost-sure stopping at every constant sign prior in $[0,1/4]$, no universal finite $C$ gives RMS error at most $C\min\{\rho,\sqrt\rho/(d\sqrt B)\}$ for every $B\ge1$, $0<\rho\le1/4$, and $\theta\in[0,\rho]$. This is an independently agent-reviewed paper proof. It does not rule out an additive error floor, a positive lower bound on rarity, or an algorithm given $\rho$.

[Constant scores](../results/constants_theory.json), [upper-bracket evaluations](../results/power_bracket.json), and [held-out benchmark summaries](../results/real_test.json) are numerical evidence. Finite grids, truncation, floating-point arithmetic, and benchmark-specific assumptions do not yield universal theorems. See the [off-grid counterexample](../proposals/constants/BIAS_AUDIT.md) and [benchmark report](process/TRACK_C.md).
