# Results and verification scope

Start with the [consolidated v6 manuscript](../paper/v6/README.md), which
combines the [v5 manuscript](../paper/v5/README.md) with the
[general-law rare-event manuscript](../paper/rare-event/README.md) and the
[finite-gap rare-event manuscript](../paper/finite-gap-rare-events/README.md).
Its [reading guide](../paper/v6/README.md#reading-guide) locates the original
theory, the rare-event results and the formal scope section; its
[editorial record](../paper/v6/README.md#source-and-editorial-scope) explains
which shared proofs appear once. The three source manuscripts are preserved
unchanged. The v5 source record preserves the original proofs and makes the
Psi correction explicit.

The general-law and finite-gap results are paper proofs, except that their
upper bounds and the $1+2\sqrt2$ quantile comparison are Lean-checked; their
scopes are recorded below.

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

Here $r_\mu(B,\delta)$ is the minimax uniform error radius at failure probability at most $\delta$, with the same expected-budget constraint. The constants are universal. The algorithms depend only on $B$, or on $(B,\delta)$, and observe neither magnitudes nor their law. The proof is in §5. Both the RMS and confidence characterizations now have Lean proofs in both directions in the original observable adaptive model.

The confidence theorem [`confidence_characterization`](../lean/ThresholdHC/Confidence/Full.lean)
proves the explicit bounds

$$\frac{1}{64}\,\omega_\mu\!\left(\sqrt{\frac{\log(1/\delta)}{B}}\right)
\le r_\mu(B,\delta)\le
8192\,\omega_\mu\!\left(\sqrt{\frac{\log(1/\delta)}{B}}\right)$$

for every probability law on positive gaps, $B\ge1$ and $0<\delta\le1/4$.
The [frozen specification](../lean/ThresholdHC/Confidence/Specification.lean)
also states the lower bound for every budget-admissible algorithm, one upper
family chosen before every gap law, and a nonvacuity theorem. The failure
event is $|\widehat\theta-\theta|>r$, uniformly over every measurable sign
law; work is the original extended-real expectation of actual flips.

The upper construction runs $2\lceil2\log(1/\delta)\rceil+1$ independent
calibrated batches and takes their median. Pair-numbered coin labels and
independent seed arrays realize those copies in the original observable
experiment. Exact pathwise identities prove the output and summed cost;
the independence and termination premises are derived. A zero-work rule
handles small budgets. The constants are not optimized. This radius depends
on $\mu$ in the theorem and does not supply a data-computable confidence
interval when the magnitude law is unknown.

The [audit](../results/confidence_001.json) checks all four full targets,
18 modules, and all 107 declaration roots. The target, model, and transitive
model dependencies were frozen at `76e9a8f` before supporting proofs.

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

[Theorem 2 and §6](../paper/paper.tex#L272) quantify over every measurable sign function $q$ at a fixed $\mu$. Put $I=\mathbb E_\mu[D^{-1}]$, $V=\sup_q\operatorname{Var}_{\mu,q}(Y)$, and $\overline W=\sup_q\mathbb E_{\mu,q}W$. An estimator unbiased for all such $q$ can have $V,\overline W<\infty$ exactly when $I<\infty$, and every such estimator satisfies $V\overline W\ge I^2/16$. These are uniform bounds, not a lower bound for each individual population. The fixed-gap example attaining the lower coefficient is in §6, equation `eq:fixed-gap-sharp`; it does not identify the optimum for every nondegenerate law.

The converse is now proved in Lean: [`unbiased_converse`](../lean/ThresholdHC/UnbiasedConverse/Full.lean)
inhabits the [full specification](../lean/ThresholdHC/UnbiasedConverse/Specification.lean)
in the unchanged Tier 6 observable adaptive experiment. For every measurable
seed space and estimator, unbiasedness for every measurable sign law and finite
uniform bounds on extended variance and actual expected flips imply inverse-gap
integrability and the product bound with coefficient 1/16. Unbiasedness explicitly
requires integrability; the conclusion does not assume a finite inverse moment.
No information bound, differentiability, bounded horizon, or finite coin supply
is an assumption of the final theorem.

The proof derives symmetric information bounds for vanishing clipped tilts,
obtains `modulus μ h ^ 2 ≤ 16 * h ^ 2 * W * V`, then applies monotone convergence
to truncated inverse gaps. The [audit](../results/unbiased_converse_001.json)
checks the exact target, all 10 modules and 38 declaration roots, transitive
axioms, and source stability. This proves the necessity direction and lower
coefficient in the original model. The construction below now supplies the
sufficiency direction in that same experiment. Their combination is the exact
Lean theorem `observable_unbiased_iff` in the hidden-magnitude model. The
oracle results below concern RMS and confidence, not an extended unbiased converse.

## Magnitude-oracle lower bounds

Theorem 1's stronger RMS and confidence lower bounds are now Lean-checked
for both revealed and adaptively selected magnitudes. For either oracle,

$$R_\mu^{\mathrm{oracle}}(B)\ge\frac{\omega_\mu(B^{-1/2})}{64},\qquad
r_\mu^{\mathrm{oracle}}(B,\delta)\ge
\frac{15}{256\sqrt2}\,\omega_\mu\!\left(\sqrt{\frac{\log(1/\delta)}{B}}\right)$$

for $B\ge1$ and $0<\delta\le1/4$. The [full theorems](../lean/ThresholdHC/OracleLower/Full.lean)
include algorithm-level bounds, minimax bounds, and nonvacuity. Work is the
extended-real expectation of actual flips, and all measurable sign laws are
allowed. In the selected experiment, $q$ is defined on the entire gap domain,
even outside the support of the target law $\mu$.

The [model](../lean/ThresholdHC/OracleLower/Model.lean) gives the revealed
algorithm the entire iid magnitude array for free, a stronger grant than
revealing gaps only when coins are created. The selected interface explicitly
creates a coin at a magnitude chosen from the seed and previous flips,
revisits a previously created coin, or stops. Its
[semantic theorem](../lean/ThresholdHC/OracleLower/SelectedSemantics.lean)
proves that creation uses an unused label and revisits preserve the birth
magnitude. Counterfactual histories supply a countable array of potential
coins; they do not restrict magnitudes to a fixed deterministic grid.
The canonical infinite experiment is proved to realize the explicit finite
transcript laws. No KL bound, realization identity, or stopping assumption
is a premise of the final lower bounds. Finite uniform work implies
almost-sure stopping.

The [audit](../results/oracle_lower_001.json) checks eight frozen targets,
10 modules, and all 54 declaration roots. The model and targets were compiled
and frozen at `3474a37` before the lower-bound and embedding proofs; the proof
checkpoint is `4a5805c`. The hidden model embeds with identical law, cost,
and risk, so the sharper confidence coefficient also applies there without
changing the earlier frozen confidence theorem. This addition concerns
RMS and confidence; it does not extend the unbiased converse or the
observed-outer-state results to a new model.

## The 713 construction

[`observable_713`](../lean/ThresholdHC/Observable713/Full.lean) inhabits the
[frozen observable specification](../lean/ThresholdHC/Observable713/Specification.lean).
It chooses one `AdaptiveEstimator ℕ` before every gap law. Whenever
$I=\mathbb E_\mu[D^{-1}]<\infty$, its output is integrable and unbiased for every
measurable sign law, with extended variance at most $23I$ and actual expected
flips at most $31I$. The product of the **two separate extended-real suprema**
is at most $713I^2$.

The seed is a geometric level. The policy reads coin zero until its fine
classifier stops; the adjacent coarse classifier reuses the same observed
prefix. Exact path identities identify both output and work with the analyzed
call. The policy never uses the gap law, hidden magnitude, or sign, and every
seed and tape stops after finitely many flips. The existing simulation theorem
transfers the analysis to the original infinite experiment. Together with the
converse, `observable_unbiased_iff` proves that uniformly finite variance/work
unbiased estimation exists exactly when the inverse gap is integrable. The
[audit](../results/observable713_001.json) checks both full targets, every new
declaration, transitive axioms, and the target/dependency freeze made before
these supporting proofs.

The earlier, more general conditional-observation theorem remains unchanged:

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

The [specification](../lean/ThresholdHC/Tier3/OptimizerModel.lean) permits atoms and singular laws and assumes no finite inverse moment. It formalizes the identity in [continuation §3.3](../inputs/next-phase/report/research_note.tex#L218). The proposed matching arbitrary-law statistical upper bound is refuted by the Lean-checked critical-law counterexample below; the variational identity remains valid. The matching rare-event construction in the preserved continuation's §4 covers power margins $F(d)=(d/a)^\alpha$ on $(0,a]$ for $0<\alpha<2$, not $\alpha\ge2$.

## General-law rare-event characterization

The separate [55-page rare-event manuscript, revised v2](../paper/rare-event/README.md)
provides a **paper proof with adversarial AI audits** for every known probability
law $\mu$ on $(0,1/2]$, known $0<\rho\le1/4$, and every $B>0$. The parameter
class is $0\le q\le1$ with $\int q\,d\mu\le\rho$. Every Bernoulli observation
is charged under a uniform expected-work budget. Creation, revisiting,
interleaving, nonlinear outputs, and unbounded stopping are allowed. The upper
procedure knows $\mu,\rho,B$; magnitude and sign remain hidden.

With $h=B^{-1/2}$, its entropy-tail selection functional is

$$\mathcal K_{\mu,\rho}(B)=\min\left\{\rho,\inf_{0\le\sigma\le\mu}
\left[h\sqrt{\rho\Gamma_\sigma}
+\int\min\{1,h/d\}\,(\mu-\sigma)(dd)\right]\right\}.$$

Here $\Gamma_\sigma$ is the homogeneous entropy of the inverse-square masses
in canonical dyadic bands, defined by increasing finite prefixes in Section
3.1 of the [source](../paper/rare-event/v2/sections/additive.tex). Section 4.6
records conservative universal constants:

$$10^{-17}\mathcal K_{\mu,\rho}(B)\le R_{\mu,\rho}(B)
\le33000\mathcal K_{\mu,\rho}(B).$$

No finite inverse moment, density, or regularity assumption is imposed.
The following scopes are **paper-level claims**. Lean versions now cover the
upper half of the first row and the other four rows, as described below, as
well as the hard-selection reduction and the elementary properties of
$\mathcal K$:

| Claim | Scope and qualification |
|---|---|
| Matching entropy-tail upper/lower bounds | Every law, known rarity, and positive expected budget in the model; hard measurable assignments suffice. |
| Attained four-prior stopping dual | Exact identity for the robust certificate program; its connection to minimax risk is a comparison inequality. |
| Factor-sixteen risk certificate | A sufficient theoretical cap or a cap passing the verified genie criterion; not every fixed cap. |
| Genie convergence | Pointwise convergence assumes finite latent divergence. An explicit infinite-divergence counterexample is included. Optimized convergence first fixes a positive regularization, takes the cap limit, then removes regularization. |
| Fixed-cap identification | For $m$ distinct positive magnitudes, the zero-bias threshold is $N\ge2m-1$. This identifies the target, not necessarily the full allocation $q$. Infinite support has a positive floor at every fixed cap; the cap may grow. |

The [audit index](../paper/rare-event/audit/README.md) distinguishes the original
source audits, final referee assessment, and revision audit, including corrected
interpretations of historical findings. V2 resolves the revision audit's two
minor editorial defects. Apart from the upper half and the stopping-program
results below, the new general results have no Lean formalization, and none
has external specialist review. The exact stored certificates cover 33 lower
bounds, 9 upper policies, 9 stopping decisions, and two perfect-label examples;
they are not proofs of the continuum or compactness claims. The existing Lean
variational-optimizer and critical-law results above and below retain their
separate scopes. See [verification commands](VERIFY.md#general-law-rare-event-manuscript-v2).

**Partial Lean formalization.** The [EntropyTail specification](../lean/ThresholdHC/EntropyTail/Specification.lean)
locks eight target types in the unchanged observable experiment of the
above-two package:

- the two-sided law $c\mathcal K\le R\le C\mathcal K$ with universal constants
  (v6 Theorem 13.2; the explicit constants above are not targets);
- its upper and lower halves;
- five properties of $\mathcal K$.

Six targets are **Lean-checked** with exact types and only the standard axioms.
The first is the upper half $R\le C\mathcal K$, with $C=28000$ (described
below). The other five are properties of $\mathcal K$:

- restricting to hard measurable assignments $\sigma=\mu|_S$ leaves the infimum
  over submeasures unchanged (v6 Lemma 13.1; no minimizer is claimed);
- $\mathcal K\le\min\{\rho,\int\min\{1,h/d\}\,d\mu,h\sqrt{\rho\Gamma_\mu}\}$;
- $\mathcal K=\min\{\rho,\sqrt\rho/(d\sqrt B)\}$ on a point mass at $d$;
- $\mathcal K=\rho$ when $B\le1$;
- $\mathcal K$ is positive and finite, and below $\rho$ for some law.

The lower half and the law are **not** Lean-proved. They remain paper proofs,
and the audit reports the law as unverified until all eight targets are
registered. The local audit of the five properties passed at `49877f3`.

**Upper half.** The upper bound comes from the additive formalization of
[#33](https://github.com/davidiach/adaptive-threshold-estimation/pull/33), in
the [EntropyTailQuantile](../lean/ThresholdHC/EntropyTailQuantile/),
EntropyTailUpper, EntropyTailAssembly, EntropyTailSampling and
[EntropyTailExecution](../lean/ThresholdHC/EntropyTailExecution/UpperTheorem.lean)
modules. It builds an observable estimator in the unchanged experiment and
proves $R\le28000\,\mathcal K'$ for every probability law on $(0,1/2]$,
$0<\rho\le1/4$ and $B>0$, with no inverse-moment or finite-support assumption.
Here $\mathcal K'$ is that development's own definition of the selection
functional, with Bochner band costs. The
[bridge](../lean/ThresholdHC/EntropyTail/Bridge.lean) proves
$\mathcal K'\le\mathcal K$ always and $\mathcal K'=\mathcal K$ for every
finite law, so [Upper.lean](../lean/ThresholdHC/EntropyTail/Upper.lean)
proves the locked upper target. The same development also proves the following,
for its closed quantile functional $Q$ with a fractional boundary atom:

- the quantile split;
- $\mathcal K\le Q\le(1+2\sqrt2)\mathcal K$, restated for the locked
  $\mathcal K$ as `selection_quantile_comparison`;
- $R\le30001\,Q$ for every law.

Its own [locked specification](../lean/ThresholdHC/EntropyTailQuantile/Specification.lean)
states the two upper bounds with the coarser constant 33000. Its
[lock](../tools/entropy_tail_quantile_specification_freeze.json) records the
mechanical rename from #33's namespace, needed because `main` had locked a
different model at the same paths. CI runs
`python tools/verify_entropy_tail.py --sequential` and
`python tools/verify_entropy_tail_upper.py --cached-dependencies` in the
`entropy-tail-upper` job ([details](VERIFY.md#entropy-tail-selection-functional)).
No result record is published for these audits.

**Stopping program, identification and genie certificates.** The same
development of #33 formalizes the robust stopping program for every
probability law on $(0,1/2]$, with the actual globally rare sign priors and
the unrestricted observable experiment, in the
[StoppingProgram](../lean/ThresholdHC/StoppingProgram/),
[CapIdentification](../lean/ThresholdHC/CapIdentification/) and
[Genie](../lean/ThresholdHC/Genie/) modules. Its
[specification](../lean/ThresholdHC/StoppingProgram/Specification.lean) fixes
three full targets. They now have a
[lock](../tools/stopping_program_specification_freeze.json), added in this
integration; its chronology records that the specification predates their
proofs. Here $P_N$ is the program value at observation cap $N$ and $R$ the
minimax risk.

| Paper claim | Lean result |
|---|---|
| Attained four-prior stopping dual | `AttainedDualStatement`: exact value identity, primal and dual optimizers, positive value and finite optimal information ratio, for $0<\rho\le1/4$, $B>0$, $N>0$. `ProgramUpperStatement`: every feasible certificate is realized by an observable estimator, so $R\le P_N$. The finite-cap value lies between the two-prior midpoint modulus and three times it. At infinite cap the dual is attained, with factor-three midpoint and factor-eight minimax comparisons and monotone cap limits, for $0<\rho\le1/2$. |
| Factor-sixteen risk certificate | `FiniteCertificateStatement`: $R\le P_N\le16R$ at $N=\lceil64\max(B,\rho B^2)\rceil$, through the exact truncation penalty and a universal Bernoulli-label floor. It does not use the entropy-tail lower bound. Also: exact finite cone/cutoff representation for finitely supported laws, the rarity-support optimizer, Bellman attainment of the information/work ratio, and information bounds for arbitrary seeded, order-dependent capped procedures. |
| Genie convergence | Monotone latent-reveal brackets and exact Bellman certificates. Residual convergence assumes finite latent divergence. Optimized convergence uses variance-reference regularization before the cap limit. Risk brackets give finite termination of the factor-sixteen test, for $0<\rho\le1/2$ and $B>0$. The direct squared-risk certificate and an exact finite-atom SOCP for $G_N^2$ are included. So is the uniform-gap counterexample: infinite latent divergence, infinite genie ratios and failure of pointwise convergence. |
| Fixed-cap identification | `fixed_cap_identification`: on $m$ distinct positive magnitudes the target is identified exactly when $N\ge2m-1$, via odd moments and count coefficients. For infinite support, every fixed cap has a positive bias floor uniform in the budget, and $P_N(B)\to\Delta_N/2$ as $B\to\infty$, where $\Delta_N$ is the largest target gap between rare priors whose capped count laws agree. |

These results are **Lean-checked** with exact statements and only the
standard axioms, subject to the CI audit in the `stopping-program` job
([details](VERIFY.md#stopping-program-identification-and-genie-certificates)).
The scopes and constants are those of the Lean statements, which can differ
from the manuscript's. None of them proves the entropy-tail lower bound or the
two-sided law.

## Rare-event power margins above two

The [full observable Lean package](../lean/ThresholdHC/RareAboveTwo/Full.lean) now proves the rate first established in the separate [27 October research note](../research/2026-10-27-route-a/construction.tex):

$$R_{\mu,\rho}(B)\asymp_\alpha\min\{\rho,\sqrt\rho/(a\sqrt B)\},\qquad \alpha>2,$$

for $F_\mu(d)=(d/a)^\alpha$ on $(0,a]$, all $0<a\le1/2$, $0<\rho\le1/4$, $B\ge1$, and every measurable $q$ with $\int q\,d\mu\le\rho$. The upper algorithm observes only coin flips and an independent seed. It knows $a,\rho$ (and $\alpha,B$ for budget calibration), and its upper guarantee also holds uniformly over laws with $F_\mu(d)\le(d/a)^\alpha$ for $d<a$, without knowing the law itself.

The original paper construction uses asymmetric sign-test errors and a randomized telescope. Its unbiased single-coin output has $\mathbb E Y^2\le(153/56)\rho$ and separately $\mathbb E T\le w_\alpha/a^2$, with explicit finite $w_\alpha$ in the note. The central integration step is $\mathbb E[q(D)\min(D,a)^{-2}]\le[\alpha/(\alpha-2)]a^{-2}\rho^{1-2/\alpha}$; this uses the global constraint, not $q(d)\le\rho$. Compound-Poisson replication enforces the exact expected budget, and a constant estimate covers saturation. The matching lower proof imports Lee–Valiant Corollary 19 and Lemma 18, then gives an explicit fixed-gap simulation reduction.

The [adversarial review](../research/2026-10-27-route-a/review.md), [second analytic review](../research/2026-10-27-route-a/second-review.md), [primary-source comparison](../research/2026-10-27-route-a/sources.md), and [baseline ledger](../research/2026-10-27-route-a/BASELINE.md) record the evidence. Reviewers did not author the main proof; model diversity is not guaranteed. The new Lean construction has second moment at most $28\rho$ and uses fixed-count averaging with the constant saturation estimator. Its matching lower coefficient is $1/256$ for every law supported below $a$, proved without importing an external statistical theorem. These two constants are instantiated in the proofs; the frozen statements assert positive constants. The [formal scope and proof map](RARE_ABOVE_TWO.md) distinguish these conservative constants and the formal algorithm from the paper construction. The seven frozen targets also cover exact-law existence, Psi equivalence and nonvacuity. External specialist review and worldwide novelty remain unverified. At the 27 October paper checkpoint, the arbitrary-law conjecture and $\alpha=2$ were unresolved. The later critical-law theorem below resolves the specified quadratic law and refutes the matching-Psi conjecture. The [general-law manuscript](#general-law-rare-event-characterization) supplies an entropy-tail replacement as an audited paper proof. The separate finite-gap manuscript below gives a closed quantile formula for known finite laws, including two atoms; infinite-support and unknown-law guarantees remain outside that manuscript's scope. Constants diverge as $\alpha\downarrow2$. The preserved paper and imported continuation are unchanged.

## Known finite-gap rare events: paper-proof characterization

Theorem 1.1 of the [standalone manuscript](../paper/finite-gap-rare-events/paper.pdf)
states, for every known finite positive-gap law, $0<\rho\le1/4$ and $B>0$,

$$10^{-20}Q(B)\le R_{\mu,\rho}(B)\le30001Q(B),\qquad Q(B)=\min\{\rho,T_h+h\sqrt{\rho\Gamma_\kappa}\},\quad h=B^{-1/2}.$$

Here $\nu$ is exactly the smallest-gap mass $\rho$, $\kappa=\mu-\nu$,
$T_h=\int\min\{1,h/d\}\,\nu(dd)$, and $\Gamma_\kappa$ is the dyadic
inverse-square cost entropy defined in the [paper guide](../paper/finite-gap-rare-events/README.md).
Rarity is the global constraint $\int q\,d\mu\le\rho$, with $0\le q\le1$.
Coins have iid complete persistent latent pairs; algorithms observe only
their independent seed, coin identities and purchased flips. Both bounds
use uniform expected physical-observation budgets and allow adaptive
creation, revisiting and interleaving.

Status: **the two-sided theorem is a paper proof**, not externally
specialist-reviewed. Its upper bound is Lean-checked in a stronger form:
$R\le30001\,Q$ for every probability law on $(0,1/2]$, not only finite ones,
with the same $Q$ ([upper half](#general-law-rare-event-characterization)).
The lower bound $10^{-20}Q\le R$ is not Lean-checked.
The precursor received fresh-context AI review; the
[provenance note](../paper/finite-gap-rare-events/PROVENANCE.md) records its
limits. The earlier Lean finite-gap entropy and critical-law results do not
certify this theorem. The manuscript does not establish an unknown-law guarantee, a
general infinite-support extension, a deterministic budget or a
high-confidence result.

[Revision 2](../paper/finite-gap-rare-events/revision-2/README.md) of the
manuscript ([PDF](../paper/finite-gap-rare-events/revision-2/paper.pdf)) adds a deterministic comparison with the
[general-law selection functional](#general-law-rare-event-characterization):
$\mathcal K\le Q\le(1+2\sqrt2)\mathcal K$ for every law on $(0,1/2]$. This
comparison is now Lean-checked ([upper half](#general-law-rare-event-characterization)). So
Theorem 1.1 is the finite-law case of the general-law characterization, with a
closed functional, explicit constants and a self-contained proof that does not
cite the general-law theorem. The two proofs share the observable upper
construction and most appendix lemmas and differ mainly in the lower-bound
reduction, so their agreement is not independent confirmation of the rate.
Conditionally on the general-law theorem, $R\asymp Q$ also holds for general
laws; that extension rests entirely on the general-law paper proof. The
consolidated v6 manuscript states this extension as a corollary of the
entropy–tail theorem in the same paper; its status is unchanged. The
comparison came from an external adversarial review of revision 1, which is
unchanged.

The additive [computation note](RARE_EVENT_COMPUTATION.md) improves the
deterministic comparison to $\mathcal K\le Q\le(5/3)\mathcal K$ for every
probability law on positive gaps, including infinite support. Its proof
retains the selected tail and core costs separately, uses superadditivity
and a square-root triangle inequality for the entropy, and proves the sharper
scale-separated estimate $\Gamma_\xi\le2H_\xi/t$ on $[t,1/2]$.
This is a new paper proof, not a Lean theorem or a completed formalization of
the statistical rare-event law. The note also gives a slightly smaller
algebraic coefficient without claiming optimality.

The [toolkit](../toolkit/README.md#3-compute-the-rare-event-rate-for-a-known-finite-law)
now computes the finite-law $Q$ and its inverse with $O(n\log n)$
preprocessing and $O(\log n)$ queries. It returns the comparison
$\mathcal K\in[\max\{T_h,3Q/5\},Q]$, evaluated in floating point, alongside the tail and
entropy terms. This implementation is not Lean-checked or interval certified;
its target-value inverse is not an achieved-error or estimator-budget guarantee.

The 30 October [certified-selection package](../research/2026-10-30-certified-selection/README.md)
sharpens the comparison further, to $\mathcal K\le Q\le\frac85\mathcal K$ for
every law on $(0,1/2]$. That is below both $5/3$ and the computation note's
algebraic coefficient $\lambda_*\approx1.6435$. Besides the same
scale-separated estimate, it replaces the square-root triangle inequality by
the entropy interaction bound
$\mathcal G(a+b)\le\mathcal G(a)+\mathcal G(b)+\sqrt{2\mathcal G(a)\mathcal G(b)}$.
The best factor lies in $(1.4604,8/5]$, by exact rational certificates for a
six-atom law ($Q/\mathcal K>1.42132$) and an eight-atom law
($Q/\mathcal K>1.4604$, from the integration review). For finite laws, the
package also proves that some optimal hard selection is an upper-gap suffix in
every dyadic band. It proves $|\mathcal K_\mu-\mathcal K_{\tilde\mu}|\le d_{\rm TV}(\mu,\tilde\mu)$
and a band-preserving rounding bound, and adds an exact-rational evaluator of
$\mathcal K$ to the toolkit. Composed with the results above, the comparison gives
$R\le30001\cdot\frac85\mathcal K$ for finite laws and, conditionally on the
general-law theorem, $\frac58\cdot10^{-17}Q\le R$ for every law. The
floating-point calculator above still reports the $5/3$ interval. Status:
**paper proofs**, except that the comparison's scalar Lemma 3 is **Lean-checked**
with its exact type and only the standard axioms
([audit](VERIFY.md#quantile-selection-comparison-scalar-lemma-3)). The $8/5$
comparison itself is not Lean-checked, though the weaker factor $1+2\sqrt2$ is
([upper half](#general-law-rare-event-characterization)). The certificates rely
on unverified Python. The
manuscripts above still state $1+2\sqrt2$ and are unchanged.

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
The exact Psi formula, rate and failure of a universal matching-Psi upper are
also Lean-checked. The original
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
The raw-second-moment version is also proved. The additive
[all-size extension](../lean/ThresholdHC/CriticalAllSizes/BaseCost.lean)
now gives explicit coefficients: `M E_0 T >= rho L(1+log L)/10000000000`
for a uniform raw second-moment bound `M`, and
`V E_0 T >= rho L(1+log L)/15000000000` for a uniform extended-variance
bound `V`, with the same bias, finite-work and capped-prior hypotheses.
The [current extension audit](../results/critical_all_sizes_002.json) checks
four exact targets and all 16 declarations in eight modules; the
[first record](../results/critical_all_sizes_001.json) preserves the original
proof checkpoint. No explicit population minimax coefficient is derived here.

The proof derives activation normalization, population moment identities,
good-gap selection, observable iid restarts, sign-testing entropy, and the
rarity-dependent number of scales from those guarantees. In particular,
[FiniteGap.lean](../lean/ThresholdHC/CriticalEntropy/FiniteGap.lean) proves
the BC2 bound `sum_j d_j^2 E_-j T >= K log(K)/512` when `log K >= 32`, for one observable test
serving every specified gap and sign. It constructs the information bounds
and stopping windows and does not assume fair-coin termination.
The [all-size entropy theorem](../lean/ThresholdHC/CriticalAllSizes/FiniteGap.lean)
removes the count restriction with coefficient `1/4096`. The original sharper
`1/512` theorem remains unchanged. A deterministic-prefix one-gap floor
`d^2 E_-d T >= 1/128` handles the smaller counts, including the trivial
zero-count case. The resulting explicit single-coin proof uses scale cutoff
16384 instead of a threshold containing `exp(32)`.
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
upper and explicit comparison refuting the matching-Psi conjecture are now
separately proved and audited below. The original
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

That comparison is now proved separately in
[CriticalPsi/Full.lean](../lean/ThresholdHC/CriticalPsi/Full.lean). Psi is the
actual supremum of the existing objective over all measurable feasible
allocations. Its exact attained formula gives
`min(rho,h*sqrt(rho*L)) <= Psi(rho,h) <= 16*min(rho,h*sqrt(rho*L))`
for every `0<rho<=1/4` and `h>0`. The separation theorem constructs a valid
rarity and budget for every `C>0` at which the original unrestricted minimax
risk exceeds `C*Psi(rho,1/sqrt(B))`. The
[Psi audit](../results/critical_psi_001.json) checks the frozen model and three
full targets. Its witness budget is `L*(1+log L)/rho`; the paper's specific
`rho^(-2)` sequence remains a paper derivation. This proves the conjecture
false for the fixed quadratic law and gives no arbitrary-law replacement.

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
The later [general-law entropy-tail manuscript](#general-law-rare-event-characterization)
provides the arbitrary-law replacement as an audited paper proof. The finite-gap manuscript above gives a separate
closed quantile formula for known finite laws. See the
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

## Practical comparison with a fixed plan

The [toolkit](../toolkit/README.md) implements the algorithm of
`distribution_blind_upper` and a fixed plan: $n$ fresh coins, an odd number $m$
of flips each, and the share of coins with a majority of heads. Over every sign
law at a known gap law, the fixed plan's bias is at most the mean
misclassification probability and its variance at most $1/(4n)$. The toolkit
evaluates the analytic formulas with binomial tails, using floating-point
arithmetic. The continuous uniform law uses an analytic integral rather than
a finite grid. This elementary bound is not Lean-checked, and its numerical
evaluation is subject to roundoff.

Take the ten-coin example law from the toolkit guide, with probabilities 0.9,
0.8, 0.7, 0.6, 0.55, 0.52, 0.45, 0.3, 0.2 and 0.1 drawn uniformly, and
$B=16{,}384$. The fixed plan with $m=169$ and $n=96$ has RMS error at most 0.0713
for every sign law, about $0.75\,\omega_\mu(B^{-1/2})$. On the listed signs, the
distribution-blind algorithm's simulated RMS error is 0.277, with a standard
error of about 0.012 over 200 runs. For RMS error 0.03, the planner finds a
fixed plan using 258,153 flips for every sign law. In simulation, the blind algorithm first
reaches 0.03 at budget 4,194,304 (0.0271 over 200 runs). That is an unconfirmed hit:
the planner's 95% upper confidence bound there is 0.183, and confirming 0.03 would need
at least 6,761 runs.

This is numerical evidence for one law and, for the blind algorithm, one sign
assignment. The fixed plan uses the gap law to choose $m$, as the
distribution-wise minimax benchmark permits; the blind algorithm does not know
$\mu$. The comparison does not affect the theorem or its coefficient 512. It
shows that the blind algorithm's practical constants are far from those of a
plan tuned to the law at these budgets. The planner searches a 1.25× grid of
odd flip counts and does not claim a global optimum: for example, 428 coins
with 599 flips each give another qualifying plan at 256,372 flips.
To reproduce the grid result from `toolkit/`, run
`python -m threshold_toolkit --rates 0.9,0.8,0.7,0.6,0.55,0.52,0.45,0.3,0.2,0.1`
with `--budget 16384` or `--target-error 0.03`. The seed defaults to 0.
