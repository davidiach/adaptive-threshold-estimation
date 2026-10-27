# Results and verification scope

This guide distinguishes complete Lean specifications from broader paper claims. Sources are the unchanged [v4 paper](../paper/paper.pdf), its [TeX](../paper/paper.tex), the [rare-event continuation](../inputs/next-phase/report/research_note.pdf), and the theorem files below.

## Paper review scope

The [response to the final Opus review](../inputs/next-phase/baseline/Adaptive_Threshold_v4/review/RESPONSE_TO_OPUS.md) records agent review of components incorporated into v4, including the budget-only algorithm and symmetric-KL converse. It explicitly says that the consolidated manuscript has not received independent specialist review. “Paper proof” therefore does not imply external peer review or a complete Lean proof. The later 713 argument, bias counterexample, and unknown-rarity obstruction have a separate [independent agent review](../proposals/RESEARCH_REVIEW.md), whose author did not write those arguments.

## Minimax law and unbiasedness

[Theorem 1 in §2](../paper/paper.tex#L239) defines the minimax RMS risk

$$R_\mu(B)=\inf_{\mathcal A:\,\sup_q\mathbb E_{\mu,q}T\le B}\ \sup_q\bigl(\mathbb E_{\mu,q}(\widehat\theta-\theta)^2\bigr)^{1/2}.$$

For every probability law $\mu$ on $(0,1/2]$, $B\ge1$, and $0<\delta\le1/4$, it proves

$$R_\mu(B)\asymp\omega_\mu(B^{-1/2}),\qquad r_\mu(B,\delta)\asymp\omega_\mu\!\left(\sqrt{\log(1/\delta)/B}\right),\qquad \omega_\mu(h)=\mathbb E_\mu\min\{1,h/D\}.$$

Here $r_\mu(B,\delta)$ is the minimax uniform error radius at failure probability at most $\delta$, with the same expected-budget constraint. The constants are universal. The algorithms depend only on $B$, or on $(B,\delta)$, and observe neither magnitudes nor their law. The proof is in §5. The full algorithm-level theorem has paper-proof status; component Lean lemmas do not certify it.

[Theorem 2 and §6](../paper/paper.tex#L272) quantify over every measurable sign function $q$ at a fixed $\mu$. Put $I=\mathbb E_\mu[D^{-1}]$, $V=\sup_q\operatorname{Var}_{\mu,q}(Y)$, and $\overline W=\sup_q\mathbb E_{\mu,q}W$. An estimator unbiased for all such $q$ can have $V,\overline W<\infty$ exactly when $I<\infty$, and every such estimator satisfies $V\overline W\ge I^2/16$. These are uniform bounds, not a lower bound for each individual population. The theorem and converse remain paper proofs. The fixed-gap example attaining the lower coefficient is in §6, equation `eq:fixed-gap-sharp`; it does not identify the optimum for every nondegenerate law.

## The 713 construction

`ThresholdHC.Uniform713.full_bound_713` in [FullBound.lean](../lean/ThresholdHC/Uniform713/FullBound.lean) inhabits [FullBound713Statement](../lean/ThresholdHC/Uniform713/Specification.lean). For classifier parameters $(k_1,k_2)=(1/4,1)$ and the geometric single-term estimator, it proves square integrability, finite expected actual work, unbiasedness, and

$$\operatorname{Var}(Y)\mathbb E W<713\left(\mathbb E[D^{-1}]\right)^2.$$

Its assumptions describe an arbitrary magnitude/sign probability space, a conditional observation kernel, independent measurable observations in $[0,1]$ with means $1/2\pm D$, $0<D\le1/2$ almost surely, and an integrable inverse magnitude. Bernoulli observations are included. No classifier error, moment, work, or unbiasedness conclusion is an assumption. The random level has unbounded support. See the [kernel audit](../results/uniform713_status.json) and [paper argument](../proposals/constants/UNIFORM_PRODUCT_BOUND.md).

## Information and stopping

Fix a finite set of $m$ coins with magnitudes $0<d_i\le1/2$. The hypotheses have sign probabilities $q_\pm(i)=1/2\pm\eta_i$, where $0\le\eta_i\le1/8$, $h>0$, and $d_i\eta_i\le h/8$. Policies adapt to observation history. Write $T_n$ for actual work by finite horizon $n$.

- `ThresholdHC.Proofs.stopped_transcript_kl` in [Transcript.lean](../lean/ThresholdHC/Proofs/Tier2/Transcript.lean) proves $\operatorname{KL}(\mathsf P_{+,n},\mathsf P_{-,n})\le(128/225)h^2\mathbb E_+T_n$ for the explicit laws in [Statements2.lean](../lean/ThresholdHC/Statements2.lean).
- `ThresholdHC.Tier3.randomized_information_bound` in [RandomizedBase.lean](../lean/ThresholdHC/Tier3/RandomizedBase.lean) proves the average conditional information bound for an arbitrary common measurable random seed. `ThresholdHC.Tier3.randomized_marginal_kl_bound` and `ThresholdHC.Tier3.randomized_testing_bound` in [Randomized.lean](../lean/ThresholdHC/Tier3/Randomized.lean) handle the seed-marginal transcript and tests allowed to observe the seed. See [RandomizedModel.lean](../lean/ThresholdHC/Tier3/RandomizedModel.lean) for assumptions.
- `ThresholdHC.Tier3.unbounded_stopping` in [StoppingBase.lean](../lean/ThresholdHC/Tier3/StoppingBase.lean) derives almost-sure halting under both hypotheses from finite expected actual work under the plus hypothesis alone. `ThresholdHC.Tier3.unbounded_testing` in [Stopping.lean](../lean/ThresholdHC/Tier3/Stopping.lean) proves $\operatorname{kl}(1-\delta,\delta)\le(128/225)h^2\mathbb E_+T$ for $0<\delta<1/2$ when both terminal-test errors are at most $\delta$. [StoppingModel.lean](../lean/ThresholdHC/Tier3/StoppingModel.lean) requires finite-prefix laws to realize the explicit experiment; it does not assume termination or the information bound.
- `ThresholdHC.Tier3.unbounded_example` in [Examples.lean](../lean/ThresholdHC/Tier3/Examples.lean) supplies a geometric-seed experiment with finite expected work and positive probability of exceeding every finite cap.

The unbounded formal experiment still has a fixed finite set of coins. It is a terminal-testing theorem, not a measure-theoretic KL identity for the entire infinite transcript. [Paper §3, Proposition 5](../paper/paper.tex#L425) states the broader stopped-transcript result for its coin-creation experiment; that full scope has paper-proof status. The [audit record](../results/tier3_status.json) lists the formalized targets and allowed axioms.

## Rare-event optimizer

For any magnitude law $\mu$ on $(0,1/2]$, $0<\rho<1$, and $h>0$, define

$$\Psi_{\mu,\rho}(h)=\sup_{\substack{v\text{ measurable},\ 0\le v\le1\\\mathbb E_\mu v(D)\le\rho}}\mathbb E_\mu\min\{v(D),h\sqrt{v(D)}/D\}.$$

`ThresholdHC.Tier3.arbitrary_law_cutoff` and `ThresholdHC.Tier3.arbitrary_law_optimizer` in [Optimizer.lean](../lean/ThresholdHC/Tier3/Optimizer.lean) prove a unique $t\in(0,1/2)$ satisfies $\mathbb E_\mu\min\{1,t^2/D^2\}=\rho$, and $v_*(d)=\min\{1,t^2/d^2\}$ is an optimizer for every $h>0$. They prove saturation at $\rho$ for $h\ge t$ and, for $h<t$,

$$\Psi_{\mu,\rho}(h)=\Pr(D\le h)+h\mathbb E[D^{-1};h<D\le t]+ht\mathbb E[D^{-2};D>t].$$

The [specification](../lean/ThresholdHC/Tier3/OptimizerModel.lean) permits atoms and singular laws and assumes no finite inverse moment. It formalizes the identity in [continuation §3.3](../inputs/next-phase/report/research_note.tex#L218). A matching arbitrary-law statistical upper bound remains conjectural. The matching rare-event construction in its §4 covers power margins $F(d)=(d/a)^\alpha$ on $(0,a]$ for $0<\alpha<2$, not $\alpha\ge2$.

## Unknown rarity and numerical evidence

The [unknown-rarity obstruction](process/TRACK_D.md#an-obstruction-to-completely-uniform-adaptation-to-unknown-rarity) concerns a budget-indexed estimator family independent of the rarity bound. For a known fixed $0<d<1/2$ and almost-sure stopping at every constant sign prior in $[0,1/4]$, no universal finite $C$ gives RMS error at most $C\min\{\rho,\sqrt\rho/(d\sqrt B)\}$ for every $B\ge1$, $0<\rho\le1/4$, and $\theta\in[0,\rho]$. This is an independently agent-reviewed paper proof. It does not rule out an additive error floor, a positive lower bound on rarity, or an algorithm given $\rho$.

[Constant scores](../results/constants_theory.json), [upper-bracket evaluations](../results/power_bracket.json), and [held-out benchmark summaries](../results/real_test.json) are numerical evidence. Finite grids, truncation, floating-point arithmetic, and benchmark-specific assumptions do not yield universal theorems. See the [off-grid counterexample](../proposals/constants/BIAS_AUDIT.md) and [benchmark report](process/TRACK_C.md).
