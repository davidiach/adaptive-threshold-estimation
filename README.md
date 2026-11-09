# Adaptive Threshold Estimation

[![Checks](https://github.com/davidiach/adaptive-threshold-estimation/actions/workflows/checks.yml/badge.svg?branch=main)](https://github.com/davidiach/adaptive-threshold-estimation/actions/workflows/checks.yml)

Minimax theory for estimating a threshold probability from noisy coin flips,
with a research manuscript, Lean 4 proofs built on Mathlib, and reproducible experiments.

**[Paper and published builds](paper/v6/README.md)** · **[Formal proof map](lean/README.md)** · **[Verification guide](docs/VERIFY.md)** · **[Specialist review packet](paper/critical-review/review.pdf)**

New contributors: start with [CONTRIBUTING.md](CONTRIBUTING.md).
AI agents: read [AGENTS.md](AGENTS.md) for current entry points, preservation
rules, and validation. The root [BRIEF.md](BRIEF.md) is the historical overnight
assignment; it is preserved as part of the [process record](docs/process/README.md).

The [consolidated v6 paper](paper/v6/README.md) combines the [v5 paper](paper/v5/README.md) with the [general-law](paper/rare-event/README.md) and [finite-gap](paper/finite-gap-rare-events/README.md) rare-event manuscripts, which are preserved unchanged.

## Problem and main result

Estimate the fraction of a population of coins whose probability of heads
exceeds one half. Each fresh coin has an independent hidden gap $D\sim\mu$
in $(0,1/2]$ and a hidden sign. An algorithm sees only its randomness and
coin flips; it may create, revisit, and interleave coins. Every flip counts
toward the expected-work budget.

Let $R_\mu(B)$ be the minimax root-mean-square error over all measurable sign
laws at uniform expected budget $B\ge1$, and define
$\omega_\mu(h)=\mathbb E_\mu[\min(1,h/D)]$ for $h>0$. Then

```math
\frac{1}{64}\,\omega_\mu(B^{-1/2})
\;\le\; R_\mu(B)
\;\le\; 512\,\omega_\mu(B^{-1/2}).
```

Both bounds are proved in Lean for the observable adaptive experiment.
One upper algorithm works for every gap law without knowing $\mu$.
The [lower theorem](lean/ThresholdHC/Tier6/Full.lean),
[upper theorem](lean/ThresholdHC/BlindUpper/Full.lean), and
[model and scope](docs/RESULTS.md) give the precise statements.

## Further results

| Result | Verification | Read more |
|---|---|---|
| General-law rare-event entropy-tail characterization, stopping dual, and sufficient-cap certificates | Paper proof with adversarial AI audits and exact finite certificates. Lean proves $10^{-17}\mathcal K\le R\le28000\mathcal K$ for every law. The stopping-dual, certificate, genie and fixed-cap identification results are also Lean-checked | [v6 §13](paper/v6/README.md#reading-guide) · [Standalone v2](paper/rare-event/README.md) · [Scope](docs/RESULTS.md#general-law-rare-event-characterization) |
| Rare-event power laws with $\alpha>2$ | Both minimax bounds proved in Lean in the observable model | [Scope and proof map](docs/RARE_ABOVE_TWO.md) |
| Critical quadratic rare-event law, including unrestricted adaptive algorithms | Both minimax bounds proved in Lean | [Statement and scope](docs/RESULTS.md#critical-power-margin-full-minimax-characterization) |
| Exact critical-law Ψ formula and counterexample to a universal matching-Ψ upper bound | Proved in Lean | [Theorems](lean/ThresholdHC/CriticalPsi/Full.lean) |
| Rare-event lower bound by the variational modulus: $10^{-17}\Psi_{\mu,\rho}(B^{-1/2})\le R_{\mu,\rho}(B)$ for every gap law, and the same for the confidence radius | Proved in Lean through $\Psi\le\mathcal K$ and the entropy-tail law, with no external statistical input | [Theorems](lean/ThresholdHC/PsiSelection/Full.lean) · [Record](results/psi-selection-20261109/README.md) |
| An estimator unbiased for every sign law, with uniformly finite variance and expected work, exists iff $I<\infty$; one universal construction has variance–work at most $713I^2$ | Proved in Lean in the observable adaptive model | [Theorems](lean/ThresholdHC/Observable713/Full.lean) · [Audit](results/observable713_001.json) |
| Unbiased converse: for such estimators, finite inverse moment is necessary and variance–work is at least $I^2/16$ | Proved in Lean in the observable adaptive model | [Theorem](lean/ThresholdHC/UnbiasedConverse/Full.lean) · [Audit](results/unbiased_converse_001.json) |
| Finite-gap entropy for every gap count; explicit single-coin base costs | Proved in Lean | [Proofs](lean/ThresholdHC/CriticalAllSizes/) · [Audit](results/critical_all_sizes_002.json) |
| Closed quantile rare-event law: direct proof for known finite gap laws, and for every law through the entropy-tail theorem | Lean proves $10^{-17}Q\le R\le30001Q$ for every law and $\mathcal K\le Q\le\frac{31}{20}\mathcal K$, and identifies the least possible factor, about $1.4626$. For finite laws a direct Lean proof gives $10^{-20}Q\le R\le30001Q$ | [v6 §14](paper/v6/README.md#reading-guide) · [Standalone manuscript](paper/finite-gap-rare-events/README.md) · [Lean scope](docs/RESULTS.md#general-law-rare-event-characterization) |
| Confidence radius $r_\mu(B,\delta)\asymp\omega_\mu(\sqrt{\log(1/\delta)/B})$ | Both bounds proved in Lean in the observable adaptive model | [Theorems](lean/ThresholdHC/Confidence/Full.lean) · [Audit](results/confidence_001.json) |
| Hard observation caps for the distribution-blind RMS rate, the critical quadratic law and the known-law rare-event rate | Lean verifies the [observable fallback controller and all three minimax bounds](results/hard-budget-rms-20261104/README.md), including a general-law upper coefficient of $160000$. | [Scope](docs/RESULTS.md#hard-observation-caps-for-the-rms-rates) · [Original paper proof](research/2026-10-30-hard-budget-rms/README.md) |
| High-confidence radius: the general-law rate is $\mathcal K(B/\log(1/\delta))$ under an expected or a hard budget, and the critical rate gains a factor $\sqrt{\log(1/\delta)}$; nested intervals stay valid under data-dependent stopping | Lean checks [both fixed-confidence rates](results/known-law-confidence-20261104/README.md) for the original observable estimator. The [known-law time-uniform rate and observable controller](results/anytime-confidence-20261105/README.md) and an [all-law time-uniform lower bound of the same order](results/anytime-asymptotic-20261105/README.md) are also Lean-checked; the two are not composed in Lean | [Scope](docs/RESULTS.md#confidence-rates-and-sequential-stopping) · [Package](research/2026-10-30-confidence-transfer/README.md) |
| RMS and confidence lower bounds with revealed or adaptively selected magnitudes | Proved in Lean in canonical oracle models | [Theorems](lean/ThresholdHC/OracleLower/Full.lean) · [Audit](results/oracle_lower_001.json) |
| $\Psi$ equals the closed quantile form without its entropy, within a factor $\sqrt2$; $\Psi\le\mathcal K$; one power-margin rate with constants independent of the exponent, through $\alpha=2$ | Paper proofs from Corollary 14.6 and Theorem S.6 of v6 and elementary inequalities; a floating-point check. Lean checks only [$\Psi\le\mathcal K$](lean/ThresholdHC/PsiSelection/Full.lean) | [v6 §14.8](paper/v6/psi-window.tex) · [Check](research/2026-11-09-psi-closed-form/README.md) · [Scope](docs/RESULTS.md#the-variational-modulus-in-closed-form) |
| Unknown-rarity obstruction, unknown-law confidence sequences, the earlier additive-class critical note, and the population and nonlinear-feedback follow-ups | Paper proofs; not Lean-checked. The power-margin rates below exponent two, the sharp quantile factor, the time-uniform lower bound and the stochastic-envelope, smooth-density and observed-state results are Lean-checked; see [Scope and review](#scope-and-review) | [Full results guide](docs/RESULTS.md) |

Here $I=\mathbb E_\mu[D^{-1}]$ is the inverse-gap moment.

For the critical law $F(d)=(4d)^2$ on $(0,1/4]$, with known rarity bound
$0<\rho\le1/4$, the minimax RMS rate is

```math
R_{\mu,\rho}(B)\asymp
\min\!\left\{\rho,\sqrt{\frac{\rho L(1+\log L)}{B}}\right\},
\qquad L=1+\log(1/\rho),\quad B\ge1.
```

The extra scale-entropy factor refutes the proposed matching-Ψ characterization.
The separate [general-law manuscript](paper/rare-event/README.md) now gives an
entropy-tail replacement for known gap law and rarity. Lean checks the explicit
coefficients $10^{-17}$ and $28000$, along with the stopping-program,
identification and genie results in their stated scopes. The finite-gap
manuscript gives the corresponding closed quantile formula and a separate
direct proof for finite laws. The existing all-count Lean entropy coefficient is 1/4096; the sharper 1/512 bound retains its large-count assumption.
The explicit new base-cost constants apply to single-coin procedures.

## Finite-gap rare-event manuscript

This standalone manuscript is §14 and Appendix O of the [consolidated v6 paper](paper/v6/README.md).

[Read the 32-page paper](paper/finite-gap-rare-events/paper.pdf) · [LaTeX sources and build instructions](paper/finite-gap-rare-events/README.md) · [Provenance](paper/finite-gap-rare-events/PROVENANCE.md) · [Revision 2 (35-page PDF)](paper/finite-gap-rare-events/revision-2/paper.pdf) · [Revision 2 notes](paper/finite-gap-rare-events/revision-2/README.md)

Revision 2 adds a section showing that $Q$ is within a factor $1+2\sqrt2$ of
the general-law selection functional, so this theorem is the finite-law case
of the general-law characterization rather than an independent one. That
comparison is now proved in Lean.

The new [computation note](docs/RARE_EVENT_COMPUTATION.md) tightens that
deterministic comparison to $\mathcal K\le Q\le(5/3)\mathcal K$ for every
positive-gap law, with a complete paper proof. The
[finite-law calculator](toolkit/README.md#3-compute-the-rare-event-rate-for-a-known-finite-law)
evaluates $Q$, its tail and entropy contributions, and its target-value
inverse without subset search. The calculator's floating-point evaluation
is unverified. Lean proves the [sharper comparison](lean/ThresholdHC/QuantileSelection/Full.lean)
from the [certified-selection note](research/2026-10-30-certified-selection/README.md),
$\mathcal K\le Q\le(8/5)\mathcal K$, for every positive-gap law in the same
parameter range. A later [Lean proof](results/quantile-price-20261104/README.md)
lowers the upper factor to $31/20$. The [optimal factor](docs/OPTIMAL_QUANTILE_FACTOR.md) is the
unique root of a scalar equation and lies strictly between $1.462554551279$
and $1.462554551280$. Its characterization, all-law comparison and finite-law sharpness are [Lean-checked](results/quantile-optimality-20261105/README.md). The decimal bracket has a separate rational certificate.
For a finite law, Lean also proves that a hard optimizer selects an upper-gap
suffix within each dyadic band. With $n_j$ atoms in occupied band $j$, at most
$\prod_j(n_j+1)$ candidates suffice. [Suffix theorem and search bound](lean/ThresholdHC/BandwiseSuffix/Search.lean)

For a **known finite** magnitude law with strictly positive gaps, known global
rarity bound $0<\rho\le1/4$, and any uniform expected observation budget $B>0$,
Theorem 1.1 gives

```math
10^{-20}\,Q(B)\le R_{\mu,\rho}(B)\le30001\,Q(B),\qquad
Q(B)=\min\{\rho,T_h+h\sqrt{\rho\Gamma_\kappa}\},\quad h=B^{-1/2}.
```

Here $\nu$ is exactly the smallest-gap mass $\rho$, $\kappa=\mu-\nu$ is the
remaining mass, $T_h=\int\min(1,h/d)\,\nu(dd)$, and $\Gamma_\kappa$ is its
dyadic inverse-square cost entropy, defined in the paper. The unknown sign
law satisfies $0\le q\le1$ and $\int q\,d\mu\le\rho$; rarity is not imposed
separately at each gap. Fresh coins have iid complete latent pairs which
persist on revisits, and the algorithm may create, revisit and interleave
coins adaptively. Only physical observations are charged.

**Verification status:** this is a complete paper-proof draft with a
fresh-context AI review of its precursor. The two-sided closed-quantile
rate is now Lean-checked for every probability law with lower coefficient
$10^{-17}$ and upper coefficient 30001
([scope](docs/RESULTS.md#general-law-rare-event-characterization)). For finite
laws, the [direct proof](lean/ThresholdHC/FiniteQuantile/Full.lean) gives
the lower coefficient $10^{-20}$. One observable estimator achieves the upper
coefficient uniformly over the allowed priors. The finite-law theorem assumes
a known gap law and a uniform expected budget.

## Check the proofs

Install Python 3.12 and Lean's `elan` tool manager. The repository pins its
[Lean toolchain](lean/lean-toolchain) and [Mathlib revision](lean/lake-manifest.json).
To check both directions of the main RMS law:

```sh
git clone https://github.com/davidiach/adaptive-threshold-estimation.git
cd adaptive-threshold-estimation
python -m pip install -r requirements.txt
cd lean
lake exe cache get
cd ..
python tools/verify_tier6.py --sequential --require-complete
python tools/verify_blind_upper_components.py --sequential
```

The [verification guide](docs/VERIFY.md) covers the other theorems, exact target
types, transitive-axiom audits, source hashes, and numerical checks.
[GitHub Actions](.github/workflows/checks.yml) runs the complete suite.
Use a disposable checkout for reproduction: some checks write diagnostic files.

## Navigate the project

- **Read the mathematics:** [consolidated v6 paper](paper/v6/README.md);
  its preserved sources, the [v5 paper](paper/v5/README.md),
  [general-law rare-event manuscript](paper/rare-event/README.md) and
  [finite-gap rare-event manuscript](paper/finite-gap-rare-events/README.md);
  the [critical-result review packet](paper/critical-review/README.md);
  and [claims with exact assumptions](docs/RESULTS.md).
- **Inspect the formalization:** [theorem and module map](lean/README.md),
  [main upper-bound scope](docs/BLIND_UPPER.md),
  [critical-law audit](docs/CRITICAL_AUDIT.md), and the
  [model-fidelity brief](docs/MODEL_FIDELITY.md), which sets the paper's
  model beside the Lean definitions for a specialist reviewer.
- **Reproduce the evidence:** [checks by task](docs/VERIFY.md#choose-checks-by-task),
  [verification tools](tools/README.md), [evidence index](results/README.md),
  and [benchmarks](benchmark/).
- **Follow the research:** [remaining work](docs/WORKPLAN.md),
  [research index](research/README.md), and [process note](docs/process/METHOD.md).
- **Use it on your own problem:** the [toolkit](toolkit/README.md) plans a flip
  budget and runs the estimators. It compares a majority-vote plan tuned to a
  guessed gap law with the distribution-blind algorithm, including simulations
  and their limits.
- **Contribute:** [setup and editing guide](CONTRIBUTING.md),
  [agent instructions](AGENTS.md), and [current priorities](docs/WORKPLAN.md#current-priorities).

## Scope and review

Lean verifies the linked mathematical statements and their definitions;
coverage of the manuscript is recorded claim by claim. The work has received
AI review and has not had independent external specialist review; the
[model-fidelity brief](docs/MODEL_FIDELITY.md) prepares one. Numerical
experiments provide supporting evidence, not proofs of universal claims.

<!-- BEGIN status summary: generated by tools/build_status_docs.py from paper/v6/status.json; do not edit by hand -->
The [status source](paper/v6/status.json) of the v6 abstract lists 31 results: 29 Lean-checked and 2 with paper proofs only. Run `python tools/build_status_docs.py` after changing it.

| Result | Status | Evidence |
|---|---|---|
| Original RMS law in both directions, with coefficients $1/64$ and $512$ and one distribution-blind upper algorithm | Lean-checked | [Tier6/Full.lean](lean/ThresholdHC/Tier6/Full.lean) · [BlindUpper/Full.lean](lean/ThresholdHC/BlindUpper/Full.lean) |
| Critical minimax law | Lean-checked | [CriticalEntropy/CriticalMinimax.lean](lean/ThresholdHC/CriticalEntropy/CriticalMinimax.lean) · [CriticalUpper/Full.lean](lean/ThresholdHC/CriticalUpper/Full.lean) |
| Exact $\Psi$ comparison and counterexample | Lean-checked | [CriticalPsi/Full.lean](lean/ThresholdHC/CriticalPsi/Full.lean) |
| Variational optimizer | Lean-checked | [Tier3/Optimizer.lean](lean/ThresholdHC/Tier3/Optimizer.lean) |
| Unbiased characterization with coefficients $1/16$ and $713$ | Lean-checked | [UnbiasedConverse/Full.lean](lean/ThresholdHC/UnbiasedConverse/Full.lean) · [Observable713/Full.lean](lean/ThresholdHC/Observable713/Full.lean) |
| Confidence characterization | Lean-checked | [Confidence/Full.lean](lean/ThresholdHC/Confidence/Full.lean) |
| Magnitude-oracle lower bounds | Lean-checked | [OracleLower/Full.lean](lean/ThresholdHC/OracleLower/Full.lean) |
| Rare-event rate above exponent two | Lean-checked | [RareAboveTwo/Full.lean](lean/ThresholdHC/RareAboveTwo/Full.lean) |
| Two-sided entropy–tail law | Lean-checked | [EntropyTail/Law.lean](lean/ThresholdHC/EntropyTail/Law.lean) · [entropy-tail-complete-20261101 record](results/entropy-tail-complete-20261101/README.md) |
| Two-sided closed-quantile law | Lean-checked | [ClosedQuantile/Full.lean](lean/ThresholdHC/ClosedQuantile/Full.lean) · [closed-quantile-law-20261101 record](results/closed-quantile-law-20261101/README.md) |
| Deterministic quantile comparison | Lean-checked | [QuantilePrice/Full.lean](lean/ThresholdHC/QuantilePrice/Full.lean) · [quantile-price-20261104 record](results/quantile-price-20261104/README.md) |
| Stopping-program duality and the risk certificates | Lean-checked | [StoppingProgram/BellmanTheorem.lean](lean/ThresholdHC/StoppingProgram/BellmanTheorem.lean) · [StoppingProgram/FiniteCertificate.lean](lean/ThresholdHC/StoppingProgram/FiniteCertificate.lean) · [rare-event-full-20261031 record](results/rare-event-full-20261031) |
| Fixed-cap identification | Lean-checked | [CapIdentification/Full.lean](lean/ThresholdHC/CapIdentification/Full.lean) |
| Genie limits | Lean-checked | [Genie/OptimizedConvergence.lean](lean/ThresholdHC/Genie/OptimizedConvergence.lean) · [GenieRate/Full.lean](lean/ThresholdHC/GenieRate/Full.lean) |
| Entropy–tail coefficients $10^{-17}$ and $28000$ for every known gap law | Lean-checked | [EntropyTailSharp/Full.lean](lean/ThresholdHC/EntropyTailSharp/Full.lean) · [entropy-tail-explicit-20261104 record](results/entropy-tail-explicit-20261104/README.md) |
| Arbitrary-law statistical $\Psi$ lower bound with coefficient $10^{-17}$, through the entropy–tail law | Lean-checked | [PsiSelection/Full.lean](lean/ThresholdHC/PsiSelection/Full.lean) · [psi-selection-20261109 record](results/psi-selection-20261109/README.md) |
| Separate direct closed-quantile bounds for finite laws, with coefficients $10^{-20}$ and $30001$ | Lean-checked | [FiniteQuantile/Full.lean](lean/ThresholdHC/FiniteQuantile/Full.lean) · [direct-finite-quantile-20261104 record](results/direct-finite-quantile-20261104/README.md) |
| Power-margin rates below exponent two | Lean-checked | [SubcriticalPower/Full.lean](lean/ThresholdHC/SubcriticalPower/Full.lean) · [ShiftedPower/Full.lean](lean/ThresholdHC/ShiftedPower/Full.lean) |
| Smooth-density rates | Lean-checked | [SmoothDensity/Full.lean](lean/ThresholdHC/SmoothDensity/Full.lean) |
| Observed-state rates | Lean-checked | [ObservedState/Finite.lean](lean/ThresholdHC/ObservedState/Finite.lean) · [ContinuousObserved/UniformLower.lean](lean/ThresholdHC/ContinuousObserved/UniformLower.lean) · [ContinuousObserved/UniformUpper.lean](lean/ThresholdHC/ContinuousObserved/UniformUpper.lean) |
| Selected-type information transfer | Lean-checked | [TypedConfidence/SignTransfer.lean](lean/ThresholdHC/TypedConfidence/SignTransfer.lean) · [adaptive-types-20261105 record](results/adaptive-types-20261105/README.md) |
| General-law confidence coefficients $10^{-17}$ and $750000$ | Lean-checked | [ConfidenceProgram/Upper.lean](lean/ThresholdHC/ConfidenceProgram/Upper.lean) · [ConfidenceEntropy/Full.lean](lean/ThresholdHC/ConfidenceEntropy/Full.lean) · [Anytime/Full.lean](lean/ThresholdHC/Anytime/Full.lean) |
| Matching all-law time-uniform lower bound | Lean-checked | [AnytimeLower/Full.lean](lean/ThresholdHC/AnytimeLower/Full.lean) · [AnytimeLower/Intervals.lean](lean/ThresholdHC/AnytimeLower/Intervals.lean) · [anytime-asymptotic-20261105 record](results/anytime-asymptotic-20261105/README.md) |
| Characterization of the sharp quantile factor as the unique root of its scalar equation, over all gap laws and over finite-support laws | Lean-checked | [QuantileOptimality/Full.lean](lean/ThresholdHC/QuantileOptimality/Full.lean) · [quantile-optimality-20261105 record](results/quantile-optimality-20261105/README.md) |
| Stochastic-envelope extension to unknown gap laws for RMS, confidence and unbiased estimation | Lean-checked | [Envelope/Minimax.lean](lean/ThresholdHC/Envelope/Minimax.lean) · [Envelope/Unbiased.lean](lean/ThresholdHC/Envelope/Unbiased.lean) · [stochastic-envelope-20261105 record](results/stochastic-envelope-20261105/README.md) |
| Lower-bound localization with coefficient $1/128$, conditional on a single-coin variance–null-work obstruction | Lean-checked | [ConfidenceLocalization/ConfidenceRate.lean](lean/ThresholdHC/ConfidenceLocalization/ConfidenceRate.lean) · [AdditiveConfidence/Full.lean](lean/ThresholdHC/AdditiveConfidence/Full.lean) · [RMSLocalization/Full.lean](lean/ThresholdHC/RMSLocalization/Full.lean) · [common-pair-20261105 record](results/common-pair-20261105/README.md) · [additive-confidence-20261105 record](results/additive-confidence-20261105/README.md) · [rms-localization-20261105 record](results/rms-localization-20261105/README.md) |
| Finite-menu cost grouping and the exact optimized value of concrete finite-law menus | Lean-checked | [BandCostSelection/Counting.lean](lean/ThresholdHC/BandCostSelection/Counting.lean) · [GapLawMenus/Full.lean](lean/ThresholdHC/GapLawMenus/Full.lean) · [band-cost-formal-20261105 record](results/band-cost-formal-20261105/README.md) · [gap-law-menus-20261105 record](results/gap-law-menus-20261105/README.md) |
| Oracle-rate adaptation within a supplied finite family of gap laws, including its paid pilot | Lean-checked | [LawAdaptation/Full.lean](lean/ThresholdHC/LawAdaptation/Full.lean) · [law-adaptation-realization-20261105 record](results/law-adaptation-realization-20261105/README.md) |
| Eventual oracle-rate adaptation over arbitrary unknown gap laws | Paper proof | [arbitrary-law-adaptation.tex](paper/v6/arbitrary-law-adaptation.tex) · [ARBITRARY_LAW_ADAPTATION.md](docs/ARBITRARY_LAW_ADAPTATION.md) |
| Closed form of $\Psi$ within a factor $\sqrt2$, its distance from the rate, and the power-margin rate uniform in the exponent | Paper proof | [psi-window.tex](paper/v6/psi-window.tex) · [README.md](research/2026-11-09-psi-closed-form/README.md) |
| Hard-cap results of [RMS guarantees under a deterministic observation cap](paper/v6/appendix-hard-budget.tex) | Lean-checked | [HardBudget/Full.lean](lean/ThresholdHC/HardBudget/Full.lean) · [hard-budget-rms-20261104 record](results/hard-budget-rms-20261104/README.md) |
<!-- END status summary -->

Lean-checked components not yet in the status source, because the v6 manuscript does not yet describe them as checked:

- **Arbitrary-law adaptation components:** checked components of the proof, including entropy transport, the CDF envelope and the observable paid learning stage. The [formal scope](docs/ARBITRARY_LAW_FORMALIZATION.md) lists each component, its exact-statement count and the work that remains. The theorem itself is a paper proof.
- **Finite-law selection approximation components:** entropy perturbation and state compression, assuming a certified bin map. The approximation scheme itself, which returns a selection within $(1+\epsilon)K$ in polynomial time, is a paper proof ([components](lean/ThresholdHC/SelectionApproximation/README.md), [record](results/selection-approximation-20261106/README.md), [note](research/2026-11-06-selection-approximation/NOTE.md)).

See the [completion ledger](docs/WORKPLAN.md) for the current boundary.

## Attribution and license

AI agents carried out the research and formalization under David Iach's
direction. The [process note](docs/process/METHOD.md) and
[provenance record](docs/process/PROVENANCE.md) document the workflow and review limits.

Use [CITATION.cff](CITATION.cff) to cite this work. Code and Lean files are
licensed under [Apache-2.0](LICENSE); the paper and documentation are licensed
under [CC BY 4.0](LICENSE-CC-BY-4.0). See [license scope](LICENSES.md).
