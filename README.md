# Adaptive Threshold Estimation

[![Checks](https://github.com/davidiach/adaptive-threshold-estimation/actions/workflows/checks.yml/badge.svg?branch=main)](https://github.com/davidiach/adaptive-threshold-estimation/actions/workflows/checks.yml)

Minimax theory for estimating a threshold probability from noisy coin flips,
with a research manuscript, Lean 4 proofs built on Mathlib, and reproducible experiments.

**[Paper](paper/v6/paper.pdf)** · **[Formal proof map](lean/README.md)** · **[Verification guide](docs/VERIFY.md)** · **[Specialist review packet](paper/critical-review/review.pdf)**

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
| General-law rare-event entropy-tail characterization, stopping dual, and sufficient-cap certificates | Paper proof with adversarial AI audits and exact finite certificates; new general claims not Lean-formalized | [v6 §13](paper/v6/README.md#reading-guide) · [Standalone v2](paper/rare-event/README.md) · [Scope](docs/RESULTS.md#general-law-rare-event-characterization) |
| Rare-event power laws with $\alpha>2$ | Both minimax bounds proved in Lean in the observable model | [Scope and proof map](docs/RARE_ABOVE_TWO.md) |
| Critical quadratic rare-event law, including unrestricted adaptive algorithms | Both minimax bounds proved in Lean | [Statement and scope](docs/RESULTS.md#critical-power-margin-full-minimax-characterization) |
| Exact critical-law Ψ formula and counterexample to a universal matching-Ψ upper bound | Proved in Lean | [Theorems](lean/ThresholdHC/CriticalPsi/Full.lean) |
| An estimator unbiased for every sign law, with uniformly finite variance and expected work, exists iff $I<\infty$; one universal construction has variance–work at most $713I^2$ | Proved in Lean in the observable adaptive model | [Theorems](lean/ThresholdHC/Observable713/Full.lean) · [Audit](results/observable713_001.json) |
| Unbiased converse: for such estimators, finite inverse moment is necessary and variance–work is at least $I^2/16$ | Proved in Lean in the observable adaptive model | [Theorem](lean/ThresholdHC/UnbiasedConverse/Full.lean) · [Audit](results/unbiased_converse_001.json) |
| Finite-gap entropy for every gap count; explicit single-coin base costs | Proved in Lean | [Proofs](lean/ThresholdHC/CriticalAllSizes/) · [Audit](results/critical_all_sizes_002.json) |
| Closed quantile rare-event law: direct proof for known finite gap laws, and for every law through the entropy-tail theorem | Paper proofs; not Lean-checked | [v6 §14](paper/v6/README.md#reading-guide) · [Standalone manuscript](paper/finite-gap-rare-events/README.md) |
| Confidence radius $r_\mu(B,\delta)\asymp\omega_\mu(\sqrt{\log(1/\delta)/B})$ | Both bounds proved in Lean in the observable adaptive model | [Theorems](lean/ThresholdHC/Confidence/Full.lean) · [Audit](results/confidence_001.json) |
| Hard observation caps: the RMS law, the critical law and the general-law rare-event rate hold with at most $\lfloor B\rfloor$ flips on every path, at a factor $\sqrt{32}$ | Paper proof; not Lean-checked. The first two inherit Lean-checked expected-budget bounds, the third the paper-only entropy-tail theorem | [Scope](docs/RESULTS.md#hard-observation-caps-for-the-rms-rates) · [Package](research/2026-10-30-hard-budget-rms/README.md) |
| RMS and confidence lower bounds with revealed or adaptively selected magnitudes | Proved in Lean in canonical oracle models | [Theorems](lean/ThresholdHC/OracleLower/Full.lean) · [Audit](results/oracle_lower_001.json) |
| Other rare-event regimes and auxiliary results | Paper proofs; formalization incomplete | [Full results guide](docs/RESULTS.md) |

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
entropy-tail replacement for known gap law and rarity, as an audited paper
proof. Its general characterization and stopping-program claims await Lean
formalization. The finite-gap manuscript below gives a closed quantile formula
for known finite laws, also as a paper proof. The existing all-count Lean entropy coefficient is 1/4096; the sharper 1/512 bound retains its large-count assumption.
The explicit new base-cost constants apply to single-coin procedures.

## Finite-gap rare-event manuscript

This standalone manuscript is §14 and Appendix O of the [consolidated v6 paper](paper/v6/README.md).

[Read the 32-page paper](paper/finite-gap-rare-events/paper.pdf) · [LaTeX sources and build instructions](paper/finite-gap-rare-events/README.md) · [Provenance](paper/finite-gap-rare-events/PROVENANCE.md) · [Revision 2 (35-page PDF)](paper/finite-gap-rare-events/revision-2/paper.pdf) · [Revision 2 notes](paper/finite-gap-rare-events/revision-2/README.md)

Revision 2 adds a section showing that $Q$ is within a factor $1+2\sqrt2$ of
the general-law selection functional, so this theorem is the finite-law case
of the general-law characterization rather than an independent one.

The new [computation note](docs/RARE_EVENT_COMPUTATION.md) tightens that
deterministic comparison to $\mathcal K\le Q\le(5/3)\mathcal K$ for every
positive-gap law, with a complete paper proof. The
[finite-law calculator](toolkit/README.md#3-compute-the-rare-event-rate-for-a-known-finite-law)
evaluates $Q$, its tail and entropy contributions, and its target-value
inverse without subset search. The new comparison and Python implementation
are not Lean-checked; the calculator reports a rate functional, not achieved
estimation error. The
[certified-selection package](research/2026-10-30-certified-selection/README.md)
sharpens the comparison further to $8/5$, also as a paper proof whose scalar
Lemma 3 is Lean-checked; the best factor lies between $1.4604$ and $8/5$.

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
fresh-context AI review of its precursor. The closed quantile theorem and
its full argument are **not Lean-checked** and have not received external
specialist review. The Lean-checked finite-gap entropy and critical-law
results above do not certify this new theorem. Its constants are not
optimized; it does not assert a deterministic total budget, an unknown-law
guarantee, an infinite-support extension or a high-confidence result.

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
  [main upper-bound scope](docs/BLIND_UPPER.md), and
  [critical-law audit](docs/CRITICAL_AUDIT.md).
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
AI review and has not had independent external specialist review. Numerical
experiments provide supporting evidence, not proofs of universal claims.

The finite-gap closed quantile theorem is currently a paper proof, separate
from the linked Lean-checked statements.
The next formalization targets include the new general-law rare-event
characterization and stopping-program arguments, the remaining paper-only
regimes, and auxiliary results on envelopes, smooth densities, and observed
outer states. Tighter constants and efficient selection algorithms remain
research directions; the quantile-to-selection factor is now known to lie in
$(1.4604,8/5]$. See the [completion ledger](docs/WORKPLAN.md) for the current boundary.

## Attribution and license

AI agents carried out the research and formalization under David Iach's
direction. The [process note](docs/process/METHOD.md) and
[provenance record](docs/process/PROVENANCE.md) document the workflow and review limits.

Use [CITATION.cff](CITATION.cff) to cite this work. Code and Lean files are
licensed under [Apache-2.0](LICENSE); the paper and documentation are licensed
under [CC BY 4.0](LICENSE-CC-BY-4.0). See [license scope](LICENSES.md).
