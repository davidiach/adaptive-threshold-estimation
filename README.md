# Adaptive Threshold Estimation

[![Checks](https://github.com/davidiach/adaptive-threshold-estimation/actions/workflows/checks.yml/badge.svg?branch=main)](https://github.com/davidiach/adaptive-threshold-estimation/actions/workflows/checks.yml)

A population of coins has hidden biases. How many flips does it take to
estimate the fraction of coins that favour heads? This repository answers the
question up to constant factors. It holds a research paper, proofs checked in
Lean 4 with Mathlib, and a Python toolkit.

## Start here

| If you want to | Open |
|---|---|
| Read the paper | [paper/v6](paper/v6/README.md), which links the current PDF |
| See what is proved, with exact assumptions | [docs/RESULTS.md](docs/RESULTS.md) |
| Check a proof yourself | [Check the proofs](#check-the-proofs), then [docs/VERIFY.md](docs/VERIFY.md) |
| Browse the Lean formalization | [lean/README.md](lean/README.md) |
| Run the estimators on your own problem | [toolkit/README.md](toolkit/README.md) |
| See what is unfinished | [docs/WORKPLAN.md](docs/WORKPLAN.md) and the [tracking issue](https://github.com/davidiach/adaptive-threshold-estimation/issues/76) |
| Find a particular file or folder | [Repository map](#repository-map) |
| Contribute | [CONTRIBUTING.md](CONTRIBUTING.md); AI agents also read [AGENTS.md](AGENTS.md) |

## The problem and the main result

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
[model and scope](docs/RESULTS.md#minimax-law-and-unbiasedness) give the
precise statements.

## Results at a glance

Each row is a summary. [docs/RESULTS.md](docs/RESULTS.md) states the exact
assumptions, constants and Lean theorem behind it.

**For every sign law.** The worst case is over every way the sign can depend
on the gap, at a fixed gap law $\mu$.

| Result | Status | Details |
|---|---|---|
| RMS error within $1/64$ and $512$ of $\omega_\mu(B^{-1/2})$, attained by one algorithm that knows only the budget | Lean-checked | [Scope](docs/RESULTS.md#minimax-law-and-unbiasedness) |
| Confidence radius of order $\omega_\mu\bigl(\sqrt{\log(1/\delta)/B}\bigr)$ | Lean-checked | [Scope](docs/RESULTS.md#minimax-law-and-unbiasedness) |
| An unbiased estimator with finite variance and expected work exists exactly when $I=\mathbb E_\mu[D^{-1}]$ is finite; the best variance–work product lies between $I^2/16$ and $713I^2$ | Lean-checked | [Scope](docs/RESULTS.md#minimax-law-and-unbiasedness) · [713](docs/RESULTS.md#the-713-construction) |
| Extensions to unknown gap laws under a stochastic envelope, smooth densities and observed outer states, and lower bounds when magnitudes are revealed | Lean-checked | [Envelope](docs/RESULTS.md#unknown-gap-laws-under-a-stochastic-envelope) · [Densities](docs/RESULTS.md#fixed-finite-order-smooth-densities) · [States](docs/RESULTS.md#finite-cell-observed-state-obstruction) · [Oracles](docs/RESULTS.md#magnitude-oracle-lower-bounds) |

**When positives are rare.** The fraction is known to be at most $\rho$, and
the gap law is known unless a row says otherwise.

| Result | Status | Details |
|---|---|---|
| For every gap law, every rarity $0<\rho\le1/4$ and every budget $B>0$, the risk $R$ satisfies $10^{-17}\mathcal K\le R\le28000\,\mathcal K$, where $\mathcal K$ is an entropy–tail selection functional | Lean-checked | [Scope](docs/RESULTS.md#general-law-rare-event-characterization) |
| A closed formula $Q$ with $\mathcal K\le Q\le\frac{31}{20}\mathcal K$; the least possible factor is the unique root of a scalar equation, which Lean places in $(\sqrt2,\frac{31}{20})$ and an exact-rational check puts at about $1.4626$ | Lean-checked; decimal by rational certificate | [Scope](docs/RESULTS.md#known-finite-gap-rare-events-closed-quantile-characterization) · [Factor](docs/RESULTS.md#sharp-finite-vector-quantile-factor) |
| Critical quadratic law $F(d)=(4d)^2$: the rate is $\min(\rho,\sqrt{\rho L(1+\log L)/B})$ with $L=1+\log(1/\rho)$, which refutes a proposed characterization by a simpler modulus $\Psi$ | Lean-checked | [Scope](docs/RESULTS.md#critical-power-margin-full-minimax-characterization) |
| Power-law gaps: the rates for exponents below and above two | Lean-checked | [Above two](docs/RESULTS.md#rare-event-power-margins-above-two) · [One to two](docs/RESULTS.md#logarithmic-and-intermediate-rare-power-margins) · [Below one](docs/RESULTS.md#rare-event-power-margins-below-exponent-one) |
| $\Psi$ still bounds the risk from below for every gap law, $0<\rho\le1/4$ and $B>0$, with coefficient $10^{-17}$ | Lean-checked | [Scope](docs/RESULTS.md#rare-event-optimizer) |
| $\Psi$ in closed form within a factor $\sqrt2$, and one power-law rate with constants independent of the exponent | Paper proof | [Scope](docs/RESULTS.md#the-variational-modulus-in-closed-form) |
| A stopping program with an exact dual, and certificates within a factor sixteen of the minimax risk | Lean-checked | [Scope](docs/RESULTS.md#general-law-rare-event-characterization) |
| Hard caps on the number of flips; fixed-confidence radius of order $\mathcal K(B/\log(1/\delta))$; a time-uniform rate for a known law and a lower bound of the same order, not composed in Lean | Lean-checked | [Caps](docs/RESULTS.md#hard-observation-caps-for-the-rms-rates) · [Confidence](docs/RESULTS.md#confidence-rates-and-sequential-stopping) |
| Unknown gap law: the same time-uniform rate within a supplied finite family of laws | Lean-checked | [Scope](docs/RESULTS.md#confidence-rates-and-sequential-stopping) |
| Unknown gap law: the same rate for arbitrary laws, after an onset that depends on the law | Paper proof, with [Lean-checked components](docs/ARBITRARY_LAW_FORMALIZATION.md) | [Proof](docs/ARBITRARY_LAW_ADAPTATION.md) |

## Scope and review

<!-- BEGIN status summary: generated by tools/build_status_docs.py from paper/v6/status.json; do not edit by hand -->
The v6 paper tracks 31 results. Lean checks 29 of them; 2 have paper proofs only: eventual oracle-rate adaptation over arbitrary unknown gap laws; the closed form of $\Psi$ with the power-margin rate uniform in the exponent. The [results guide](docs/RESULTS.md#verification-status) lists every result with its status and evidence. Both are generated from the [status source](paper/v6/status.json).
<!-- END status summary -->

What the verification does and does not cover:

- Lean checks the linked statements and the definitions they are stated with.
  Whether those definitions model the paper's experiment is a separate question;
  the [model-fidelity brief](docs/MODEL_FIDELITY.md) sets the two side by side.
- AI agents carried out the research and formalization under David Iach's
  direction. The work has had AI review and no independent external specialist
  review.
- The constants are explicit but conservative. A coefficient such as $10^{-17}$
  proves a rate; it is not a practical guarantee.
- Numerical experiments are supporting evidence, not proofs. The Python
  toolkit is tested and is not formally verified.

Two sets of Lean-checked components are not counted above, because the paper
does not yet describe them as checked: parts of the
[arbitrary-law adaptation proof](docs/ARBITRARY_LAW_FORMALIZATION.md), and
parts of the [finite-law selection approximation](lean/ThresholdHC/SelectionApproximation/README.md).

## Repository map

Current material:

| Path | What it holds | Start with |
|---|---|---|
| [paper/](paper/README.md) | The manuscripts. Version 6 is the current paper; the others are its preserved sources | [paper/README.md](paper/README.md) |
| [lean/](lean/README.md) | The Lean 4 formalization, about 1,190 modules | [lean/README.md](lean/README.md) |
| [docs/](docs/README.md) | Guides: results and scope, verification commands, work plan, and one note for each result | [docs/README.md](docs/README.md) |
| [tools/](tools/README.md) | Audit scripts that check exact statements and axioms, their tests, and the manuscript generators | [tools/README.md](tools/README.md) |
| [results/](results/README.md) | Evidence records of audits and experiments. A record describes one checkpoint and is not edited afterwards | [results/README.md](results/README.md) |
| [research/](research/README.md) | Dated research packages: paper proofs with their checks, kept as written | [research/README.md](research/README.md) |
| [toolkit/](toolkit/README.md) | Python package with budget planners, estimators and rate calculators | [toolkit/README.md](toolkit/README.md) |
| [benchmark/](benchmark/README.md) | The benchmark protocol and its locked experiment code | [benchmark/README.md](benchmark/README.md) |

Historical and locked material, kept unchanged. It explains how the project
started and is not a starting point:

| Path | What it is |
|---|---|
| [BRIEF.md](BRIEF.md) | The original overnight assignment for the AI agents |
| `FROZEN.sha256`, `TIER3_FROZEN.sha256` to `TIER6_FROZEN.sha256`, [FREEZE_LOG.md](FREEZE_LOG.md) | Hash locks on frozen statements and tools, and the log of changes to them |
| [inputs/](inputs/STARTER_README.md) | The imported starting material, preserved byte for byte |
| `constants/` | The constant-scoring harness of the original assignment |
| [proposals/](proposals/README.md) | Proposals to change frozen items |
| [docs/process/](docs/process/README.md) | The process record: method, provenance and run logs |

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
[GitHub Actions](.github/workflows/checks.yml) runs every maintained audit; the two
intermediate entropy-tail audits that [VERIFY.md](docs/VERIFY.md) lists as outside
CI are the exception.
Use a disposable checkout for reproduction: some checks write diagnostic files.

## Open work

The main unfinished item is a Lean proof of adaptation to an arbitrary unknown
gap law, which has a paper proof today. [docs/WORKPLAN.md](docs/WORKPLAN.md)
gives the current priorities, and the
[tracking issue](https://github.com/davidiach/adaptive-threshold-estimation/issues/76)
lists every open task with its dependencies.

## Attribution and license

AI agents carried out the research and formalization under David Iach's
direction. The [process note](docs/process/METHOD.md) and
[provenance record](docs/process/PROVENANCE.md) document the workflow and review limits.

Use [CITATION.cff](CITATION.cff) to cite this work. Code and Lean files are
licensed under [Apache-2.0](LICENSE); the paper and documentation are licensed
under [CC BY 4.0](LICENSE-CC-BY-4.0). See [license scope](LICENSES.md).
