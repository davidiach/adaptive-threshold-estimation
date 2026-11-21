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
\frac{1}{6}\,\omega_\mu(B^{-1/2})
\;\le\; R_\mu(B)
\;\le\; 12\,\omega_\mu(B^{-1/2}).
```

Both bounds are proved in Lean for the observable adaptive experiment.
The lower constant $1/6$ is sharp: no larger constant holds for every gap
law and budget. The upper constant $12$ is not optimized: a
[numerical study](research/2026-11-19-upper-constant-12/README.md) puts the
actual worst ratio of the algorithm behind it near $5.4$. One upper algorithm works
for every gap law without knowing $\mu$. The v6 paper states $12$ and
proves it in Appendix AB; the frozen upper target states $512$. The
[lower theorem](lean/ThresholdHC/SharpRMS/Full.lean),
[upper theorem](lean/ThresholdHC/UpperScale/Full.lean), and
[model and scope](docs/RESULTS.md#minimax-law-and-unbiasedness) give the
precise statements. The original lower theorem, with the constant $1/64$,
is kept as a [frozen target](lean/ThresholdHC/Tier6/Full.lean).

## Results at a glance

Each row is a summary. [docs/RESULTS.md](docs/RESULTS.md) states the exact
assumptions, constants and Lean theorem behind it.

**For every sign law.** The worst case is over every way the sign can depend
on the gap, at a fixed gap law $\mu$.

| Result | Status | Details |
|---|---|---|
| For $B\ge1$, the sharp universal minimax RMS lower bound is $\omega_\mu(B^{-1/2})/6$ in the ordinary model and both magnitude oracles. Four fresh flips attain equality at $B=4$ and $\mu=\delta_{1/2}$. | Lean-checked | [Scope](docs/RESULTS.md#minimax-law-and-unbiasedness) · written proof in Appendix AA of the [paper](paper/v6/README.md) |
| For $B\ge25$ the best universal lower constant lies between $0.175198$ and $0.186752$; its exact value is open. | Lean-checked | [Scope](docs/RESULTS.md#minimax-law-and-unbiasedness) · outline in Appendix AA of the [paper](paper/v6/README.md) |
| One algorithm that knows only the budget attains RMS error at most $12\,\omega_\mu(B^{-1/2})$ ($512$ in the frozen target). | Lean-checked | [Scope](docs/RESULTS.md#minimax-law-and-unbiasedness) · written proof in Appendix AB of the [paper](paper/v6/README.md) |
| Confidence radius of order $\omega_\mu\bigl(\sqrt{\log(1/\delta)/B}\bigr)$ | Lean-checked | [Scope](docs/RESULTS.md#minimax-law-and-unbiasedness) |
| An unbiased estimator with finite variance and expected work exists exactly when $I=\mathbb E_\mu[D^{-1}]$ is finite; the best variance–work product lies between $I^2/16$ and $713I^2$ | Lean-checked | [Scope](docs/RESULTS.md#minimax-law-and-unbiasedness) · [713](docs/RESULTS.md#the-713-construction) |
| Extensions to unknown gap laws under a stochastic envelope, smooth densities and observed outer states, and lower bounds when magnitudes are revealed | Lean-checked | [Envelope](docs/RESULTS.md#unknown-gap-laws-under-a-stochastic-envelope) · [Densities](docs/RESULTS.md#fixed-finite-order-smooth-densities) · [States](docs/RESULTS.md#finite-cell-observed-state-obstruction) · [Oracles](docs/RESULTS.md#magnitude-oracle-lower-bounds) |

**When positives are rare.** The fraction is known to be at most $\rho$, and
the gap law is known unless a row says otherwise.

| Result | Status | Details |
|---|---|---|
| For every gap law, every rarity $0<\rho\le1/4$ and every budget $B>0$, the risk $R$ satisfies $10^{-17}\mathcal K\le R\le28000\,\mathcal K$, where $\mathcal K$ is an entropy–tail selection functional | Lean-checked | [Scope](docs/RESULTS.md#general-law-rare-event-characterization) |
| A closed formula $Q$ with $\mathcal K\le Q\le\frac{31}{20}\mathcal K$; the least possible factor is the unique root of a scalar equation, which Lean places in $(\sqrt2,\frac{31}{20})$ and an exact-rational check puts at about $1.4626$ | Lean-checked; lower decimal end Lean-checked, upper by rational certificate | [Scope](docs/RESULTS.md#known-finite-gap-rare-events-closed-quantile-characterization) · [Factor](docs/RESULTS.md#sharp-finite-vector-quantile-factor) |
| Critical quadratic law $F(d)=(4d)^2$: the rate is $\min(\rho,\sqrt{\rho L(1+\log L)/B})$ with $L=1+\log(1/\rho)$, which refutes a proposed characterization by a simpler modulus $\Psi$ | Lean-checked | [Scope](docs/RESULTS.md#critical-power-margin-full-minimax-characterization) |
| Power-law gaps: the rates for exponents below and above two | Lean-checked | [Above two](docs/RESULTS.md#rare-event-power-margins-above-two) · [One to two](docs/RESULTS.md#logarithmic-and-intermediate-rare-power-margins) · [Below one](docs/RESULTS.md#rare-event-power-margins-below-exponent-one) |
| $\Psi$ still bounds the risk from below for every gap law, $0<\rho\le1/4$ and $B>0$, with coefficient $10^{-17}$ | Lean-checked | [Scope](docs/RESULTS.md#rare-event-optimizer) |
| $\Psi$ in closed form within a factor $\sqrt2$, and one power-law rate with constants independent of the exponent | Lean-checked | [Scope](docs/RESULTS.md#the-variational-modulus-in-closed-form) |
| A stopping program with an exact dual, and certificates within a factor sixteen of the minimax risk | Lean-checked | [Scope](docs/RESULTS.md#general-law-rare-event-characterization) |
| Hard caps on the number of flips; fixed-confidence radius of order $\mathcal K(B/\log(1/\delta))$; a time-uniform rate for a known law and a lower bound of the same order, not composed in Lean | Lean-checked | [Caps](docs/RESULTS.md#hard-observation-caps-for-the-rms-rates) · [Confidence](docs/RESULTS.md#confidence-rates-and-sequential-stopping) |
| Unknown gap law: the same time-uniform rate within a supplied finite family of laws | Lean-checked | [Scope](docs/RESULTS.md#confidence-rates-and-sequential-stopping) |
| Unknown gap law: the same rate for arbitrary laws, after an onset that depends on the law | Lean-checked | [Theorem and construction](docs/ARBITRARY_LAW_FORMALIZATION.md#full-arbitrary-law-all-budget-controller) · [Publication evidence](results/adaptation-publication-20261116/README.md) |

## Scope and review

<!-- BEGIN status summary: generated by tools/build_status_docs.py from paper/v6/status.json; do not edit by hand -->
The v6 paper tracks 33 results. Lean checks 32 of them; 1 has a paper proof only: the critical-window simplification and its asymptotic interpretation. The [results guide](docs/RESULTS.md#verification-status) lists every result with its status and evidence. Both are generated from the [status source](paper/v6/status.json).
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

Lean also checks the
[finite-law selection approximation](docs/FINITE_SELECTION_APPROXIMATION.md).
It is not counted above, because the paper does not describe it.

The opt-in [numerical certificate path](docs/DETERMINISTIC_VERIFICATION.md)
lets the Lean kernel check individual outputs of the toolkit. It covers
finite-law objectives and oracles,
[zero-residual envelopes, rounding and conditional transfer](docs/ENVELOPE_TRANSFER_CERTIFICATES.md),
and [bounded global-selection outputs](docs/GLOBAL_SELECTION_CERTIFICATES.md).
Solver transcripts, other selection entry points and concrete planners
remain open in
[#85](https://github.com/davidiach/adaptive-threshold-estimation/issues/85);
stochastic execution is
[#86](https://github.com/davidiach/adaptive-threshold-estimation/issues/86).

## Repository map

Current material:

| Path | What it holds | Start with |
|---|---|---|
| [paper/](paper/README.md) | The manuscripts. Version 6 is the current paper; the others are its preserved sources | [paper/README.md](paper/README.md) |
| [lean/](lean/README.md) | The Lean 4 formalization, about 1,350 modules | [lean/README.md](lean/README.md) |
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

Project files at the top level:

| Path | What it is |
|---|---|
| [CONTRIBUTING.md](CONTRIBUTING.md), [AGENTS.md](AGENTS.md) | Setup, where to edit and how to check a change; the second is the working guide for AI agents |
| [CITATION.cff](CITATION.cff), [LICENSE](LICENSE), [LICENSE-CC-BY-4.0](LICENSE-CC-BY-4.0), [LICENSES.md](LICENSES.md) | How to cite the work, the two licenses and which files each covers |
| `requirements.txt` | Pinned Python packages for the tools and the numerical checks |
| `.github/` | The CI workflows, such as [checks.yml](.github/workflows/checks.yml), and [lean_ci.py](.github/lean_ci.py), which selects the Lean audits a change needs |
| `.gitattributes`, `.gitignore` | Byte-exact storage of tracked files, which the hash locks rely on, and ignored build output |

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
python tools/verify_sharp_rms.py
python tools/verify_upper_scale.py
python tools/verify_blind_upper_components.py --sequential
python tools/verify_tier6.py --sequential --require-complete
```

The first command checks the sharp lower bound with the constant $1/6$,
the second the upper bound with $12$, the third the frozen upper target
with $512$, and the fourth the original frozen lower target with $1/64$. Each one builds what it needs, restates the
target types exactly and reports the axioms the proofs use.

The [verification guide](docs/VERIFY.md) covers the other theorems, exact target
types, transitive-axiom audits, source hashes, and numerical checks.
[GitHub Actions](.github/workflows/checks.yml) runs the research and numerical
checks on pull requests and pushes to `main`. It selects Lean audits from the
files changed by the entire PR or push. Changes to project proofs or the pinned
toolchain run all four Lean jobs. On pull requests these jobs reuse compiled
modules from earlier runs and rebuild only what changed; pushes to `main`
build from scratch. To run the full CI audit suite on any branch, with a
build from scratch, start **Reproducible checks** manually from the Actions tab.
[VERIFY.md](docs/VERIFY.md) also lists two intermediate entropy-tail audits
available for local reproduction.
Use a disposable checkout for reproduction: some checks write diagnostic files.

## Open work

- **Paper proof only, now Lean-checked.** The one tracked result with a
  paper proof only, the critical-window simplification that closes
  [v6 §14.8](docs/RESULTS.md#the-variational-modulus-in-closed-form) with its
  asymptotic interpretation, is Lean-checked since 20 November 2026
  ([record](results/critical-window-20261120/README.md)). The v6 status table
  still lists it as a paper proof until the next manuscript update.
- **Smaller paper and guide claims.** Twelve claims that the paper or the
  guides stated with only a written proof, a numerical check or an existential
  constant are Lean-checked since 20 November 2026, among them the critical
  theorem with explicit constants, the sharpness of the unbiased coefficient
  $1/16$ and the lower end of the bracket for the sharp quantile factor
  ([record](results/paper-statements-20261120/README.md)). Two of the four
  pilot-feedback separations, Lean-proved inside their research packages, are
  in the audited library too
  ([record](results/pilot-feedback-20261120/README.md)); the other two need
  their integer certificates split before CI can check them.
  Since 21 November 2026 Lean also checks the impossibility half of
  Proposition `prop:bounded`, states the explicit constants $15/(256\sqrt2)$,
  $1/256$ and $28\rho$ as exact targets, and checks both corollaries of the
  finite-gap manuscript, the stopped time-uniform remark, the threshold form
  of the target for every law, the zero-atom split, the explicit fixed-cap
  estimate, the bias-subtraction remark of Appendix H and the common-pair RMS
  bound at the critical law ([records](results/README.md)).
- **Constants of the main law.** The lower constant $1/6$ is sharp and the
  upper constant is $12$, so the two sides are a factor $72$ apart. For
  budgets of at least 25 the best lower constant is known only to lie in
  $[0.175198,\,0.186752]$.
- **Toolkit verification.** The Python toolkit is tested and not formally
  verified; #85 and #86 track the connection to the Lean statements.

[docs/WORKPLAN.md](docs/WORKPLAN.md) gives the current priorities, and the
[tracking issue](https://github.com/davidiach/adaptive-threshold-estimation/issues/76)
lists every open task with its dependencies.

## Attribution and license

AI agents carried out the research and formalization under David Iach's
direction. The [process note](docs/process/METHOD.md) and
[provenance record](docs/process/PROVENANCE.md) document the workflow and review limits.

Use [CITATION.cff](CITATION.cff) to cite this work. Code and Lean files are
licensed under [Apache-2.0](LICENSE); the paper and documentation are licensed
under [CC BY 4.0](LICENSE-CC-BY-4.0). See [license scope](LICENSES.md).
