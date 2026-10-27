# A Distributional Minimax Law for Adaptive Threshold Estimation

[Paper (PDF)](paper/paper.pdf) · [Lean 4 / Mathlib proofs](lean/) · [Reproducible numerics](docs/VERIFY.md)

**The problem.** A coin's hidden gap $`D\sim\mu`$ on $`(0,1/2]`$ and sign $`S\in\{0,1\}`$ determine $`P=\tfrac12+(2S-1)D`$. Estimate $`\theta=\Pr(P>1/2)`$ by adaptive flips, allowing revisits and interleaving; cost is expected flips.

**Main results.** Set $`\omega_\mu(h)=\mathbb E_\mu\min\{1,h/D\}`$ for $`h>0`$ and $`I=\mathbb E_\mu[D^{-1}]`$. Write $`R_\mu(B)`$ for minimax RMS error at uniform expected budget $`B\ge1`$.

| Result | Statement | Status | Source |
|---|---|---|---|
| Minimax law | $`R_\mu(B)\asymp\omega_\mu(B^{-1/2})`$; one algorithm independent of $`\mu`$. | paper proof | [Theorem 1](paper/paper.tex#L239) |
| Minimax RMS lower bound | $`R_\mu(B)\ge\omega_\mu(B^{-1/2})/64`$ for every gap law and $`B\ge1`$. | Lean-checked | [minimax_lower_bound](lean/ThresholdHC/Tier6/Full.lean) |
| Uniform unbiasedness | Finite uniform variance and work are attainable iff $`I<\infty`$; their product is $`\ge I^2/16`$. | paper proof | [Theorem 2](paper/paper.tex#L272) |
| Unbiased estimate $`Y`$, flip count $`W`$ | For $`(k_1,k_2)=(1/4,1)`$ and $`I<\infty`$:<br>$`\mathbb E Y=\theta`$, $`\mathrm{Var}(Y)\mathbb E W<713I^2`$. | Lean-checked | [full_bound_713](lean/ThresholdHC/Uniform713/FullBound.lean) |

Uniformity is over all conditional sign laws. The paper has agent-reviewed components, not independent specialist review of v4. Lean checks the linked exact statements. [Verify locally](docs/VERIFY.md) · [CI](https://github.com/davidiach/adaptive-threshold-estimation/actions/workflows/checks.yml)

<details>
<summary>All results: full statements, assumptions, theorem names and sources</summary>

## The problem

A fresh coin has an unobserved magnitude $`D`$ with law $`\mu`$ on $`(0,1/2]`$ and sign $`S\in\{0,1\}`$. A measurable function $`q(d)\in[0,1]`$ gives its positive-sign probability. Its success probability is $`P`$; conditional on $`P`$, flips are independent Bernoulli trials, and fresh coins are independent. An algorithm may create, revisit, and interleave coins, then stop after $`T`$ flips. The target $`\theta`$ is the positive fraction; cost is $`\mathbb E T`$.

$`D\sim\mu`$, $`S\mid D=d\sim\mathrm{Bernoulli}(q(d))`$,<br>
$`P=\tfrac12+(2S-1)D`$, $`\theta=\Pr(P>1/2)=\mathbb E_\mu q(D)`$.

## Main results

Write $`R_\mu(B)`$ for minimax RMS error over all $`q`$ at uniform expected budget $`B\ge1`$, $`\omega_\mu(h)=\mathbb E_\mu\min\{1,h/D\}`$ for $`h>0`$, and $`I=\mathbb E_\mu[D^{-1}]`$. For an estimator $`Y`$ using $`W`$ flips, let $`V=\sup_q\mathrm{Var}_{\mu,q}(Y)`$ and $`\overline W=\sup_q\mathbb E_{\mu,q}W`$.

In the information rows, $`\mathsf P_\pm`$ are transcript laws with sign priors $`1/2\pm\eta(d)`$, $`0\le\eta\le1/8`$, and $`d\eta(d)\le h/8`$; $`\mathrm{kl}`$ is Bernoulli relative entropy and $`0<\delta<1/2`$ bounds both testing errors. For the optimizer, $`0<\rho<1`$ is the allocation budget and $`t`$ solves $`\mathbb E_\mu\min\{1,t^2/D^2\}=\rho`$.

| Result | One-line statement | Status | Where |
|---|---|---|---|
| Minimax law | $`R_\mu(B)\asymp\omega_\mu(B^{-1/2})`$; universal constants, one algorithm independent of $`\mu`$. | paper proof | [Theorem 1; §§2, 5](paper/paper.tex#L239). Component agent review; [review scope](docs/RESULTS.md#paper-review-scope). |
| Minimax RMS lower bound, unrestricted adaptive algorithms | $`R_\mu(B)\ge\omega_\mu(B^{-1/2})/64`$. The infinite experiments are constructed, and the infimum ranges over arbitrary measurable randomized estimators with a uniform expected-work budget. | Lean-checked | `minimax_lower_bound` in [Full.lean](lean/ThresholdHC/Tier6/Full.lean); [algorithm model](lean/ThresholdHC/Tier6/AlgorithmModel.lean), [scope and verification](docs/TIER6.md). |
| Unbiasedness criterion | Unbiased for every $`q`$ with $`V,\overline W<\infty`$ is possible iff $`I<\infty`$. | paper proof | [Theorem 2; §6](paper/paper.tex#L272). Same review scope. |
| Uniform variance–work lower bound | $`V\overline W\ge I^2/16`$ for every unbiased estimator with both uniform bounds finite. | paper proof | [Theorem 2; §6](paper/paper.tex#L774). Same review scope. |
| Unbiased construction, $`(k_1,k_2)=(1/4,1)`$ | $`I<\infty\Rightarrow\mathbb E Y=\theta,`$<br>$`\mathrm{Var}(Y)\mathbb E W<713I^2`$. | Lean-checked | `full_bound_713` in [FullBound.lean](lean/ThresholdHC/Uniform713/FullBound.lean); [assumptions](lean/ThresholdHC/Uniform713/Specification.lean). |
| Full transcript information, finite coin set | $`\mathbb E_+T<\infty\Rightarrow`$<br>$`\mathrm{KL}(\mathsf P_+,\mathsf P_-)\le`$<br>$`(128/225)h^2\mathbb E_+T`$. | Lean-checked | `infinite_kl_bound` in [Full.lean](lean/ThresholdHC/Tier4/Full.lean); [exact joint-law specification](lean/ThresholdHC/Tier4/Model.lean). |
| Full transcript information, unrestricted adaptive coin creation | The same KL/work bound with arbitrary natural-number coin labels, measurable common random environments, revisiting and interleaving. Only plus-law finite expected work is required. | Lean-checked | `creation_infinite_kl_bound` in [Full.lean](lean/ThresholdHC/Tier5/Full.lean); [exact model](lean/ThresholdHC/Tier5/Model.lean), [proof and verification scope](docs/TIER5.md). |
| Randomized, unbounded stopping/testing, finite coin set | $`\mathbb E_+T<\infty\Rightarrow T<\infty`$ a.s. under both laws; $`\mathrm{kl}(1-\delta,\delta)\le`$<br>$`(128/225)h^2\mathbb E_+T`$. | Lean-checked | `unbounded_stopping` in [StoppingBase.lean](lean/ThresholdHC/Tier3/StoppingBase.lean); `unbounded_testing` in [Stopping.lean](lean/ThresholdHC/Tier3/Stopping.lean). |
| Rare-event optimizer, arbitrary laws | $`v_*(d)=\min\{1,t^2/d^2\}`$ maximizes $`\mathbb E_\mu\min\{v(D),h\sqrt{v(D)}/D\}`$ over measurable $`0\le v\le1`$, $`\mathbb E_\mu v(D)\le\rho`$. | Lean-checked | `arbitrary_law_optimizer` in [Optimizer.lean](lean/ThresholdHC/Tier3/Optimizer.lean); [specification](lean/ThresholdHC/Tier3/OptimizerModel.lean). |
| Rare-event power margins above two | For $`F(d)=(d/a)^\alpha`$, $`\alpha>2`$, $`R_{\mu,\rho}(B)\asymp_\alpha\min\{\rho,\sqrt\rho/(a\sqrt B)\}`$. | paper proof | Two agent reviews; [Construction and proof](research/2026-10-27-route-a/construction.tex), [scope and evidence](docs/RESULTS.md#rare-event-power-margins-above-two). Known rarity; constants depend on $`\alpha`$; not Lean-checked or externally specialist-reviewed. |
| Unknown-rarity limitation | No $`\rho`$-independent estimator family has RMS error $`\le C\min\{\rho,\sqrt\rho/(d\sqrt B)\}`$ uniformly over $`B\ge1`$, $`0<\rho\le1/4`$, $`0\le\theta\le\rho`$. | paper proof | [Argument](docs/process/TRACK_D.md#an-obstruction-to-completely-uniform-adaptation-to-unknown-rarity): known $`0<d<1/2`$, a.s. stopping, universal finite $`C`$. [Independently agent-reviewed](proposals/RESEARCH_REVIEW.md#unknown-rarity-adaptation-obstruction). |

Paper proofs in v4 have component agent review, but the consolidated manuscript has no independent specialist review. The Lean rows certify their linked specifications, not the entire paper. Tier 5 removes the fixed finite coin set from the full-transcript information/work theorem, using Mathlib's measure-theoretic KL. The earlier stopping/testing statements keep their original finite-family scope. The 713 theorem covers the untruncated estimator and arbitrary magnitude/sign laws. See [precise scopes](docs/RESULTS.md) and [updates to the unchanged paper](paper/UPDATES.md).

</details>

## What is not claimed

- **713 is not asserted to be optimal.** The lower bound uses uniform bounds over $`q`$, not a pointwise bound for every population; see [paper §6](paper/paper.tex#L774).
- **The proposed arbitrary-law matching-Psi upper bound is refuted at $`\alpha=2`$.** The [full critical note](research/2026-10-27-nonlinear-critical/unrestricted.tex) proves $`R_{\mu,\rho}(B)\asymp\min\{\rho,\sqrt{\rho L(1+\log L)/B}\}`$, $`L=1+\log(1/\rho)`$, at $`F(d)=(4d)^2`$, for all observable fresh-coin algorithms with uniform expected work at most B, including interaction and nonlinear output. This is an agent-reviewed paper proof, not a Lean or external specialist verification. The [scope and evidence](research/2026-10-27-nonlinear-critical/CHECKPOINT.md) distinguish this from the preserved variational optimizer. A sharp replacement for arbitrary laws remains open; the earlier [power-margin note](research/2026-10-27-route-a/construction.tex) resolves $`\alpha>2`$.
- **Finite-grid proxies are not universal constants.** Truncated floating-point recursions give numerical evidence; the grid winner fails the original uniform bias bound off-grid. See the [counterexample](proposals/constants/BIAS_AUDIT.md) and [scores](results/constants_finite_grid.json).
- **Numerical comparisons do not establish practical superiority or universal theorems.** See [benchmark limitations](docs/process/TRACK_C.md). Expected-work guarantees provide neither a deterministic work cap nor a data-observable confidence radius for every unknown law ([paper §10](paper/paper.tex#L1280)).

## Verify it yourself

Use Python 3.12 and the [pinned Lean toolchain](lean/lean-toolchain). From the repository root:

```sh
python -m pip install -r requirements.txt
cd lean
lake exe cache get
cd ..
python tools/verify_lean_checkpoint.py --sequential
python tools/verify_uniform713.py --sequential --require-complete
python tools/verify_tier3.py --sequential --require-complete
python tools/verify_tier4.py --sequential --require-complete
python tools/verify_tier5.py --sequential --require-complete
python tools/verify_tier6.py --sequential --require-complete
python tools/check_targets_numeric.py
python tools/check_targets2_numeric.py
python -m unittest discover -s tools -p 'test_*.py' -v
```

The [full verification list](docs/VERIFY.md) includes hashes, experiment locks, arithmetic, constant scores, and benchmark checks. Several commands write diagnostics under `results/`; use a disposable checkout to preserve published records. [GitHub Actions](https://github.com/davidiach/adaptive-threshold-estimation/actions/workflows/checks.yml) runs the numerical and Lean audits.

## Repository layout

The [research index](research/README.md) connects the rare-event, population and
nonlinear-feedback packages and distinguishes their historical checkpoints from
the current results. Their paper proofs and numerical experiments retain their
stated evidence levels.

| Path | Contents |
|---|---|
| [paper/](paper/) | Unchanged v4 PDF and TeX, and subsequent results. |
| [lean/](lean/) | Statements, proofs, and pinned Mathlib dependencies. |
| [docs/RESULTS.md](docs/RESULTS.md), [docs/VERIFY.md](docs/VERIFY.md) | Claim scopes, source pointers, and verification commands. |
| [constants/](constants/), [benchmark/](benchmark/) | Numerical evaluators and benchmark code. |
| [results/](results/), [inputs/](inputs/) | Recorded evidence and preserved inputs. |
| [proposals/](proposals/), [docs/process/](docs/process/) | Supporting arguments, reviews, and research history. |

## How this was made

The [process note](docs/process/METHOD.md) explains how the experiment was
specified, proofs and claims were checked, failed approaches were retained,
and the limits of agent review were recorded. The current follow-up is tracked
in the [verification and consolidation ledger](docs/WORKPLAN.md).

AI agents carried out the research and formalization under David Iach's direction, against frozen Lean targets checked by a hash-locked scorer. The [provenance record](docs/process/PROVENANCE.md), [research report](docs/process/REPORT.md), and [run log](docs/process/RUNLOG.md) document the work and its evidence. Tiers, point totals, and checkpoints record that process; they do not extend the verified statements. The [process index](docs/process/README.md) links the original brief, approval history, and independent agent reviews.

Code and Lean files use [Apache-2.0](LICENSE); the paper and documentation use [CC BY 4.0](LICENSE-CC-BY-4.0). See [license scope](LICENSES.md) and [CITATION.cff](CITATION.cff) for attribution and the AI-assisted provenance note.
