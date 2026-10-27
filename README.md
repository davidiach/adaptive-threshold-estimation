# A Distributional Minimax Law for Adaptive Threshold Estimation

[Paper (PDF)](paper/paper.pdf), Lean 4 formalization with Mathlib, and reproducible numerics for estimating the fraction of noisy coins above a threshold.

## The problem

A fresh coin has an unobserved magnitude $D$ with law $\mu$ on $(0,1/2]$ and sign $S\in\{0,1\}$. A measurable function $q(d)\in[0,1]$ gives its positive-sign probability. Its success probability is $P$; conditional on $P$, flips are independent Bernoulli trials, and fresh coins are independent. An algorithm may create, revisit, and interleave coins, then stop after $T$ flips. The target $\theta$ is the positive fraction; cost is $\mathbb E T$.

$$D\sim\mu,\quad S\mid D=d\sim\operatorname{Bernoulli}(q(d)),\quad P=\tfrac12+(2S-1)D,\quad \theta=\Pr(P>1/2)=\mathbb E_\mu q(D).$$

## Main results

Write $R_\mu(B)$ for minimax RMS error over all $q$ at uniform expected budget $B\ge1$, $\omega_\mu(h)=\mathbb E_\mu\min\{1,h/D\}$ for $h>0$, and $I=\mathbb E_\mu[D^{-1}]$. For an estimator $Y$ using $W$ flips, let $V=\sup_q\operatorname{Var}_{\mu,q}(Y)$ and $\overline W=\sup_q\mathbb E_{\mu,q}W$.

In the information rows, $\mathsf P_\pm$ are transcript laws with sign priors $1/2\pm\eta(d)$, $0\le\eta\le1/8$, and $d\eta(d)\le h/8$; $\operatorname{kl}$ is Bernoulli relative entropy and $0<\delta<1/2$ bounds both testing errors. For the optimizer, $0<\rho<1$ is the allocation budget and $t$ solves $\mathbb E_\mu\min\{1,t^2/D^2\}=\rho$.

| Result | One-line statement | Status | Where |
|---|---|---|---|
| Minimax law | $R_\mu(B)\asymp\omega_\mu(B^{-1/2})$; universal constants, one algorithm independent of $\mu$. | paper proof | [Theorem 1; §§2, 5](paper/paper.tex#L239). Component agent review; consolidated v4 not independently specialist-reviewed ([record](docs/RESULTS.md#paper-review-scope)). |
| Unbiasedness criterion | Unbiased for every $q$ with $V,\overline W<\infty$ is possible iff $I<\infty$. | paper proof | [Theorem 2; §6](paper/paper.tex#L272). Same component-review scope as above. |
| Uniform variance–work lower bound | $V\overline W\ge I^2/16$ for every unbiased estimator with both uniform bounds finite. | paper proof | [Theorem 2; §6](paper/paper.tex#L774). Same component-review scope as above. |
| Unbiased construction, $(k_1,k_2)=(1/4,1)$ | $I<\infty\Rightarrow\mathbb E Y=\theta,\quad\operatorname{Var}(Y)\mathbb E W<713I^2$. | Lean-checked | `ThresholdHC.Uniform713.full_bound_713` in [FullBound.lean](lean/ThresholdHC/Uniform713/FullBound.lean); [assumptions](lean/ThresholdHC/Uniform713/Specification.lean). |
| Full transcript information, finite coin set | $\mathbb E_+T<\infty\Rightarrow\operatorname{KL}(\mathsf P_+,\mathsf P_-)\le(128/225)h^2\mathbb E_+T$. | Lean-checked | `ThresholdHC.Tier4.infinite_kl_bound` in [Full.lean](lean/ThresholdHC/Tier4/Full.lean); [exact joint-law specification](lean/ThresholdHC/Tier4/Model.lean). |
| Randomized, unbounded stopping/testing, finite coin set | $\mathbb E_+T<\infty\Rightarrow T<\infty$ a.s. under both laws; $\operatorname{kl}(1-\delta,\delta)\le(128/225)h^2\mathbb E_+T$. | Lean-checked | `ThresholdHC.Tier3.unbounded_stopping` in [StoppingBase.lean](lean/ThresholdHC/Tier3/StoppingBase.lean); `ThresholdHC.Tier3.unbounded_testing` in [Stopping.lean](lean/ThresholdHC/Tier3/Stopping.lean). |
| Rare-event optimizer, arbitrary laws | $v_*(d)=\min\{1,t^2/d^2\}$ maximizes $\mathbb E_\mu\min\{v(D),h\sqrt{v(D)}/D\}$ over measurable $0\le v\le1$, $\mathbb E_\mu v(D)\le\rho$. | Lean-checked | `ThresholdHC.Tier3.arbitrary_law_optimizer` in [Optimizer.lean](lean/ThresholdHC/Tier3/Optimizer.lean); [specification](lean/ThresholdHC/Tier3/OptimizerModel.lean). |
| Unknown-rarity limitation | No $\rho$-independent estimator family has RMS error $\le C\min\{\rho,\sqrt\rho/(d\sqrt B)\}$ uniformly over $B\ge1$, $0<\rho\le1/4$, $0\le\theta\le\rho$. | paper proof | [Argument](docs/process/TRACK_D.md#an-obstruction-to-completely-uniform-adaptation-to-unknown-rarity): known $0<d<1/2$, a.s. stopping, universal finite $C$. [Independently agent-reviewed](proposals/RESEARCH_REVIEW.md#unknown-rarity-adaptation-obstruction). |

The Lean rows certify their linked specifications, not the entire paper. The stopping and transcript bounds allow arbitrary measurable random seeds and unbounded horizons, but retain a fixed finite set of coins; the full-transcript bound uses Mathlib's measure-theoretic KL. The 713 theorem covers the untruncated estimator and arbitrary magnitude/sign laws. See [precise scopes](docs/RESULTS.md) and [updates to the unchanged paper](paper/UPDATES.md).

## What is not claimed

- **713 is not asserted to be optimal.** The lower bound uses uniform bounds over $q$, not a pointwise bound for every population; see [paper §6](paper/paper.tex#L774).
- **Matching rare-event upper bounds for arbitrary laws or power margins with $\alpha\ge2$ remain open here.** This concerns the rarity-constrained class, not the unrestricted minimax law; see [continuation §4 and its conjecture](inputs/next-phase/report/research_note.tex#L246).
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
python tools/check_targets_numeric.py
python tools/check_targets2_numeric.py
python -m unittest discover -s tools -p 'test_*.py' -v
```

The [full verification list](docs/VERIFY.md) includes hashes, experiment locks, arithmetic, constant scores, and benchmark checks. Several commands write diagnostics under `results/`; use a disposable checkout to preserve published records. [GitHub Actions](https://github.com/davidiach/adaptive-threshold-estimation/actions/workflows/checks.yml) runs the numerical and Lean audits.

## Repository layout

| Path | Contents |
|---|---|
| [paper/](paper/) | Unchanged v4 PDF and TeX, and subsequent results. |
| [lean/](lean/) | Statements, proofs, and pinned Mathlib dependencies. |
| [docs/RESULTS.md](docs/RESULTS.md), [docs/VERIFY.md](docs/VERIFY.md) | Claim scopes, source pointers, and verification commands. |
| [constants/](constants/), [benchmark/](benchmark/) | Numerical evaluators and benchmark code. |
| [results/](results/), [inputs/](inputs/) | Recorded evidence and preserved inputs. |
| [proposals/](proposals/), [docs/process/](docs/process/) | Supporting arguments, reviews, and research history. |

## How this was made

AI agents carried out the research and formalization under David Iach's direction, against frozen Lean targets checked by a hash-locked scorer. The [provenance record](docs/process/PROVENANCE.md), [research report](docs/process/REPORT.md), and [run log](docs/process/RUNLOG.md) document the work and its evidence. Tiers, point totals, and checkpoints record that process; they do not extend the verified statements. The [process index](docs/process/README.md) links the original brief, approval history, and independent agent reviews.

Code and Lean files use [Apache-2.0](LICENSE); the paper and documentation use [CC BY 4.0](LICENSE-CC-BY-4.0). See [license scope](LICENSES.md) and [CITATION.cff](CITATION.cff) for attribution and the AI-assisted provenance note.
