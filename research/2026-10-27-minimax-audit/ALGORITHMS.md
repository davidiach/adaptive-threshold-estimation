# Algorithms, observation contracts, and reproduction

## Proved construction (paper proof)

`theorem/critical.tex` and `theorem/critical.py` specify a capped asymmetric classifier. At level j use epsilon=16^(-j-1), cap ceil(1/(a² rho epsilon)), and finitely many geometric reference gaps. Multiply correct and wrong reference factors from observed samples; reject negative at threshold (K+1)/epsilon and accept positive at (K+1)/(rho epsilon). If neither fires, classify by the mean at the cap. No latent magnitude or q is read.

Draw level J with probability 2^(-J-1). At J=0 return the base decision divided by its level probability. Otherwise run adjacent classifiers on successive blocks of the **same coin**, take their difference and divide by the level probability. Fresh calls use fresh coins. The conditional-iid suffix justification, bias, second moment, mean work and termination are proved in the note. Independent Poisson replication gives the expected budget exactly as an upper bound, without replacing a product of separate suprema by a supremum of products. Median replication provides the stated confidence radius. A constant rho/2 is chosen when its proved bound is smaller.

The direct bounded-observation version uses product factors 1±2r(2X-1) and the same caps. It applies to X in [0,1], not the unbounded GHA observations. No Bernoulli conversion is required. `critical.py` contains floating implementations, explicitly not exact real-arithmetic certificates. Its bounded finite tests use Fraction arithmetic; it is not a tested production implementation of the full unbounded-level random estimator.

For arbitrary mu, the finite capped bracket uses exact or certified beta_j=E exp(-2N_jD²), truncated work integrals and a global-rarity upper-tail integral, then independent Poisson allocations proportional to sqrt(v_j/C_j). A known abstract law may determine finitely many real constants. This is not an algorithm to compute integrals from every representation of a measure, and gives no observed gap oracle. No comparison of this bracket with Psi is proved.

The unknown-rarity fixed-gap construction and computable conservative CI are in `adaptation.tex`. They use an exactly known gap; the CI needs certified arithmetic for its binomial false-positive probability. Its sufficient logarithmic loss and additive floor are not claimed sharp.

## New practical candidate (NUMERICAL)

The experiment is **not** a performance implementation of the critical theorem. `experiments.py` compares:

1. GHA Algorithm 1 inner-sampling rule, N0=32, C=3, r=1.5, in a single-base-level driver.
2. A two-level direct-real randomized sum, coarse cap B/16, fine cap B/4, minimum early check 16, threshold multiplier 1, inclusion probability 4^(-3/4)/(1+4^(-3/4)).
3. The same sum with positive threshold multiplied by sqrt(1+log(1/rho)); negative threshold unchanged. This candidate was fixed before testing and is now rejected as a general improvement.

The GHA comparator here is explicitly **altered allocation, single level**, not the published full adaptive tolerance MLMC driver. Original tuned-GHA historical comparisons are independently reproduced with the original code in `replay_benchmark.py`; they still favor GHA. The new experiment cannot establish superiority to that stronger comparator.

For each term (Y,C), 0<C<=M=B/4. Use independent pilot terms until two cost-marker successes U<C/M, discard their values, then average K-1 fresh production terms. With c=EC, Wald and the inverse-binomial identity give total expected work 4M-c and raw variance Var(Y)c/M. Value and cost within a term may depend on each other; production is independent of the pilot stopping count. This is inherited calibration, not a novel method. Work is random, not capped. There is no confidence procedure for these heuristic estimates.

Each inner real observation is charged one; no Bernoulli conversion is made. Fresh outer draws are uncharged in the inherited primary convention, separately counted, and alternative total-work means charging one per outer draw are in the result file. Every pilot/production call counts. Arithmetic and auxiliary randomness are uncharged. No offline moments are fitted, and no candidate grid was searched in this run. Historical training/tuning expense is preserved below.

## Simulators and truth

| Simulator | Observable channel | Analytic truth; supplied rarity bound |
|---|---|---|
| Published GHA | X=.02(Y²-U²)+2 sqrt(.02*.98) Y Z-loss, independent standard normals | loss=.02[(Phi^-1(1-theta/2))²-1]; theta=.025, rho=.1 |
| Rarer GHA variant (synthetic) | Same channel, changed loss | theta=.005, rho=.02 |
| Fixed gap (synthetic) | Bernoulli(.5±.2), centered by .5 | positive probability .01, rho=.04 |
| Mixed scales (synthetic) | 4% mass at d=.01, half positive there; remainder d=.25 negative | theta=.02, rho=.04 |
| Near-negative population (synthetic) | 95% mass negative d=.005; remainder positive d=.25 | theta=.05, rho=.1 |
| Independently specified Gaussian simulator (synthetic) | Hidden M uniform[-.95,.05]; X=M+N(0,1) | theta=.05, rho=.1 |
| Deterministic endpoint (synthetic) | Bernoulli probabilities zero and one | theta=.02, rho=.04 |

Only the simulator uses its hidden state. The decision procedures use observations, identity and supplied rho. The Gaussian and GHA sample-variance rules are heuristics; no bounded-observation theorem is imported. Truth has no simulation uncertainty except floating evaluation of the specified normal quantile; it is an exact analytic target mathematically. No independent high-accuracy MC truth estimate was substituted.

## Fixed evaluation and accounting

`PREREGISTRATION.json` pins source hash, budgets 4,096 and 16,384, seven models, 128 repetitions, all seeds, epsilon=max(.0025,theta/2), metrics and no exclusions. `TEST_STARTED.json` links the one permitted final run to that lock. No later candidate was tested on these data. Values and unchanged work counts are retained in `BENCHMARK_RAW.npz`; JSON and CSV report raw/clipped RMS, bias, empirical variance, miss probability, clipping fraction, work quantiles, wall times and outer counts. Coverage is null because no confidence procedure is supplied.

Bootstrap percentile intervals (2,000 resamples per cell) are descriptive, not coverage certificates. Random calibration work has an unbounded tail; 128 runs do not characterize extreme quantiles reliably. Raw values are bounded for this finite two-level implementation, but rare events still make RMS intervals unstable. Point-estimate ordering at nominal budgets is not a matched-accuracy speedup.

Zero/half/rho-half baselines have no work. All truths are nonzero; rho/2 coincides with truth in some synthetic cells. Such a coincidence is reported, not presented as a uniformly useful estimator. No one-shot or amortized advantage is established. New fitting/tuning expense is zero; finite verification and historical replay are recorded separately rather than hidden. Historical direct-real development cost was 1,541,656,608 inner draws; historical GHA training and tuning cost was 200,921,568. There is no demonstrated equal-accuracy production saving, so no finite break-even workload is justified.

## Reproduction

Use the pinned Python dependencies in the main repository requirements. From the repository root:

```powershell
python research/2026-10-27-minimax-audit/replay_benchmark.py
python research/2026-10-27-minimax-audit/test_experiments.py
python research/2026-10-27-minimax-audit/check_exact.py
python research/2026-10-27-minimax-audit/theorem/critical.py
python research/2026-10-27-minimax-audit/formal/check_stopping_counterexample.py
```

To independently reproduce final data, copy the research source into a fresh repository copy while keeping its relative location, omit output files, run `experiments.py lock` and `experiments.py test` there. Keep identical source, parameters and seeds to reproduce; label this a replay. Do not delete this checkpoint's lock or test marker. Training and tuning commands do not exist in this harness.

`summarize.py` needs ReportLab, available in the bundled desktop Python; it regenerates the CSV and vector figure from existing samples, without resampling production. Compile `RESEARCH_NOTE.tex` with a TeX engine using this directory as its input root. Current local build, renderer and acceptance details are in the run log. New proof specifications are locked separately under `formal/` and never regenerate historical locks.
