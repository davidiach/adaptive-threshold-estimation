# Adaptive threshold estimation — next-phase research package

**Baseline:** v4, preserved unchanged. **Date:** 26 October 2026.
This is a continuation, not a rewritten v4 manuscript.

## Evidence labels

**Proved in the accompanying note:**
- A counterexample to rho * omega_mu((rho B)^(-1/2)) under the global constraint integral q dmu <= rho.
- A restricted-region lower bound; an arbitrary-law variational lower bound using the explicitly cited Lee–Valiant Corollary 19.
- The exact optimizer of the variational functional Psi.
- Matching RMS and high-confidence rates for power margins 0 < alpha < 2, with an implementable shifted-start multilevel construction.
- A nonmatching general upper bracket and a model-specific sign-preserving Bernoulli conversion for the benchmark.

These are mathematical proof claims, not machine-checked formal proofs or independent referee endorsements. The full arbitrary-law upper characterization is NOT proved.

**Conjecture:** a matching arbitrary-law upper rate Psi. The alpha >= 2 matching upper regimes and a distribution-blind rare-event upper theorem are not established here.

**Numerical evidence:** held-out benchmark, finite-tape implementation comparisons, quadrature checks, finite optimization diagnostics. These do not prove universal inequalities or asymptotic rates.

**Prior art:** `PRIOR_ART_AUDIT.md` distinguishes full statement/proof inspection from abstract-only leads and failed access. No novelty or priority claim.

## Contents

- `report/research_note.pdf` and `.tex`: complete research continuation and proofs.
- `PRIOR_ART_AUDIT.md`: source-by-source audit, inspection depth, overlaps, gaps.
- `code/rare_event.py`: reference shifted-start power-margin estimator and atomic Psi evaluator.
- `code/verify_phase2.py`: diagnostic tests; output `results/theory_diagnostics.json`.
- `code/benchmark.py`: model, GHA adaptive sampling/coupling, v4 reference, tuned variants, original training/tuning/test stages.
- `code/benchmark_extension.py`: larger-budget test that exercises nontrivial multilevel corrections.
- `code/summarize_results.py`: descriptive bootstrap intervals, CSV and LaTeX table.
- `code/plot_results.py`: reproducible comparison plot.
- `results/`: all summarized and raw held-out outcomes, training allocation moments, tuning results, configurations and seeds.
- `baseline/Adaptive_Threshold_v4/`: unchanged v4 source, implementation, and PDF.
- `baseline_original/`: exact original v4 PDF and ZIP; their SHA-256 hashes are recorded.
- `BASELINE_INTEGRITY.json`: hashes and preservation record.
- `MANIFEST_SHA256.txt`: package-file hashes (excluding itself).

## Key theoretical rates

For F(t)=(t/a)^alpha, 0<alpha<2, global theta<=rho, define x=1/(a sqrt(B)). The proved RMS scales, up to constants depending only on alpha, are:

- alpha<1: min(rho, x^alpha).
- alpha=1: min(rho, x [1+log_+(rho/x)]).
- 1<alpha<2: min(rho, rho^(1-1/alpha) x).

For confidence delta replace x by sqrt(log(1/delta)/B)/a. The power upper algorithm needs alpha, a, rho. It does not infer or certify these assumptions. All work bounds are in expectation, not per-run caps. Outputs are projected onto [0,rho] only when rho is supplied to this theoretical algorithm.

The arbitrary-law optimizer is w(d)=min(1,t^2/d^2), where E[min(1,t^2/D^2)]=rho. The optimizer identity and lower bound are proved; general upper optimality remains a conjecture.

## Benchmark protocol and limitations

The original real-valued Giles–Haji-Ali equation (3.2) model uses tau=0.02 and theta=0.025. Their adaptive-count algorithm, fresh pilots and antithetic coupling are implemented. This is NOT a reproduction of their complete adaptive-tolerance software driver. Allocation is learned offline for a budget-indexed experiment.

The v4 theorem only covers Bernoulli observations. To keep a proved reference, each real observation X is transformed to 1{X+tau(V^2-1)>0}, with a fresh independent standard normal V. Symmetry proves preservation of the target. The conversion discards information, unlike the comparator's real-valued access. It is specific to this model, not a general reduction for unbounded inner observations.

Work counts all original inner draws, including pilots. Auxiliary normals, arithmetic, and wall-clock time are not counted. v4's two-success wrapper has an exact expected-work bound; fitted GHA allocations do not have a new uniform budget guarantee. Always compare against measured mean work and its variability.

All final benchmark outputs are clipped to [0,1], not [0,0.025]. Raw values and work are in NPZ files. Tuning and held-out samples are independent. The original stage has 500 held-out repetitions per cell (four budgets x four methods), the extension 150 per cell (one budget x four methods). Tuning uses true theta only for offline scoring; production estimators do not receive it.

The first four comparator budget plans selected a single level, so those are degenerate MLMC plans. The larger extension restricts the base level to <=4 and genuinely uses multiple levels. This different planning rule is explicit, not hidden.

Offline costs, excluded from per-estimate work:
- Initial GHA level-moment training: 166,827,744 inner draws.
- Configuration tuning: 139,244,642 draws, across methods/configurations.
- Extension level-moment training: 106,127,872 draws.

Thus results are amortized production comparisons, not equal-total-cost one-shot comparisons. The proved v4 reference needs no fitting. GHA wins on this model, but no universal superiority or asymptotic performance claim follows. Clipping introduces bias and does not preserve unbiased-estimator claims.

Bootstrap intervals use 3,000 resamples per cell and are descriptive, not certified coverage under heavy tails. The largest-budget v4 sample mean work exceeds its nominal expected budget within nontrivial Monte Carlo uncertainty; no hard cap is claimed.

## Reproduction

Python 3.11+ with numpy, scipy, numba, sympy and matplotlib. The recorded run used the versions in `environment.json`. Install via `pip install -r requirements.txt`. Run from the package root:

```sh
python code/verify_phase2.py
python code/summarize_results.py
python code/plot_results.py
```

The existing raw data reproduce summaries without rerunning expensive simulations. To rerun the full benchmark (over 700 million original draws including offline stages and evaluation):

```sh
python code/benchmark.py train --n 4000
python code/benchmark.py tune --n 100
python code/benchmark.py test --n 500
python code/benchmark_extension.py
python code/summarize_results.py
python code/plot_results.py
```

The extension script has its own fixed replication/training settings. Benchmark timings can vary across hardware; no runtime comparison is claimed. Numba's seeded RNG is deterministic for the recorded implementation/environment but bitwise portability across all versions is not guaranteed.

Build the PDF from `report/`:

```sh
pdflatex -interaction=nonstopmode -halt-on-error research_note.tex
pdflatex -interaction=nonstopmode -halt-on-error research_note.tex
pdflatex -interaction=nonstopmode -halt-on-error research_note.tex
```

## Unfinished work

The main arbitrary-law matching upper bound, alpha>=2 matching upper cases, fully distribution-blind rare-event adaptation, complete priority clearance, direct real-valued v4 theory, and equal-total-training-cost comparisons are not supplied. The optional hard-cap theorem and universal equality inf VW=I^2/16 were not pursued ahead of these tasks.
