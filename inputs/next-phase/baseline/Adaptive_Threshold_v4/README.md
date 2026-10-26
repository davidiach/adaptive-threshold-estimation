# A Distributional Minimax Law for Adaptive Threshold Estimation — v4

**26 October 2026. Consolidated AI-assisted research draft.**

This package replaces the v3 manuscript plus separate review addenda and inserts with one self-contained paper. It is not a journal acceptance, independent human proof certification, or publication-priority certificate. No human authorship or institutional affiliation is assigned by this package.

## Read and reproduce

- `Distributional_Minimax_Law_Adaptive_Threshold_Estimation_v4.pdf`: consolidated manuscript.
- `source/paper.tex`, `source/verification_table.tex`: editable LaTeX.
- `code/calibration.py`: distribution-blind expected-budget and confidence-amplified estimators.
- `code/threshold.py`: dyadic classifier, coupled increment, universal randomized term, illustrative moduli.
- `code/verify_v4.py`: the main v4 verification runner.
- `code/verify.py`: legacy v3 diagnostic runner and the reusable shared-prefix dynamic program. Its old known-envelope allocation is retained for comparison, **not** the v4 main algorithm.
- `results/v4_verification_summary.json`, `results/v4_classifier_checks.csv`, `results/v4_run.log`: actual results recomputed in this revision.
- `review/`: change log, response to Opus, assumptions checklist, and source audit.
- `SHA256SUMS.txt`: content hashes (the manifest itself is excluded).

The recorded environment was Python 3.13.5, NumPy 2.3.5, SciPy 1.17.0, SymPy 1.14.0, and mpmath 1.3.0. Install the pinned packages in an isolated environment:

```sh
python -m venv .venv
. .venv/bin/activate
python -m pip install -r requirements.txt
python code/verify_v4.py
python code/example.py
```

Compile using a LaTeX distribution with the ordinary packages listed in the preamble:

```sh
cd source
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
```

The numeric table records the supplied run. Regenerating tests overwrites the JSON/CSV/log outputs only when redirected as desired; it does not automatically rewrite the LaTeX table. Small numerical residuals can differ across numerical-library versions.

## Main claims and their scope

Write D = |P − 1/2|, μ = law(D), ωμ(h) = Eμ min(1,h/D), and Iμ = Eμ D⁻¹.

1. For every μ on (0,1/2], the distribution-wise minimax RMS risk under expected observation budget B is of order ωμ(B⁻¹/²), with universal constants. The high-confidence version uses ωμ(sqrt(log(1/δ)/B)). A common algorithm depending only on B, or B and δ, attains these bounds simultaneously for all μ and conditional sign functions q.
2. An estimator unbiased for all q at fixed μ can have **both** uniformly finite variance and expected work exactly when Iμ < ∞. The universal lower coefficient in VW ≥ Iμ²/16 is sharp; the construction proves VW ≤ 12665 Iμ². Equality at 1/16 is shown for fixed-gap laws, not every law.
3. A continuous-magnitude, observable-state hard subclass satisfies Giles–Haji-Ali Assumptions 2.1 and 2.4 with uniform constants and exhibits the critical ε⁻² log²(1/ε) cost. The claim concerns sample-oracle access without additional cross-state structure.

## API and observation contract

`estimate_budget(new_coin, budget, rng)` receives no latent magnitude or population law. Each invocation of `new_coin()` must return a fresh independent coin's callback. Calling that callback with integer n returns the number of successes in n additional, conditionally independent Bernoulli observations **of that same coin**. The example constructs a synthetic population inside the oracle only; the algorithm does not receive its parameters.

`estimate_confidence(new_coin, budget, delta, rng)` returns a median of calibrated groups. It does **not** return a data-computable error radius. The theorem's radius involves the unknown true ωμ. Choosing a budget for a numerical target error requires additional information.

`calibrate(draw, cap, rng)` requires IID calls returning finite value and integer work between 0 and cap, with strictly positive mean work. Within-call value/work dependence is allowed. Zero mean work cannot be detected from finite samples; it is an input-contract violation that can cause nontermination. Pilot values must be discarded; production samples must be fresh and independent.

## Expected work is not a runtime limit

The mathematical cost counts Bernoulli observations, not Python operations, random bits, or simulation overhead. Total work is random and unbounded. A supplied smoke test with budget 1024 used 1903 observations; this is compatible with the expected-budget theorem. Adding a hard timeout or truncating the pilot changes the guarantee and requires new analysis.

Outputs can be negative or exceed one. Clipping a finite-budget output into [0,1] can reduce its estimation error but destroys exact calibration-mean/variance identities; clipping the unbiased estimator destroys unbiasedness. The unbounded-level unbiased implementation can occasionally require very large work. No production latency or practical speedup is claimed.

Finite machine arithmetic is an implementation approximation to exact-arithmetic definitions. The reference implementation explicitly rejects caps outside its 64-bit integer sampling range. Mathematical results are not restricted to those representable caps.

## Verification, not certification

The run includes seven symbolic identities; 630 predictive-KL comparisons and 280 hard-pair comparisons in both directions; 315 symmetric-KL/Hellinger comparisons at 120-decimal precision; two deterministic-endpoint checks; 264 floating-point shared-prefix dynamic programs over 11 magnitudes, both signs, and caps through 2048; 96 modulus comparisons; five inverse-moment evaluations; four calibration distributions with 4000 Monte Carlo repetitions each; nine API smoke runs; and six invalid-input checks.

The dynamic program uses probability recursion, not Monte Carlo, but its arithmetic is floating point. Calibration simulations are Monte Carlo. Neither finite grids nor simulations certify universal theorems. No unprovided reviewer logs are included or treated as this package's own computations. The analytic upper constants remain 85 and 149 despite smaller observed ratios.

The review reports concern component arguments; the consolidated manuscript still needs specialist proof and priority review. Rare-event localization, hard-work caps, fixed analytic/Gevrey classes, and uniformly observable confidence radii are not resolved here.
