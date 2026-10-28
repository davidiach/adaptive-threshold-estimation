# Track B: two accepted candidates and a uniform-bound audit

**Finite-grid results: numerical evidence, not a universal theorem.**
The frozen evaluator computes probability recursions in floating point.
All 169 tuning trials used only the fixed development grid and no randomness.
Both candidates and their testing order were locked in
`results/constants_candidate_lock.json` and published in commit `f4f8e84`
before either held-out evaluation. Each candidate was tested once, in the
declared order; no subsequent tuning used held-out results.

| Configuration (k1,k2) | Dev proxy | Held-out proxy | Result |
|---|---:|---:|---|
| Baseline (1,1) | 6.778762 | 6.771882 | Valid baseline |
| Theory-compatible (0.25,1) | 5.550646 | 5.550060 | ACCEPT |
| Finite-grid winner (0.25,0.5) | 4.281742 | 4.282069 | ACCEPT |

The winner reduces the dev proxy by 36.84% and held-out proxy by 36.77%.
Both candidates have maximum grid bias ratio 0.717774 and telescoping
residual below 3.2e-15. The grid covers caps through 4096 only.
`constants/candidate_finite_grid.json` contains the finite-grid winner;
`constants/candidate_theory.json` and `constants/candidate.json` hold the
theorem-compatible candidate.
There is no proof that these are globally optimal parameters, even for the
finite-grid objective: this was a coarse grid plus two local refinements.

**Uniform guarantee: proved in Lean and on paper.**
For `(0.25,1)`, `proposals/constants/UNIFORM_PRODUCT_BOUND.md` proves
conditional second moment below `23/d` and expected work below `31/d`.
Therefore the untruncated geometric single-term estimator has
`Var(Y) E[W] < 713 (E[1/D])^2` whenever `E[1/D]<infinity`.
The proof uses a tighter error envelope, one-sided survival concentration,
and the pathwise fact that the coarse classifier stops no later than the
fine classifier. The complete Lean theorem is
`ThresholdHC.Uniform713.full_bound_713`, checked against the recorded
`FullBound713Statement` by `python tools/verify_uniform713.py --require-complete`.
Its natural model assumptions contain no error, work, or moment bounds.
The earlier exact rational checks remain in `results/constants_uniform_bound.json`;
the full kernel audit is recorded separately in `results/uniform713_status.json`.
This improves the supplied analytic upper constant 12665 but remains well
above both the finite-grid proxy and the lower bound 1/16. No optimality claim.

**Counterexample: proved on paper, with exact rational checks.**
The finite-grid winner `(0.25,0.5)` fails the original uniform bias bound.
At positive sign, `d=0.1`, and cap `N=2^97`, the all-tails event through
prefix 128 forces a negative stop and has probability exceeding the proposed
bias bound by a factor greater than 2907. This result is independent of all
held-out errors. The full argument is in
`proposals/constants/BIAS_AUDIT.md`, with exact checks in
`results/constants_bias_counterexample.json`. Thus the score winner should
not replace the theory-compatible estimator when that theorem is required.

Reproduction, from a clean copy without an existing selection lock:

```powershell
python tools/tune_constants.py --stage coarse
python tools/tune_constants.py --stage refine
python tools/tune_constants.py --stage fine
python tools/tune_constants.py --select
Copy-Item results/constants_baseline.json results/constants_best.json
python constants/score_constants.py constants/candidate_theory.json --accept results/constants_best.json
python constants/score_constants.py constants/candidate_finite_grid.json --accept results/constants_best.json
python proposals/constants/bias_audit.py
python proposals/constants/uniform_constant_checks.py
```

Published search records must be preserved. To reproduce just the accepted
score without modifying the best ledger, omit `--accept` and supply either
candidate JSON. The search script refuses post-lock tuning or lock overwrite.
