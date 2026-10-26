# Adaptive threshold research hill-climb

Reproducible experiments and formal proof work extending the supplied adaptive
threshold estimation research. Numerical evidence, paper proofs, conjectures,
and Lean kernel-checked results are labeled separately. No novelty claim.

The original Tier 1 60/60 checkpoint passed on Windows and in
[independent Linux CI](https://github.com/davidiach/threshold-hillclimb/actions/runs/40410461304).

**Tier 2 proved:** all 13 additional targets (61 points), with unchanged frozen
statements and the stronger 713 definition lock. See [TIER2.md](TIER2.md) and
[approval record](FREEZE_LOG.md). The complete 121/121 checkpoint passes on
Windows and in [independent Linux CI](https://github.com/davidiach/threshold-hillclimb/actions/runs/40417194219).

## Current checkpoints

- Lean Tier 2 checkpoint 002 proves **46/46 targets, 121/121 points**:
  Tier 1 remains 60/60 and Tier 2 is 61/61. The new proofs cover finite
  information inequalities, adaptive stopped-transcript KL/testing bounds,
  the actual Bernoulli classifier and estimator bounds, and the atomic
  rare-event optimizer. No `sorry` remains in the proof modules. Full build,
  exact target types, all 21 frozen hashes, and both audits pass on Windows and Linux
  with only `propext`, `Classical.choice`, and `Quot.sound`.
- The **full uniform 713 bound is proved in Lean**, including concentration,
  the actual stopping rule and coupled work, infinite random-level sampling,
  unbiasedness, and integration over arbitrary magnitude/sign laws. See the
  [formal development](proposals/constants/LEAN713_PROGRESS.md).
- The constants track has two independently preselected, held-out accepted
  improvements. The conservative choice preserves the original bias theorem;
  the finite-grid winner has an explicit off-grid counterexample.
- The direct-real candidate was rejected after its one-time held-out test:
  tuned GHA had lower RMSE at both budgets. See [benchmark results](TRACK_C.md).
- The [research audit](TRACK_D.md) checks the imported Lee–Valiant input, evaluates
  the existing power-margin upper bracket, and proves a limitation on completely
  uniform adaptation to unknown rarity. These arguments are not Lean-checked.

| Constants configuration | Development proxy | Held-out proxy | Scope |
|---|---:|---:|---|
| Original (1, 1) | 6.7788 | 6.7719 | Supplied baseline |
| (0.25, 1) | 5.5506 | 5.5501 | Uniform 713 bound proved in Lean |
| (0.25, 0.5) | 4.2817 | 4.2821 | Finite grid only; uniform bias bound fails |

These proxies use a finite grid, truncated levels, and floating-point probability
recursions. They are not universal variance–work constants. See the
[bias audit](proposals/constants/BIAS_AUDIT.md),
[locked choices](results/constants_candidate_lock.json), and raw result JSONs.
`constants/candidate.json` records the scorer's finite-grid winner;
`constants/candidate_theory.json` records the conservative alternative.

The independently reviewed [paper proof](proposals/constants/UNIFORM_PRODUCT_BOUND.md)
and [complete Lean theorem](lean/ThresholdHC/Uniform713/FullBound.lean) establish
`Var(Y) E[W] < 713 (E[1/D])²` for (0.25,1) when `E[1/D]` is finite,
improving the supplied upper constant 12665. The theorem covers the untruncated
estimator and assumes no error or moment bounds. The [research report](REPORT.md)
distinguishes this guarantee from finite-grid proxies and optimality claims.

## Reproduce

Python 3.12:

```sh
python -m pip install -r requirements.txt
python tools/verify_inputs.py
python tools/verify_experiment_lock.py
python tools/check_targets_numeric.py
python tools/check_targets2_numeric.py
python -m unittest discover -s tools -p 'test_validation.py' -v
python tools/check_power_bracket.py
python proposals/constants/bias_audit.py
python constants/score_constants.py constants/candidate_theory.json
python constants/score_constants.py constants/candidate_finite_grid.json
```

The numerical and Lean checks run in GitHub Actions. After installing the pinned
Lean toolchain and running `lake exe cache get` from `lean/`, use
`python tools/verify_lean_checkpoint.py --sequential` from the repository root.
Then run `python tools/verify_uniform713.py --sequential --require-complete`
to check the full 713 theorem against its recorded specification, hash-locked
local dependencies, and transitive axioms. The original Tier 1 mathematical
statements remain unchanged.
See [environment notes](proposals/lean-environment.md) and
[benchmark reproduction](benchmark/README.md). All input files
are preserved in [inputs/next-phase](inputs/next-phase/README.md), with the
original hash manifest checked by `tools/verify_inputs.py`.

## Evidence and history

- [Original project brief](BRIEF.md) and [starter README](inputs/STARTER_README.md)
- [Provenance and verification policy](PROVENANCE.md)
- [Run log](RUNLOG.md) and [freeze log](FREEZE_LOG.md)
- [Source audit and theory limitations](TRACK_D.md)
- [Proposals](proposals/)

Local runtimes and dependency caches are excluded from version control.
