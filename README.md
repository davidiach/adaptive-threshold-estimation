# Adaptive threshold research hill-climb

Reproducible experiments and formal proof work extending the supplied adaptive
threshold estimation research. Numerical evidence, paper proofs, conjectures,
and Lean kernel-checked results are labeled separately. No novelty claim.

## Current checkpoints

- Lean checkpoint 001 proves **23/33 frozen targets, 34/60 points**, with a
  complete successful kernel audit. Statements compiled unchanged. Further
  proofs are in progress; the separate numerical sanity check is not a proof.
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
| (0.25, 1) | 5.5506 | 5.5501 | Original uniform bias bound proved on paper |
| (0.25, 0.5) | 4.2817 | 4.2821 | Finite grid only; uniform bias bound fails |

These proxies use a finite grid, truncated levels, and floating-point probability
recursions. They are not universal variance–work constants. See the
[bias audit](proposals/constants/BIAS_AUDIT.md),
[locked choices](results/constants_candidate_lock.json), and raw result JSONs.
`constants/candidate.json` records the scorer's finite-grid winner;
`constants/candidate_theory.json` records the conservative alternative.

A separate, independently reviewed [paper proof](proposals/constants/UNIFORM_PRODUCT_BOUND.md)
gives the uniform upper constant **713** for (0.25,1), improving 12665.
That probability argument is not Lean-verified. The [research report](REPORT.md)
distinguishes all evidence levels and remaining questions.

## Reproduce

Python 3.12:

```sh
python -m pip install -r requirements.txt
python tools/verify_inputs.py
python tools/verify_experiment_lock.py
python tools/check_targets_numeric.py
python tools/check_power_bracket.py
python proposals/constants/bias_audit.py
python constants/score_constants.py constants/candidate_theory.json
python constants/score_constants.py constants/candidate_finite_grid.json
```

The numerical and Lean checks run in GitHub Actions. After installing the pinned
Lean toolchain and running `lake exe cache get` from `lean/`, use
`python tools/verify_lean_checkpoint.py --sequential` from the repository root.
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
