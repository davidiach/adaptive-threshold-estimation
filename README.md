# Adaptive threshold research hill-climb

Reproducible experiments and formal proof work extending the supplied adaptive
threshold estimation research. Numerical evidence, paper proofs, conjectures,
and Lean kernel-checked results are labeled separately. No novelty claim.

## Current checkpoints

- The supplied numerical check passes all 33 target statements. Sampling is not
  a proof. The Lean compile/freeze gate is in progress; no formal points are
  claimed until its audit passes.
- The constants track has two independently preselected, held-out accepted
  improvements. The conservative choice preserves the original bias theorem;
  the finite-grid winner has an explicit off-grid counterexample.
- The real-valued benchmark is in tuning. Its final choices will be committed
  before the one-time held-out evaluation.
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

## Reproduce

Python 3.12:

```sh
python -m pip install -r requirements.txt
python tools/verify_inputs.py
python tools/check_targets_numeric.py
python tools/check_power_bracket.py
python proposals/constants/bias_audit.py
python constants/score_constants.py constants/candidate_theory.json
python constants/score_constants.py constants/candidate_finite_grid.json
```

The numerical checks run in GitHub Actions. Benchmark commands and full Lean
verification will be documented at their verified checkpoints. All input files
are preserved in [inputs/next-phase](inputs/next-phase/README.md), with the
original hash manifest checked by `tools/verify_inputs.py`.

## Evidence and history

- [Original project brief](BRIEF.md) and [starter README](inputs/STARTER_README.md)
- [Provenance and verification policy](PROVENANCE.md)
- [Run log](RUNLOG.md) and [freeze log](FREEZE_LOG.md)
- [Source audit and theory limitations](TRACK_D.md)
- [Proposals](proposals/)

Local runtimes and dependency caches are excluded from version control.
