# Full verification commands

For the additive 27 October rare-event result and separate-supremum bridge:

```sh
python research/2026-10-27-route-a/check_construction.py
python lean/ThresholdHC/ResearchRouteA/verify.py
```

The first command checks exact rational finite-prefix experiments and retains unresolved tails; it does not certify the main theorem. The second checks the new locked formal specification, exact types, and all five public roots. See [formal replay details](../research/2026-10-27-route-a/formal-audit.md) for the local Windows environment. The main theorem remains a reviewed paper proof. [Baseline replay records](../research/2026-10-27-route-a/BASELINE.md) and the new `acceptance_check.py` keep diagnostics separate from published `results/`; the latter compares against this session's recorded source snapshot.

Use Python 3.12 and the toolchain in [lean/lean-toolchain](../lean/lean-toolchain). The pinned package revisions are in [lean/lake-manifest.json](../lean/lake-manifest.json); do not run `lake update` on this frozen checkout. [Environment notes](../proposals/lean-environment.md) include the existing local Windows installation.

Several verifiers write logs or summaries into `results/`. Run this sequence in a disposable checkout if you want the published evidence to remain byte-for-byte unchanged:

```sh
git clone https://github.com/davidiach/adaptive-threshold-estimation.git
cd adaptive-threshold-estimation
python -m pip install -r requirements.txt
cd lean
lake exe cache get
cd ..
```

Run all remaining commands from that checkout's root. They retain every verifier from the former README's “Reproduce” section, plus the arithmetic and benchmark implementation checks.

## Integrity, numerics, and unit tests

```sh
python tools/verify_inputs.py
python tools/verify_experiment_lock.py
python tools/freeze.py --verify
python tools/check_targets_numeric.py
python tools/check_targets2_numeric.py
python -m unittest discover -s tools -p 'test_validation.py' -v
python -m unittest discover -s tools -p 'test_tier3_validation.py' -v
python -m unittest discover -s tools -p 'test_tier4_validation.py' -v
python tools/check_power_bracket.py
python proposals/constants/bias_audit.py
python proposals/constants/uniform_constant_checks.py
python constants/score_constants.py constants/candidate_theory.json
python constants/score_constants.py constants/candidate_finite_grid.json
python constants/score_constants.py constants/candidate.json
python benchmark/verify_real.py
```

The shorter `python -m unittest discover -s tools -p 'test_*.py' -v` runs all validation test modules present in the checkout. Constant scoring without `--accept` evaluates the recorded configurations without changing the best-score ledger. `verify_experiment_lock.py` recomputes summaries from stored samples; it does not repeat the held-out experiment. Full benchmark resimulation is a separate procedure in [benchmark/README.md](../benchmark/README.md).

## Lean kernel checks

```sh
python tools/verify_lean_checkpoint.py --sequential
python tools/verify_uniform_arithmetic.py
python tools/verify_uniform713.py --sequential --require-complete
python tools/verify_tier3.py --sequential --require-complete
python tools/verify_tier4.py --sequential --require-complete
```

The first command rebuilds the scored proof modules and runs the frozen scorer plus an independent audit. The arithmetic command checks the separate scalar lemmas. The final three commands enforce complete proofs of their exact specifications and check their source locks and transitive axioms. Passing arithmetic or numerical checks alone does not establish those probability theorems.

## Evidence and CI

| Check | Published record |
|---|---|
| Scored Lean statements | [lean_tier2_002_checkpoint.json](../results/lean_tier2_002_checkpoint.json) |
| Full 713 theorem | [uniform713_status.json](../results/uniform713_status.json) |
| Randomized stopping and optimizer | [tier3_status.json](../results/tier3_status.json) |
| Full infinite-transcript KL | [tier4_status.json](../results/tier4_status.json) |
| Input preservation | [MANIFEST_SHA256.txt](../inputs/next-phase/MANIFEST_SHA256.txt) |
| Frozen specifications and tools | [FROZEN.sha256](../FROZEN.sha256), [TIER3_FROZEN.sha256](../TIER3_FROZEN.sha256), [TIER4_FROZEN.sha256](../TIER4_FROZEN.sha256) |
| Workflow definition | [checks.yml](../.github/workflows/checks.yml) |

The completed research commit `23988c7` passed [Linux CI](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/40468287646). Later runs are available on the [workflow page](https://github.com/davidiach/adaptive-threshold-estimation/actions/workflows/checks.yml). Historical logs retain the terminology and checkpoints used when each result was produced.
