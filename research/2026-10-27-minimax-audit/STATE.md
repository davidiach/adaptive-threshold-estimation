# Research checkpoint, 27 October 2026

This is a substantive bounded research pass, not completion of the arbitrary-law minimax mission. The central conjecture remains open. No work is promised to continue in the background.

## Baseline and preservation

- Repository: https://github.com/davidiach/adaptive-threshold-estimation; local checkout `C:/Users/User/Desktop/Projects/math/threshold-hillclimb`.
- Initial HEAD: `ddf950122776a059e62c808021bbd2b59c39f0b0`, branch `main`.
- Initial tracked modifications: README.md, docs/RESULTS.md, docs/VERIFY.md, docs/process/REPORT.md, paper/UPDATES.md. Initial untracked directories: lean/ThresholdHC/ResearchRouteA and research/2026-10-27-route-a. They are inherited work.
- Created local branch `research/rare-minimax-20261027`; no reset, force push, remote edit, publication, or external message.
- No applicable AGENTS.md found in repository or workspace ancestors. The current request supersedes the historical score-oriented brief.
- Read actual README, REPORT, TRACK_D, benchmark docs/source, lock/verification tools, v4 TeX and continuation TeX, and dirty route-a construction. Coverage is mapped separately.
- `BASELINE_SNAPSHOT.json` records current tracked and preexisting untracked bytes copied to `../minimax-baseline-snapshot`, not just Git HEAD. New research was excluded. Original logs were never overwritten.
- Concurrent activity committed inherited route-a and documentation through `d4f74a2`, `db25e62`, and `c11aa9b`, and created/edited Tier5 files. This task did not author those commits/files. Exact proof dependency hashes, not a moving global HEAD alone, identify verification scope. See the formal audit's explicit global-stability failure and separate scoped result.
- The snapshot caught Route A's generated status.json at valid=false/complete=false while its source and documentation were being finalized. Its later build.log/status.json changed during concurrent work and were committed externally. Our fresh exact-closure kernel audit, rather than either stored status, supplies verification here. The final all-protected-bytes gate deliberately remains false for those two generated files; v4, old results, locks, specifications and proof sources match the snapshot. The changed generated files are recorded, not restored or silently ignored.

## Environment actually used

Windows 11 10.0.26300; Python 3.12.2; NumPy 2.4.4; SciPy 1.17.1; Numba 0.68.0; llvmlite 0.50.0; mpmath 1.3.0. Numerical packages were loaded from the repository's preexisting ignored `.runtime/python`.
Lean is pinned to 4.36.0-rc1; Mathlib commit `9bdd0bc71aaae0fd83889f9aacd70c32fccd1bcd`, with all dependency pins retained. Actual Lean commands/outputs and version appear in `formal/`.
PDF/chart work uses the bundled ReportLab 4.4.9, Pillow 12.3.0, Poppler and desktop Tectonic 0.17.0+20260731. No new paid service or package purchase was used. Matplotlib was unavailable; the figure uses ReportLab graphics. Native editor compilation succeeded; local compilation/export diagnostics are in `logs/latex-build*.log`.

## Executed work

`baseline.py`: fourteen original integrity/numerical/regression commands, all exit zero in the snapshot, including original locks, inputs, experiment lock, numerical targets, unit tests, constant/bias checks, benchmark invariants, and inherited route-a exact checks. Commands, durations, and outputs: `BASELINE_RUNS.json`, `logs/baseline-*.log`.

`replay_benchmark.py`: four historical cells, 500 replications each, all 2,000 values and work counts byte-exact. This reuses already-opened historical seeds and is reproduction, not a new held-out confirmation. Work: 81,363,392 original observations; see `BASELINE_BENCHMARK_REPLAY.json`.

`test_experiments.py`: four checks passed before the new freeze, including 7,308 finite decision comparisons, 800 exact original-real-oracle comparisons, 1,050 bounded term checks and the finite telescope identity. Initial Numba boolean conversion failure and fix are recorded in FAILED_APPROACHES; no test or acceptance criterion was weakened.

`experiments.py lock`, then `experiments.py test`: implementation hash locked before 42 new cells, 128 replications each; 5,376 runs, 52,720,432 charged inner observations. No exclusions, refit, retune, or repeated test. Per-cell seeds, timings, outer counts, raw values and costs are retained. Measured test execution was about 2.30 seconds on the already warmed compiled kernels; wall time is environment-specific and excludes other verification/reporting work.

`check_exact.py`: 660 exact rational feasible-grid comparisons plus 36 majority-channel identities. `theorem/critical.py`: 36 exact finite classifiers, eight exact two/three-scale identities, three retained counterexample instances. `formal/check_stopping_counterexample.py`: 202 exact finite-prefix stopping diagnostics. These are finite arithmetic evidence, not unrestricted statistical theorem certificates.

New paper proofs underwent explicit separate-agent adversarial review. This is not human specialist review or independently established priority. The source audit records inspected passages and inaccessible material. No novelty claim is made.

## Scope remaining

No matching arbitrary-law Psi upper theorem or counterexample to Psi; no proof of necessity/removal of the critical iterated logarithm; no sharp general adaptation penalty; no new complete Lean rare-event theorem; no full practical matched-accuracy superiority. Current Tier5 work is treated only to its verified scope in FORMAL_COVERAGE, not assumed complete from a green partial workflow.
