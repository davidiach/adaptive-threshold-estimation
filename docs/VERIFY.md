# Full verification commands

The follow-up's scoped critical-proof components have a separate check:

```sh
python tools/verify_critical_components.py
python -m unittest discover -s tools -p 'test_critical_components.py' -v
```

After building the existing Lean dependencies with the kernel commands below,
this checks eight exact targets: entropy packing, the compact-convex common
point, seeded Bernoulli prefix information, finite-prefix event transfer,
the statistical finite-gap sign-entropy theorem, actual stopped-suffix
independence from output and work, observable sequential restart laws and
expected work, and arbitrary fixed-count repetition with iid outputs and
linear expected work. It audits all 117
declarations in these modules and writes fresh evidence under
`.runtime/critical-components/`. It does not certify the continuum base-cost
or critical minimax theorem. See the
[follow-up audit](CRITICAL_AUDIT.md#formalization-boundary-and-first-checkpoint).

For the integrated research packages, including the full critical-law paper
theorem and Psi counterexample:

```sh
python tools/verify_research.py
python tools/verify_population_research.py
```

This verifies all five current frozen manifests and the research identity
locks, reviewed four-file paper bundle, exact scalar arithmetic, 20 certified
finite-prefix experiments plus two sufficient-statistic checks, Route A finite
experiments, finite-support identities, and the recorded Fisher policies.
It writes fresh diagnostics to a temporary directory; use `--output-dir` with
a nonexistent directory to choose the destination. Published evidence stays
unchanged. Run the guard regressions listed below as well. See the
[checkpoint](../research/2026-10-27-nonlinear-critical/CHECKPOINT.md) and
[validation record](../research/2026-10-27-nonlinear-critical/validation.json).
These are reproducibility and sanity checks; the statistical theorem is a
reviewed paper proof, not a Lean result. CI now runs this replay on research
changes and checks the five locked Route A Lean roots after the complete
Tier 6 audit. These checks do not certify the continuum paper proof.

Historical research `validate.py` and acceptance scripts preserve their original
checkout snapshots, including the old CI workflow. Replay those at the source
commits named in their checkpoints. They may reject an integrated checkout
because its workflow and completed formalization have advanced; their original
locks and recorded evidence have not been rewritten.

The population replay additionally checks both sealed research packages,
recomputes exact single-coin and population arithmetic, finite Bayes policies,
feedback certificates and bounded-depth identities, audits all 7,680 recorded
synthetic rows, and replays one predesignated replicate in each of 240 cells.
It runs in disposable copies under `.runtime/`; historical reports and source
locks are unchanged. See the [research index](../research/README.md) for how the
earlier checkpoints relate to the later full critical-law paper theorem.

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
python tools/verify_tier5.py --sequential --require-complete
python tools/verify_tier6.py --sequential --require-complete
```

The first command rebuilds the scored proof modules and runs the frozen scorer plus an independent audit. The arithmetic command checks the separate scalar lemmas. The final three commands enforce complete proofs of their exact specifications and check their source locks and transitive axioms. Passing arithmetic or numerical checks alone does not establish those probability theorems.

## Critical-regime paper checkpoint

The critical note is a reviewed paper proof, not a new Lean target. Its
preservation, exact scalar diagnostics, current 34 guard regressions and nine
finite Fisher-policy replays run with:

```sh
python research/2026-10-27-critical-two/validate.py
```

This writes only that research directory's diagnostics; it does not replace
published results or rebuild unchanged Lean dependencies. The
[validation record](../research/2026-10-27-critical-two/validation.json) records
exact commands, exit codes, source hashes and limits. The numerical checks do
not prove the paper theorem. Compile the standalone
[TeX note](../research/2026-10-27-critical-two/construction.tex) separately;
compilation is also not mathematical verification.

## Evidence and CI

The [consolidated v5 manuscript](../paper/v5/README.md) is checked with
`python tools/build_v5.py --check`. This verifies the inherited source
identities, generated proofs, unique labels, and citation references.
Its PDF is separately compiled and visually inspected; these checks do not
extend the mathematical claims verified by Lean.

The critical-law [review packet](../paper/critical-review/README.md) is assembled
from the locked mathematical sources and a short editable overview. Check its
source identity with `python tools/build_critical_review.py --check`. PDF
compilation and visual inspection are documented with the packet and are
separate from mathematical verification.

| Check | Published record |
|---|---|
| Scored Lean statements | [lean_tier2_002_checkpoint.json](../results/lean_tier2_002_checkpoint.json) |
| Full 713 theorem | [uniform713_status.json](../results/uniform713_status.json) |
| Randomized stopping and optimizer | [tier3_status.json](../results/tier3_status.json) |
| Full infinite-transcript KL | [tier4_status.json](../results/tier4_status.json) |
| Unrestricted adaptive-creation KL (9 targets, 109 declaration checks) | [tier5_status.json](../results/tier5_status.json) |
| Canonical experiments and minimax RMS lower bound (11 targets) | [tier6_status.json](../results/tier6_status.json) |
| Input preservation | [MANIFEST_SHA256.txt](../inputs/next-phase/MANIFEST_SHA256.txt) |
| Frozen specifications and tools | [FROZEN.sha256](../FROZEN.sha256), [TIER3_FROZEN.sha256](../TIER3_FROZEN.sha256), [TIER4_FROZEN.sha256](../TIER4_FROZEN.sha256) |
| Workflow definition | [checks.yml](../.github/workflows/checks.yml) |

The completed research commit `23988c7` passed [Linux CI](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/40468287646). Later runs are available on the [workflow page](https://github.com/davidiach/adaptive-threshold-estimation/actions/workflows/checks.yml). Historical logs retain the terminology and checkpoints used when each result was produced.
