# Full verification commands

The critical lower and both upper component verifiers use `lake build`, which
rebuilds stale transitive imports before the kernel and axiom checks. Use
`--sequential` to build one registered module at a time on constrained machines.
The lower audit checks that all 43 statement examples are present exactly once;
its source hashes cover the full local import closure. The upper audits also
check the review-time dependency snapshots in their specification freeze records.
These additions preserve the original frozen statements and published evidence.

The critical upper estimator checkpoint has a scoped audit, run after the
critical and distribution-blind builds below:

```sh
python tools/verify_critical_upper_components.py
python -m unittest discover -s tools -p 'test_critical_upper_components.py' -v
```

It checks every declaration in the eighteen `CriticalUpper` modules, their
transitive axioms, and the unchanged pre-proof full specification. The
[component record](../results/critical_upper_components_002.json) includes
calibration and the actual population unbiased estimator, second moment and
expected work. It does not certify the full upper theorem: budgeted fresh-coin
aggregation and its Tier 6 realization remain pending. See the
[exact scope](CRITICAL_AUDIT.md#upper-construction-checkpoint).

The full distribution-blind upper theorem has a separate
[verification record](BLIND_UPPER.md). After the baseline, Tier 6, and critical
builds below, run:

```sh
python tools/verify_blind_upper_components.py
python -m unittest discover -s tools -p 'test_blind_upper_components.py' -v
```

This rebuilds 45 modules plus three existing prerequisites and checks the
final theorem against its unchanged frozen type, together with all 373
declaration roots and their transitive axioms. It includes actual population
cost/output identities, termination, budget selection and uniform RMS risk.
The separate critical upper remains pending, with its completion flag false.

The follow-up's scoped critical-proof components have a separate check:

```sh
python tools/verify_critical_components.py
python -m unittest discover -s tools -p 'test_critical_components.py' -v
```

After building the existing Lean dependencies with the kernel commands below,
this checks forty-three exact targets: entropy packing, the compact-convex common
point, seeded Bernoulli prefix information, finite-prefix event transfer,
the statistical finite-gap sign-entropy theorem, actual stopped-suffix
independence from output and work, observable sequential restart laws and
expected work, arbitrary fixed-count repetition with iid outputs and linear
expected work, the constructed sign test's error and work bounds, and finite-gap
real-output estimator entropy, constructed population moment identities, and
conditional finiteness derived from population guarantees, the extended-variance
floor, conversion of variance bounds to raw moments, and quantitative good-gap
selection over the capped global class, the exact quadratic gap law, and its
finite-scale null-cost product under explicit annulus-mass and scale-count
hypotheses, activation normalization and its cost bounds, and the full critical
single-coin raw-moment and variance base-cost theorems for every rarity,
plus capped full-transcript reconstruction, canonical Hellinger affinity
preservation, exact expected-work preservation, and actual population
compactness, affine observation geometry, and continuous convex Hellinger
constraints on the separated population-pair set, actual observable estimator
realization from the affinity modulus, its critical null-work obstruction, and
an admissible separated pair for each capped policy, its normalized
Hellinger/work constraint, and one common separated pair valid simultaneously
for all capped policies with arbitrary measurable seeds. Actual finite revealed
mixtures, reseeding and cap invariance are proved in the dependency chain.
It also checks the exact independent-tape population law, actual local work
charging, and the common pair's transfer to every fixed finite coin family and
deterministic horizon. It then checks the unrestricted transfer with arbitrary
measurable population seeds, separate endpoint termination, eventual exact tape
reconstruction, terminal affinity, algorithm and minimax lower rates, budget
nonemptiness, and the trivial upper bound by rarity. The full rare-prior class
is used in the budget and risk. The matching critical upper is still pending.
It audits all 674
declarations in these modules and writes fresh evidence under
`.runtime/critical-components/`. The base-cost flag now certifies the actual
single-coin theorem; the full critical minimax flag remains false. See the
[follow-up audit](CRITICAL_AUDIT.md#current-formal-boundary).

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
