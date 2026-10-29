# Full verification commands

## General-law rare-event manuscript v2

From the repository root, using the Python standard library:

```sh
python tools/verify_rare_event_manuscript.py
```

This verifies the immutable [v2 payload](../paper/rare-event/v2/MANIFEST.sha256)
and [historical audit records](../paper/rare-event/audit/MANIFEST.sha256), then
runs the certificate and revision verifiers in a temporary copy. It rechecks
33 exact lower certificates, 9 upper policies, 9 stopping decisions, two
perfect-label examples, and rejection of six targeted corruptions. It also
replays the independent revision audit's finite computations, including the
new examples, constants, and genie comparisons. Published files are unchanged.

The [build record](../paper/rare-event/v2/VERIFICATION.json) covers the delivered
55-page PDF and its visual review; [build instructions](../paper/rare-event/README.md#verify-and-build)
explain reproduction in a disposable copy. The current command verifies source
and PDF identity, not bit-for-bit TeX rebuild reproducibility. These finite
checks do not formally verify the manuscript's general statistical or limit
theorems. See the [claim status](RESULTS.md#general-law-rare-event-characterization)
and [audit qualifications](../paper/rare-event/audit/README.md).

The all-size finite-gap and explicit single-coin base-cost extension has a
separate audit: `python tools/verify_critical_all_sizes.py` (optionally
`--sequential`). It checks four exact target types, every new declaration's
axioms, and the locked specification/dependency snapshot made during
implementation. The saved local result is
[`critical_all_sizes_002.json`](../results/critical_all_sizes_002.json).
The [initial record](../results/critical_all_sizes_001.json) remains unchanged;
the current record includes the reviewed source documentation correction.
Its constants are 1/4096 for entropy at every gap count, 1/10000000000 for
raw second moment times null work, and 1/15000000000 for variance times
null work. The older 1/512 entropy coefficient retains its large-count
hypothesis. No explicit population minimax constant is certified by this audit.

The critical lower and both upper component verifiers use `lake build`, which
rebuilds stale transitive imports before the kernel and axiom checks. Use
`--sequential` to build one registered module at a time on constrained machines.
The lower audit checks that all 43 statement examples are present exactly once;
its source hashes cover the full local import closure. The upper audits also
check the review-time dependency snapshots in their specification freeze records.
These additions preserve the original frozen statements and published evidence.

The Psi verifier also rebuilds transitive imports with Lake and checks the
review-time dependency snapshot of its variational model and specifications.

The full unbiased-estimation converse has a dedicated audit:

```sh
python tools/verify_unbiased_converse.py --sequential
python -m unittest discover -s tools -p 'test_unbiased_converse.py' -v
```

The [record](../results/unbiased_converse_001.json) checks all ten modules,
38 declaration roots and their transitive axioms, and the exact full target
`UnbiasedConverseStatement`. The model uses the existing observable adaptive
experiment, explicit integrability in unbiasedness, extended variance, and actual
flip work. Its conclusion is inverse-gap integrability and the variance-work
lower bound with coefficient 1/16. The audit locks both the target definitions
and their transitive project dependencies, including the underlying experiment,
and rejects source changes during the run. The model and target were compiled
before supporting proofs; the dependency snapshot was recorded after the proof
drafts, as its [chronology](../tools/unbiased_converse_specification_freeze.json)
states. This audit does not certify a new 713 realization or stronger oracle model.

The 713 construction in the same observable model has its own audit:

```sh
python tools/verify_observable713.py --sequential
python -m unittest discover -s tools -p 'test_observable713.py' -v
```

The [record](../results/observable713_001.json) covers all eight modules, 47 declarations, and
both exact targets: `Observable713Statement` and `ObservableUnbiasedIffStatement`.
It certifies one algorithm before every gap law, unbiasedness for every
measurable sign law, uniform extended variance at most `23 I`, actual work
at most `31 I`, and product of separate suprema at most `713 I²`. The second
target combines this construction with the existing converse to prove the
existence characterization. The specification and its transitive model
dependencies were compiled and frozen before the new supporting proofs.
The verifier rejects missing or weakened targets, unregistered modules,
altered frozen dependencies, proof escapes, unexpected axioms, and source
changes during the audit. CI runs the audit and its regression tests.

The confidence characterization in the same observable model has a dedicated audit:

```sh
python tools/verify_confidence.py
python -m unittest discover -s tools -p 'test_confidence.py' -v
```

The [record](../results/confidence_001.json) covers 18 modules, all 107
declaration roots, and four exact targets: the algorithm-level lower bound,
one law-independent upper family, the two-sided minimax characterization,
and nonvacuity. The constants are `1/64` and `8192`, for `B >= 1` and
`0 < delta <= 1/4`. The definition uses strict error exceedance, all measurable
sign laws, arbitrary measurable seed spaces, and the original expected number
of actual flips. The full targets and their transitive model definitions were
compiled and frozen at `76e9a8f` before supporting proofs. The verifier rebuilds
imports, checks every declaration's transitive axioms, and rejects altered
models, weakened targets, missing modules, and changes during the audit.
The statistical independence of the repetitions and their actual execution
are proved; neither is assumed in the final target. CI runs this audit and
its regression tests. The radius is a theoretical function of the gap law,
not a data-computable confidence interval over all unknown laws.

The magnitude-oracle lower bounds have a separate audit:

```sh
python tools/verify_oracle_lower.py
python -m unittest discover -s tools -p 'test_oracle_lower.py' -v
```

Its [record](../results/oracle_lower_001.json) covers 10 modules and all 54
public declaration roots. Eight exact targets cover canonical realization,
fresh/revisit semantics, the general RMS and confidence lower bounds,
both concrete oracle interfaces, their minimax bounds, and nonvacuity.
The coefficients are `1/64` and `15/(256 sqrt(2))`, respectively. The model,
eight statements, and 33 transitive model dependencies were compiled and
frozen at `3474a37` before lower-bound and semantic-embedding proofs.
The revealed model grants the full iid magnitude array; the selected model
allows continuous-valued gap choices based on previous flips and preserves
the gap on reuse. The audit checks the frozen types and all transitive axioms;
CI runs both the audit and mutation tests for each required target. Only
`propext`, `Classical.choice`, and `Quot.sound` are permitted.

The actual critical-law Psi formula, two-sided rate and unrestricted minimax
counterexample have a separate audit. After the prerequisite builds below:

```sh
python tools/verify_critical_psi.py
python -m unittest discover -s tools -p 'test_critical_psi.py' -v
```

The [Psi record](../results/critical_psi_001.json) checks the frozen variational
model and all three exact target types, all six proof modules, every declaration's
transitive axioms, and source stability during the run. The
[scope](CRITICAL_AUDIT.md#exact-psi-comparison-and-minimax-separation) distinguishes
the formal witness budget from the preserved paper's particular sequence.

The full critical upper theorem has a dedicated audit, run after the
critical and distribution-blind builds below:

```sh
python tools/verify_critical_upper_components.py
python -m unittest discover -s tools -p 'test_critical_upper_components.py' -v
```

It checks every declaration in the 26 `CriticalUpper` modules, their transitive
axioms, and both exact full targets against the unchanged pre-proof
specification. The [full record](../results/critical_upper_components_003.json)
includes the unbiased estimator, independent fresh-coin aggregation, actual
controller work/output identities, original-experiment realization, and every
budget regime. The universal upper coefficient is 100000. The explicit Psi
comparison is certified by the separate Psi audit above. See the
[exact scope](CRITICAL_AUDIT.md#upper-construction-checkpoint).

The full distribution-blind upper theorem has a separate
[verification record](BLIND_UPPER.md). After the baseline, Tier 6, and critical
builds below, run:

```sh
python tools/verify_blind_upper_components.py
python -m unittest discover -s tools -p 'test_blind_upper_components.py' -v
```

Lake builds 45 modules plus three existing prerequisites, rebuilding any stale
import, and the audit checks the
final theorem against its unchanged frozen type, together with all 373
declaration roots and their transitive axioms. It includes actual population
cost/output identities, termination, budget selection and uniform RMS risk.
The critical upper has its own full audit above; historical records retain their original completion flags.

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
is used in the budget and risk. The matching critical upper has the separate audit above.
It audits all 674
declarations in these modules and writes fresh evidence under
`.runtime/critical-components/`. The base-cost flag now certifies the actual
single-coin theorem. This lower-only record retains its historical
`full_critical_minimax_theorem_verified=false` flag; the matching upper and Psi
comparison have the separate completed records above. See the
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
These are reproducibility and sanity checks for the preserved paper bundle.
The completed statistical Lean theorems are checked by the separate audits
above. CI runs this replay on research changes and checks the five locked
Route A Lean roots after the complete Tier 6 audit. These replay checks do
not themselves certify the continuum paper proof.

Historical research `validate.py` and acceptance scripts preserve their original
checkout snapshots, including the old CI workflow, so they may reject an
integrated checkout whose workflow and formalization have advanced. The
critical-two, nonlinear-critical, Route A and minimax-audit snapshots also
captured an uncommitted `constants/candidate.json`, so their scripts reject
every clean checkout, including their source commits; the minimax-audit
acceptance records `valid: false` instead of stopping. Use
`python tools/verify_research.py` to replay their locked identities and finite
diagnostics. Their original locks and recorded evidence have not been rewritten.

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
python benchmark/verify_production.py
```

The shorter `python -m unittest discover -s tools -p 'test_*.py' -v` runs all validation test modules present in the checkout. Constant scoring without `--accept` evaluates the recorded configurations without changing the best-score ledger. `verify_experiment_lock.py` recomputes summaries from stored samples; it does not repeat the held-out experiment. The locked `verify_real.py` checks tape copies of the benchmark's stopping state machines; `verify_production.py` replays the production routines that generated the results against an independent classifier. Full benchmark resimulation is a separate procedure in [benchmark/README.md](../benchmark/README.md).

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

The first command rebuilds the scored proof modules and runs the frozen scorer plus an independent audit. The arithmetic command checks the separate scalar lemmas. The final five commands enforce complete proofs of their exact specifications and check their source locks and transitive axioms. Passing arithmetic or numerical checks alone does not establish those probability theorems.

## Critical-regime paper checkpoint

The earlier restricted-class critical note remains a reviewed paper proof.
Its source-lock preservation, exact scalar diagnostics and nine finite
Fisher-policy replays are re-run by:

```sh
python tools/verify_research.py
```

This writes fresh evidence to a temporary directory, or to `--output-dir`; it
does not replace published results or rebuild Lean dependencies. The guard
regressions are the `tools/test_*.py` suites listed above;
`python -m unittest discover -s tools -p 'test_*.py' -v` runs them all.
The package's own `validate.py` cannot be replayed from a clean checkout, as
noted above. The
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
| Full observable unbiased converse and 1/16 lower coefficient | [unbiased_converse_001.json](../results/unbiased_converse_001.json) |
| Observable 713 construction and unbiased existence iff finite inverse moment | [observable713_001.json](../results/observable713_001.json) |
| Full observable confidence characterization, upper family, and nonvacuity | [confidence_001.json](../results/confidence_001.json) |
| Canonical revealed/selected-magnitude RMS and confidence lower bounds | [oracle_lower_001.json](../results/oracle_lower_001.json) |
| Input preservation | [MANIFEST_SHA256.txt](../inputs/next-phase/MANIFEST_SHA256.txt) |
| Frozen specifications and tools | [FROZEN.sha256](../FROZEN.sha256), [TIER3_FROZEN.sha256](../TIER3_FROZEN.sha256), [TIER4_FROZEN.sha256](../TIER4_FROZEN.sha256) |
| Workflow definition | [checks.yml](../.github/workflows/checks.yml) |

The completed research commit `23988c7` passed [Linux CI](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/40468287646). Later runs are available on the [workflow page](https://github.com/davidiach/adaptive-threshold-estimation/actions/workflows/checks.yml). Historical logs retain the terminology and checkpoints used when each result was produced.
