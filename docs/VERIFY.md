# Full verification commands

Choose the checks for the area you changed, then follow the setup below.
Commands run from the repository root unless a block explicitly changes directory.
The [tool index](../tools/README.md) explains script families and output behavior;
the [evidence index](../results/README.md) explains published checkpoints.

## Choose checks by task

| Task | Commands or command guide | Output and scope |
|---|---|---|
| Navigation or ordinary documentation | `git -c core.whitespace=cr-at-eol diff --check`; `python tools/freeze.py --verify`; check relative links and heading anchors | No proof rebuild needed when sources, specifications, tools, and dependencies are unchanged. This file and some others use CRLF line endings, which plain `--check` reports as trailing whitespace. `freeze.py --verify` covers only `FROZEN.sha256`; run the matching verifier for any other locked path. Inspect the final diff for unintended files. |
| Python toolkit | `python -m pip install -e ./toolkit`; `python -m unittest discover -s toolkit/tests -v`; `python toolkit/examples/quickstart.py`; `python toolkit/examples/rare_events.py` | Python implementation tests and examples; do not certify the implementation in Lean. |
| Consolidated v6 manuscript | `python tools/build_v6.py --check`; `python -m unittest discover -s tools -p 'test_build_v6.py' -v` | Checks inherited source identities, the merge of the shared rare-event appendices, assembly, references, and citations. The [manuscript workflow](../.github/workflows/manuscript.yml) compiles the PDF; [build and visually review](../paper/v6/README.md#reproduce) it when typeset content changes. |
| Consolidated v5 manuscript | `python tools/build_v5.py --check`; `python -m unittest discover -s tools -p 'test_build_v5.py' -v` | Checks inherited source identities, assembly, references, and citations. [Build and visually review](../paper/v5/README.md#reproduce) the PDF when typeset content changes. |
| Critical review packet | `python tools/build_critical_review.py --check` | Compares generated source to the locked proof and editable brief. [Compile and review](../paper/critical-review/README.md) changed typeset content separately. |
| General-law rare-event manuscript (v2) | `python tools/verify_rare_event_manuscript.py` | Hashes and finite checks in a temporary copy; preserves the payload. Does not formally verify the general theorems. |
| Finite-gap rare-event manuscript | `cd paper/finite-gap-rare-events && sha256sum -c SHA256SUMS`; for the [revision 2](../paper/finite-gap-rare-events/revision-2/README.md) sources, the same command in `revision-2/`; [build](../paper/finite-gap-rare-events/README.md) in a disposable copy | Checks the source and PDF identity of revision 1 and of revision 2. The closed quantile theorem is a paper proof; no Lean or numerical certificate covers it. |
| Certified-selection research package | The [package replay commands](../research/2026-10-30-certified-selection/README.md#replay) | Unit tests, exact polynomial identities and exact rational certificates, written to `.runtime/certified-selection/` and compared byte for byte with the tracked evidence. They check finite computations, not the paper proofs; `--write-evidence` rewrites the tracked files. |
| Imported inputs and research packages | `python tools/verify_inputs.py`; `python tools/verify_research.py`; `python tools/verify_population_research.py` | Input identities and maintained research replay. Research diagnostics use temporary output and `.runtime/`; original records remain intact. |
| Main RMS law | `python tools/verify_tier6.py --sequential --require-complete`; `python tools/verify_blind_upper_components.py --sequential` | Exact formal audits of both directions. Tier 6 writes tracked `results/`; use a disposable checkout. The upper audit writes `.runtime/`. |
| Another Lean result | [Theorem-to-audit map](../lean/README.md#main-theorem-entry-points), [baseline and tier sequence](#lean-kernel-checks) | Run the affected result's exact-target/axiom audit, including affected downstream results when shared dependencies change. Check locks first. |
| Verification logic or registration | Relevant audit plus its matching `test_*.py` module; `python -m unittest discover -s tools -p 'test_*.py' -v` for all guard tests | Tests exercise validation guards; they do not replace the mathematical kernel audits. Use a disposable checkout for audits that overwrite published files. |
| Numerical checks and recorded benchmarks | [Integrity and numerical sequence](#integrity-numerics-and-unit-tests), [benchmark protocol](../benchmark/README.md) | Some commands write `results/`. Replaying stored samples is distinct from rerunning held-out experiments. |

For complete integration coverage and ordering, follow
[checks.yml](../.github/workflows/checks.yml) and the separate
[toolkit workflow](../.github/workflows/toolkit.yml). Run only the relevant checks
for a focused local change; report exactly what ran. The detailed sections below
retain the scope and limitations of each audit.

## Setup

Use Python 3.12 for research checks. Toolkit-only work supports Python 3.10 or
newer and uses the installation command in the table. Lean audits additionally
need `elan` on `PATH`; the repository pins the
[Lean toolchain](../lean/lean-toolchain) and
[Mathlib revision](../lean/lake-manifest.json). Do not run `lake update` on the
frozen checkout. The [environment notes](../proposals/lean-environment.md) retain
historical Windows installation details; substitute your own tool locations.

Several legacy verifiers write logs and summaries into tracked `results/` files.
Run those in a disposable checkout containing the exact revision or changes
being checked. For a fresh reproduction checkout:

```sh
git clone https://github.com/davidiach/adaptive-threshold-estimation.git
cd adaptive-threshold-estimation
python -m pip install -r requirements.txt
cd lean
lake exe cache get
cd ..
```

If reviewing a branch or commit, check it out before installing dependencies and
fetching the cache. Python-only checks do not need the `cd lean` / Lake steps.
Newer audits use `.runtime/` or temporary directories as listed in the table.
`--sequential` reduces build concurrency where supported; first-time Lean/cache
setup and a full kernel run are substantially heavier than documentation checks.
Keep published evidence unchanged and inspect the working tree after verification.

## General-law rare-event manuscript v2

From the repository root, using the Python standard library:

```sh
python tools/verify_rare_event_manuscript.py
```

This verifies the immutable [v2 payload](../paper/rare-event/v2/MANIFEST.sha256)
and [historical audit records](../paper/rare-event/audit/MANIFEST.sha256), then
runs the certificate and revision verifiers in a temporary copy. It rechecks
33 exact lower certificates, 9 upper policies, 9 stopping decisions, two
perfect-label examples, and rejection of six targeted corruptions. It then
binds each of the nine genie-bracket rows to its lower and upper files. Both
files must pass the payload's exact verifiers and state the row's law, rarity,
budget and cap. The lower must be a verified four-prior genie dual, the
uncapped scope the bracket needs. The stopping decision, ratios and displayed
decimals are recomputed from the verified bounds. Each case's cap search must
follow the generator's cap ladder at both budgets and stop at its first
passing cap. Eight targeted substitutions must be rejected: seven altered file
references, including an upper policy for another instance, a finite-cap lower
and a file outside the checks, and one flipped stopping decision. It also replays the independent revision audit's finite
computations, including the new examples, constants, and genie comparisons.
Published files are unchanged.

The [build record](../paper/rare-event/v2/VERIFICATION.json) covers the delivered
55-page PDF and its visual review; [build instructions](../paper/rare-event/README.md#verify-and-build)
explain reproduction in a disposable copy. The current command verifies source
and PDF identity, not bit-for-bit TeX rebuild reproducibility. These finite
checks do not formally verify the manuscript's general statistical or limit
theorems. See the [claim status](RESULTS.md#general-law-rare-event-characterization)
and [audit qualifications](../paper/rare-event/audit/README.md).

## All-size finite-gap extension

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

## Build behavior of the critical component audits

The critical lower and both upper component verifiers use `lake build`, which
rebuilds stale transitive imports before the kernel and axiom checks. Use
`--sequential` to build one registered module at a time on constrained machines.
The lower audit checks that all 43 statement examples are present exactly once;
its source hashes cover the full local import closure. The upper audits also
check the review-time dependency snapshots in their specification freeze records.
These additions preserve the original frozen statements and published evidence.

The Psi verifier also rebuilds transitive imports with Lake and checks the
review-time dependency snapshot of its variational model and specifications.

## Unbiased-estimation converse

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

## Observable 713 construction

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

## Confidence characterization

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

## Observable rare events above alpha two

The full observable rare-event theorem for alpha > 2 has a separate audit:

```sh
python tools/verify_rare_above_two.py --sequential
python -m unittest discover -s tools -p 'test_rare_above_two.py' -v
```

It checks all 54 registered modules and seven frozen full statements: exact
power-law existence, the observable unbiased single-coin construction, the
supported-law lower bound, uniform upper bound, exact-power minimax rate,
Psi comparison and nonvacuity. The [scope guide](RARE_ABOVE_TWO.md) records
parameter ranges, constants, the original observable model and paper differences.
The [saved audit](../results/rare_above_two_001.json) passed at `637fb4a`,
covering all 322 declaration roots and their transitive axioms.

## Entropy-tail selection functional

The general-law entropy-tail law (v6 Theorem 13.2) has a locked specification
and a partial audit:

```sh
python tools/verify_entropy_tail.py --sequential
python -m unittest discover -s tools -p 'test_entropy_tail.py' -v
```

The [freeze record](../tools/entropy_tail_specification_freeze.json) hashes the
specification and its project dependencies. It fixes eight full target types:

- the two-sided law and its upper and lower halves;
- hard selection;
- the elementary bounds;
- the single-atom and small-budget values;
- nonvacuity.

The audit checks every registered target for its exact type and transitive
axioms. It rejects any declaration that carries an unregistered target's name.
Six targets are proved: the upper half and the five deterministic targets. The
law and its lower half are not, so the status reports
`entropy_tail_law_verified: false`, and `--require-complete` fails. No result
record is published for this partial audit.

The upper half imports the observable upper-bound development of
[#33](https://github.com/davidiach/adaptive-threshold-estimation/pull/33), about
240 modules, so this audit takes much longer than the other theorem audits. CI
runs it in the separate `entropy-tail-upper` job, followed by that
development's own audit:

```sh
python tools/verify_entropy_tail_upper.py --cached-dependencies
python -m unittest discover -s tools -p 'test_entropy_tail_upper.py' -v
python -m unittest discover -s tools -p 'test_entropy_tail_components.py' -v
```

`verify_entropy_tail_upper.py` checks the four targets of the
[quantile-model specification](../lean/ThresholdHC/EntropyTailQuantile/Specification.lean):
the quantile split, $\mathcal K\le Q\le(1+2\sqrt2)\mathcal K$, and the two
upper bounds with constant 33000. It also checks the explicit theorems
`entropy_tail_upper_28000` and `closed_quantile_upper_30001`, and the transitive
axioms of every declaration in the five upper-bound module groups. Without
`--cached-dependencies` it recompiles every local dependency sequentially, which
takes much longer. With the flag it recompiles only the sampling and execution
groups and reuses objects built earlier, so run it after the first audit.
`verify_entropy_tail_components.py` audits the quantile model alone, and
`verify_entropy_tail_assembly.py` an intermediate stage. Their
[lock](../tools/entropy_tail_quantile_specification_freeze.json) records the
rename of #33's namespace and the superseded lock's hashes. All three write
timestamped evidence under `.runtime/`.

## Quantile-selection comparison: scalar Lemma 3

The scalar inequality of Lemma 3 in the
[certified-selection package](../research/2026-10-30-certified-selection/README.md)
has a locked specification and a complete audit:

```sh
python tools/verify_quantile_comparison.py --sequential --require-complete
python -m unittest discover -s tools -p 'test_quantile_comparison.py' -v
```

The [freeze record](../tools/quantile_comparison_specification_freeze.json) hashes
the specification, which imports only Mathlib, and fixes one full target type:
for real $T,v,c\ge0$,
$T+\sqrt{v^2+2Tc+2v\sqrt{Tc}}\le\frac85(\sqrt{T^2+v^2}+c)$. The audit checks
its exact type and transitive axioms and writes its status under
`.runtime/quantile-comparison/`. The comparison
$\mathcal K\le Q\le\frac85\mathcal K$, Lemmas 1–2 and the suffix theorem are not
targets.

## Magnitude-oracle lower bounds

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

## Critical Psi comparison

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

## Critical upper bound

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

## Distribution-blind upper bound

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

## Critical lower bound

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

## Integrated research replay

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

## Above-two paper checkpoint and formal bridge

For the additive 27 October rare-event result and separate-supremum bridge:

```sh
python research/2026-10-27-route-a/check_construction.py
python lean/ThresholdHC/ResearchRouteA/verify.py
```

Both commands rewrite tracked records in their own directories (`construction-checks.json`; `status.json`, `build.log` and `audit.log`), so run them in a disposable checkout; `tools/verify_research.py` replays the first in a temporary copy. The first command checks exact rational finite-prefix experiments and retains unresolved tails; it does not certify the main theorem. The second checks the new locked formal specification, exact types, and all five public roots. See [formal replay details](../research/2026-10-27-route-a/formal-audit.md) for the local Windows environment. The paper's own construction and constants remain a reviewed paper proof; the alpha > 2 rate itself is now proved in Lean by a different construction (see the [scope guide](RARE_ABOVE_TWO.md)). [Baseline replay records](../research/2026-10-27-route-a/BASELINE.md) and the new `acceptance_check.py` keep diagnostics separate from published `results/`; the latter compares against this session's recorded source snapshot.

## Integrity, numerics, and unit tests

```sh
python tools/verify_inputs.py
python tools/verify_experiment_lock.py
python tools/freeze.py --verify
python tools/verify_lean_sources.py
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

The shorter `python -m unittest discover -s tools -p 'test_*.py' -v` runs all validation test modules present in the checkout. Constant scoring without `--accept` evaluates the recorded configurations without changing the best-score ledger. `verify_experiment_lock.py` requires the held-out record to hold exactly the locked selection's cells and recomputes every summary and the accept decision from the stored samples; it does not repeat the held-out experiment. CI runs it with `--strict`, before `verify_real.py` rewrites its locked record with the platform's line endings. `verify_lean_sources.py` scans every project Lean source with the strengthened proof-escape pattern: the frozen Tier 3–6 verifiers also scan unfrozen proof modules, with a pattern that misses `admit`, `#guard_msgs`, metaprogramming entry points such as `elab_rules`, and code hidden from its comment stripper by a string literal, an escaped identifier or the doc-comment opener `/--/`. The strengthened pattern rejects these forms; it is a textual guard, not a Lean parser. The locked `verify_real.py` compares tape copies of the benchmark's stopping state machines with an independent classifier; `verify_production.py` replays the production routines' exact draws across every recorded training and tuning configuration and checks them against the same kind of classifier. Full benchmark resimulation is a separate procedure in [benchmark/README.md](../benchmark/README.md).

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

The [consolidated v6 manuscript](../paper/v6/README.md) is checked with
`python tools/build_v6.py --check` and its assembly tests. These verify the
hash-locked v5, general-law and finite-gap inputs, the generated sources,
unique labels, and resolved references and citations. The tests also show
that the merged appendices keep every line of both rare-event papers'
versions apart from listed replacements. A separate workflow compiles the
PDF in a scratch copy; none of these checks extends the claims verified by Lean.

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
| Observable alpha > 2 rare-event theory (7 targets, 54 modules, 322 declarations) | [rare_above_two_001.json](../results/rare_above_two_001.json) |
| Input preservation | [MANIFEST_SHA256.txt](../inputs/next-phase/MANIFEST_SHA256.txt) |
| Frozen specifications and tools | [FROZEN.sha256](../FROZEN.sha256), [TIER3_FROZEN.sha256](../TIER3_FROZEN.sha256), [TIER4_FROZEN.sha256](../TIER4_FROZEN.sha256) |
| Workflow definition | [checks.yml](../.github/workflows/checks.yml) |

The completed research commit `23988c7` passed [Linux CI](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/40468287646). Later runs are available on the [workflow page](https://github.com/davidiach/adaptive-threshold-estimation/actions/workflows/checks.yml). Historical logs retain the terminology and checkpoints used when each result was produced.
