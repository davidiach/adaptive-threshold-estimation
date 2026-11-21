# Full verification commands

Choose the checks for the area you changed, then follow the setup below.
Commands run from the repository root unless a block explicitly changes directory.
The [tool index](../tools/README.md) explains script families and output behavior;
the [evidence index](../results/README.md) explains published checkpoints.

## Choose checks by task

| Task | Commands or command guide | Output and scope |
|---|---|---|
| Navigation or ordinary documentation | `git -c core.whitespace=cr-at-eol diff --check`; `python tools/verify_locks.py`; check relative links and heading anchors | No proof rebuild needed when sources, specifications, tools, and dependencies are unchanged. This file and some others use CRLF line endings, which plain `--check` reports as trailing whitespace. `verify_locks.py` covers `FROZEN.sha256` (including a deleted line, which `freeze.py --verify` misses), the Tier 3 to Tier 6 locks and the published checksum manifests; run the matching audit for a path in a specification lock. Inspect the final diff for unintended files. |
| Python toolkit | `python -m pip install -e ./toolkit`; `python -m unittest discover -s toolkit/tests -v`; `python toolkit/examples/quickstart.py`; `python toolkit/examples/rare_events.py` | Python implementation tests and examples; do not certify the implementation in Lean. |
| Consolidated v6 manuscript | `python tools/build_v6.py --check`; `python -m unittest discover -s tools -p 'test_build_v6.py' -v`; `python tools/build_status_docs.py --check`; `python tools/check_build_record.py` | Checks inherited source identities, the merge of the shared rare-event appendices, assembly, references, and citations. After changing `paper/v6/status.json`, run `python tools/build_v6.py` and `python tools/build_status_docs.py`, which regenerates the status tables in `README.md` and `docs/RESULTS.md`. `check_build_record.py` confirms that the build the [v6 README](../paper/v6/README.md) links as current still describes its PDF, and warns when the sources have changed since. The [manuscript workflow](../.github/workflows/manuscript.yml) compiles the PDF and keeps the abstract and provenance note on page 1; [build and visually review](../paper/v6/README.md#reproduce) it when typeset content changes. |
| Consolidated v5 manuscript | `python tools/build_v5.py --check`; `python -m unittest discover -s tools -p 'test_build_v5.py' -v` | Checks inherited source identities, assembly, references, and citations. [Build and visually review](../paper/v5/README.md#reproduce) the PDF when typeset content changes. |
| Critical review packet | `python tools/build_critical_review.py --check` | Compares generated source to the locked proof and editable brief. [Compile and review](../paper/critical-review/README.md) changed typeset content separately. |
| General-law rare-event manuscript (v2) | `python tools/verify_rare_event_manuscript.py` | Hashes and finite checks in a temporary copy; preserves the payload. Does not formally verify the general theorems. |
| Finite-gap rare-event manuscript | `cd paper/finite-gap-rare-events && sha256sum -c SHA256SUMS`; for the [revision 2](../paper/finite-gap-rare-events/revision-2/README.md) sources, the same command in `revision-2/`; [build](../paper/finite-gap-rare-events/README.md) in a disposable copy | Checks the source and PDF identity of revision 1 and of revision 2. Run `python tools/verify_finite_quantile.py` for the explicit finite-law bounds and `python tools/verify_closed_quantile.py` for the general-law rate. |
| Certified-selection research package | The [package replay commands](../research/2026-10-30-certified-selection/README.md#replay) | Unit tests, exact polynomial identities and exact rational certificates, written to `.runtime/certified-selection/` and compared byte for byte with the tracked evidence. They check finite computations, not the paper proofs; `--write-evidence` rewrites the tracked files. |
| Hard-budget RMS research package | `python -m unittest discover -s toolkit/tests -p 'test_budget_ladders.py' -v`; `python research/2026-10-30-hard-budget-rms/verify.py` | Driver unit tests and exact rational recurrence, schedule and timeout-counterexample audits, written to `.runtime/hard-budget-rms/validation.json`. There are no tracked evidence records to compare with. They check finite computations, not the [paper proof](../research/2026-10-30-hard-budget-rms/NOTE.md). |
| Confidence-transfer research package | `python -m unittest discover -s toolkit/tests -p 'test_confidence*.py' -v`; `python research/2026-10-30-confidence-transfer/verify_transfer.py --output .runtime/confidence-transfer/transfer.json`; `python research/2026-10-30-confidence-transfer/verify_anytime.py` | Driver unit tests; exact rational smoothing, likelihood-factorization and null-work audits; exact error-spending identities and the optional-stopping path count, written to `.runtime/confidence-transfer/`. There are no tracked evidence records to compare with. They check finite computations, not the [paper proof](../research/2026-10-30-confidence-transfer/NOTE.md). |
| Imported inputs and research packages | `python tools/verify_inputs.py`; `python tools/verify_research.py`; `python tools/verify_population_research.py` | Input identities and maintained research replay. Research diagnostics use temporary output and `.runtime/`; original records remain intact. |
| Main RMS law | `python tools/verify_sharp_rms.py --replay`; `python tools/verify_large_budget_rms.py --replay`; `python tools/verify_upper_scale.py --replay`; `python tools/verify_upper_quarter.py --replay`; `python tools/verify_upper_sign.py --replay`; `python tools/verify_upper_disagreement.py --replay`; `python tools/verify_upper_cost.py --replay`; `python tools/verify_upper_mixture.py --replay`; `python tools/verify_upper_moment.py --replay`; `python tools/verify_upper_work.py --replay`; `python tools/verify_upper_constant.py --replay`; `python tools/verify_blind_upper_components.py --sequential`; `python tools/verify_tier6.py --sequential --require-complete` | Exact formal audits of both directions. The first eleven check the sharp lower coefficient $1/6$, the large-budget bracket and the upper coefficients $12$, $13$, $15$, $17$, $19$, $27$, $36$, $45$ and $119$, and write nothing; `verify_blind_upper_components.py` checks the frozen upper coefficient $512$ and writes `.runtime/`; `verify_tier6.py` checks the original frozen lower target with $1/64$ and writes tracked `results/`, so use a disposable checkout. |
| Any Lean source | `python tools/verify_project_axioms.py`; add `--replay-main-theorem` for the kernel replay | Builds every module under `lean/ThresholdHC` and checks the transitive axioms of every constant they declare, every exported instance (named, global, default priority, no new data-carrying instance on a type the project does not define) and the fingerprint of every project definition against `tools/definition_lock.json`. A changed or removed definition fails; a new one fails until `--add-definitions` adds it, which never rewrites an existing entry. Registers no theorem and writes only with `--add-definitions`. It does not check exact statement types; run the affected result's audit as well. |
| Finite-law relative approximation | `python tools/verify_finite_selection_approximation.py`; `python -m unittest discover -s tools -p 'test_finite_selection_approximation.py' -v`; for the two component targets, `python tools/verify_selection_approximation.py` | Checks the 79-file specification/dependency lock, 12 exact statements and 93 transitive reports; writes fresh `.runtime/finite-selection/` evidence. The [scope](FINITE_SELECTION_APPROXIMATION.md) separates mathematical endpoints and extension counts from bit complexity and numerical/Python execution. |
| Another Lean result | [Theorem-to-audit map](../lean/README.md#main-theorem-entry-points), [baseline and tier sequence](#lean-kernel-checks) | Run the affected result's exact-target/axiom audit, including affected downstream results when shared dependencies change. Check locks first. |
| Verification logic or registration | Relevant audit plus its matching `test_*.py` module; `python -m unittest discover -s tools -p 'test_*.py' -v` for all guard tests | Tests exercise validation guards; they do not replace the mathematical kernel audits. Use a disposable checkout for audits that overwrite published files. |
| Numerical checks and recorded benchmarks | [Integrity and numerical sequence](#integrity-numerics-and-unit-tests), [benchmark protocol](../benchmark/README.md) | Some commands write `results/`. Replaying stored samples is distinct from rerunning held-out experiments. |

CI runs on pull requests and on pushes to `main`. In
[checks.yml](../.github/workflows/checks.yml) the `research-evidence` and
`numerical-evidence` jobs always run. The four Lean jobs, `lean-kernel`,
`lean-all-modules`, `entropy-tail-upper` and `stopping-program`, run when
[lean_ci.py](../.github/lean_ci.py) selects them from the changed files, or on
a manual run; a green run on a documentation-only change ran no Lean audit.
On pull requests each Lean job restores the project's compiled modules from
an earlier run of the same job on the branch or on `main`, and Lake rebuilds
every module whose source, imports or toolchain changed. Pushes to `main` and
manual runs build every module from scratch.
Three further workflows cover the [toolkit](../.github/workflows/toolkit.yml),
the [v6 PDF](../.github/workflows/manuscript.yml) and
[experiment persistence](../.github/workflows/experiment-persistence.yml).
For complete integration coverage and ordering, follow those files. Run only the relevant checks
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
and a complete audit:

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
All eight targets are proved, including both halves and the two-sided law.
Run with `--require-complete` to require that full registry. The
[completion record](../results/entropy-tail-complete-20261101/README.md)
covers 15 canonical modules, 92 roots and all eight exact types. The supporting
audit covers 57 modules, 368 roots and 89 exact types:

```sh
python tools/verify_entropy_tail_lower_components.py
python tools/verify_entropy_tail.py --sequential --require-complete
python -m unittest discover -s tools -p 'test_entropy_tail_lower_components.py' -v
```

The lower-component audit rebuilds its entire local dependency closure by
default. Its `--cached-dependencies` mode rebuilds only registered lower
modules and hashes reused local native artifacts. The canonical audit also
offers `--cached-dependencies`: it rebuilds all 15 canonical modules with
the pinned native compiler and hashes reused local artifacts. Before
reusing anything, cached mode runs `lake build --no-build` on the local
modules that the rebuilt modules import, so Lake must confirm from current
sources and its traces that every reused dependency is up to date. Populate
them first with the default Lake build, or pass `--build-dependencies` to let
Lake build missing or stale dependencies. Only compiler outputs (`.olean`,
`.olean.private`, `.olean.server`) are hashed, in sorted order; a leftover
temporary artifact from an interrupted write fails the audit. Generated
audit sources use LF line endings, so their hashes do not depend on the
platform. Both modes check exact types, transitive axioms, and source
stability; cached mode also checks reused artifact stability. `--lake PATH`
selects the Lake executable. Each status file records its `build_mode` and
the dependency check it ran. A successful cached audit is not a full
dependency rebuild. The canonical audit's default Lake mode also reports
`local_dependency_rebuild_performed: false`, because Lake rebuilds only
stale dependencies.

The published completion and closed-quantile records predate these checks.
Their `source_sha256` mappings identify, by hash, the verifier versions that
produced them. Fresh runs add the dependency check, omit Lake `.hash` files
from the artifact list and write LF audit sources, so their command lists
and hashes differ from those records.

The separate universal closed-quantile corollary is checked by:

```sh
python tools/verify_closed_quantile.py
python -m unittest discover -s tools -p 'test_closed_quantile.py' -v
```

Its [record](../results/closed-quantile-law-20261101/README.md) covers two
modules, two declaration roots, and one complete exact target. The target
was introduced alongside its proof, with the previously frozen experiment
and quantile definitions unchanged. The default rebuilds the whole local
closure; `--cached-dependencies` rebuilds the two registered modules and
hashes reused artifacts. Run that mode after the default Lake-mode canonical
entropy-tail audit has built its dependencies, or add `--build-dependencies`.
Run `python tools/verify_entropy_tail_sharp.py` for the sharper general-law
coefficient. Lake builds the new proof, checks its independent statements
and audits transitive axioms. The [evidence](../results/entropy-tail-explicit-20261104/README.md)
binds the pinned native run to its sources and dependency artifacts.

The separate direct finite-law audit runs with `python tools/verify_finite_quantile.py`.
It builds the registered proof modules with Lake, checks the statement fixed at
`5557334`, and validates the exact types and transitive axioms. The exact types
are the seven `example` declarations of `FiniteQuantile/Audit.lean`; the audit
pins that file by hash and fails if they are missing. It rejects imports
of the completed general statistical lower theorem. The [finite-law record](../results/direct-finite-quantile-20261104/README.md)
gives the local verification scope and the exact coefficients.

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
`verify_entropy_tail_assembly.py` an intermediate stage. CI does not run
these two. Their
[lock](../tools/entropy_tail_quantile_specification_freeze.json) records the
rename of #33's namespace and the superseded lock's hashes. All three write
timestamped evidence under `.runtime/`.

## Stopping program, identification and genie certificates

The StoppingProgram, CapIdentification and Genie modules come from
[#33](https://github.com/davidiach/adaptive-threshold-estimation/pull/33). Each
of the sixteen audits checks its exact statements, rejects proof escapes and
reports the transitive axioms of every declaration it covers:

| Audit | Scope |
|---|---|
| `verify_stopping_components.py` | Four-prior value identity, positive finite-ratio dual attainment, full fixed-cap identification |
| `verify_stopping_flow_mixture.py` | Count-flow conservation, Bellman potential bounds, finite decision-table mixtures, bounded observable calls |
| `verify_finite_stopping_program.py` | Finite cone, cutoff and excess representation for finitely supported laws |
| `verify_rarity_support.py` | Rarity-support minimum and fractional cutoff optimizer |
| `verify_stopping_dual.py` | `AttainedDualStatement` |
| `verify_information_bellman.py` | Bellman attainment of the information/work ratio and its unique price zero |
| `verify_reference_absorption.py` | Program value between the midpoint modulus and three times it |
| `verify_ordered_information.py` | Count-flow aggregation of seeded, order-dependent capped procedures; Hellinger bounds |
| `verify_adaptive_information.py` | Affinity testing and transfer to the adaptive population experiment |
| `verify_stopping_program_upper.py` | `ProgramUpperStatement`: observable realization of certificates, $R\le P_N$ |
| `verify_finite_risk_certificate.py` | `FiniteCertificateStatement`: $R\le P_N\le16R$ at the prescribed cap |
| `verify_infinite_cap_dual.py` | Infinite-cap attained dual, factor-three and factor-eight comparisons, cap limits |
| `verify_genie_brackets.py` | Latent-reveal brackets and exact Bellman certificates |
| `verify_genie_convergence.py` | Residual and optimized genie convergence, risk brackets, finite termination |
| `verify_genie_conic.py` | Direct squared-risk certificate and the finite-atom SOCP |
| `verify_genie_counterexample.py` | The uniform-gap infinite-divergence counterexample |

Each has a guard-test file of the same name with a `test_` prefix. By default
an audit recompiles every local dependency sequentially; `--cached-dependencies`
recompiles only its own new modules and uses objects built earlier.
`verify_stopping_components.py` also accepts `--audit-only`. CI's
`stopping-program` job builds the eight top-level modules with `lake` and then
runs all sixteen audits with `--cached-dependencies`:

```sh
cd lean && lake build ThresholdHC.StoppingProgram.BellmanTheorem ThresholdHC.StoppingProgram.FiniteCertificate ThresholdHC.CapIdentification.FiniteSeparation ThresholdHC.CapIdentification.Full ThresholdHC.Genie.AtomConicRealization ThresholdHC.Genie.DirectRisk ThresholdHC.Genie.InfiniteDivergenceExample ThresholdHC.Genie.OptimizedConvergence && cd ..
python tools/verify_finite_risk_certificate.py --cached-dependencies
python -m unittest discover -s tools -p 'test_stopping_program_lock.py' -v
```

The [specification lock](../tools/stopping_program_specification_freeze.json)
hashes `StoppingProgram/Specification.lean` and its 35 project dependencies.
The three audits of its targets check it first. Each audit writes
timestamped evidence under `.runtime/`, and none of them certifies the
entropy-tail lower bound.

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

## Hard-budget RMS

Run `python tools/verify_hard_budget.py`. It checks the advance statement
digest, the actual observable controller and the ordinary, critical and
known-law minimax applications. [Native inputs and exact statements](../results/hard-budget-rms-20261104/README.md)

## Critical confidence and finite-cap rates

Run `python tools/verify_critical_confidence.py` to check the fixed quadratic
law, the local pair and the expected-budget minimax confidence lower bound.
[Exact statements and compiler output](../results/critical-confidence-20261104/README.md)

Run `python tools/verify_genie_rate.py` for the uniform cap theorem, its
relative-error bound and the factor-sixteen risk certificate. The separate
`python tools/verify_finite_cap_rate.py` replay checks 576 exact Bellman
comparisons. [Cap theorem and compiler output](../results/genie-rate-20261104/README.md)

Run `python tools/verify_finite_cap_truncation.py` for the sharper
square-root rate of the ordinary program and its minimax-risk consequence.
The [native record](../results/finite-cap-truncation-20261105/README.md)
checks ten exact statements: the output-preserving flow, work and bias
bounds, feasible certificate, optimized value and risk corollaries.
This is not a square-root rate for the genie lower program.

## Sharper quantile factor

Run `python tools/verify_quantile_price_upper.py` for the original arbitrary-law
comparison $K\le Q\le(31/20)K$ and the $16/9$ separated-cost bound. The audit
includes the earlier $8/5$ endpoints after sharing their pointwise reduction.
[Six exact statements and 31 axiom reports](../results/quantile-price-20261104/README.md)
`python tools/verify_quantile_price_bounds.py` replays, in exact rational
arithmetic, the inequalities of that comparison and of its lower example;
CI runs it in `research-evidence`.

Run `python tools/verify_optimal_quantile_factor.py` for the strict rational
bracket of width $10^{-12}$ around the sharp factor. The reduction to the
scalar root and finite-law sharpness are Lean-checked; see the
[quantile-optimality record](../results/quantile-optimality-20261105/README.md).
The rational bracket itself is an exact-arithmetic certificate, not a Lean proof.

## Full quantile-selection comparison

```sh
python tools/verify_quantile_selection.py
```

The [specification](../lean/ThresholdHC/QuantileSelection/Specification.lean)
fixes Lemma 1 with both entropy interaction coefficients, the factor-two
scale-separated estimate of Lemma 2 and Theorem 4 with its tail floor and
saturation clause. The verifier builds the [full proof](../lean/ThresholdHC/QuantileSelection/Full.lean),
checks the three exact types and the comparison for the statistical selection
functional, and inspects the transitive axioms of every new declaration. The
[verification record](../results/quantile-selection-20261104/README.md) identifies
the compiler, rebuilt modules and reused inputs.

## Finite-menu cost grouping

`python tools/verify_band_cost_selection.py` checks 14 independently stated
types and their transitive axioms. It covers feasible compression, recursive
optimality, state and transition bounds, the entropy price, exact saving
comparisons and interval certificates.

The [native record](../results/band-cost-formal-20261105/README.md) binds six
fresh modules with empty logs and one unchanged, previously hash-checked
dependency. A further `python tools/verify_gap_law_menus.py` audit checks 13
exact theorem types and transitive axiom reports for concrete menu coverage,
disjointness, the original prefix-supremum entropy, tail savings, equality of
the optimized value with $K$, and the atomic weight formulas.
Its [native record](../results/gap-law-menus-20261105/README.md) binds all 64 project
sources, five fresh empty compiler logs and 59 previously published dependencies.
Python execution remains outside the formal proofs.

## Finite-law bandwise-suffix theorem

```sh
python tools/verify_bandwise_suffix.py
```

The [specification](../lean/ThresholdHC/BandwiseSuffix/Specification.lean)
requires a hard restriction on the support that minimizes the uncapped
objective over every submeasure and gives the capped value $K$. The verifier
checks finite hard attainment, strict improvement from an inversion, Theorem 5,
the bound on the size of the suffix family and the existence of a minimizer
in that family. It checks the transitive axioms of every new declaration.
The [native record](../results/bandwise-suffix-20261104/README.md) lists the
rebuilt modules, cached inputs and kernel reports.

## Observable population confidence transfer

Run `python tools/verify_confidence_population.py`. The kernel checks the
exact hybrid identity, the single-type $16/3$ information bound for finite
decision trees and full randomized observable prefixes, its extension to
stopped tapes, and confidence testing and minimax conclusions. The $1/128$
lower bound assumes the note’s quantitative common-pair statement. The
[verification record](../results/confidence-population-20261104/README.md)
pins the proof, reused project artifacts and newly compiled modules.

## Quarter smoothing for arbitrary laws

Run `python tools/verify_quarter_smoothing.py`. It checks the locked
statement and an expanded version with both mixtures written explicitly.
The [isolated build](../results/quarter-smoothing-20261104/README.md) checks
five transitive axiom reports. The statistical application to an adaptive
population requires additional work beyond this inequality.

## Selection stability and finite approximation

Run `python tools/verify_selection_stability.py` from the repository root.
The audit checks total-variation stability using half of Mathlib’s variation
distance, both rounding inequalities, the transported interval, its $5Q/8$
specialization and existence of finite approximations for every positive
tolerance and distortion above one. The [native record](../results/selection-stability-20261104/README.md)
lists the five exact statements, 18 transitive axiom reports and reused inputs.

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
above. CI runs this replay on every pull request and push to `main`, and
checks the five locked Route A Lean roots in `lean-kernel` after the complete
Tier 6 audit. These replay checks do
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
python tools/verify_locks.py
python tools/verify_lean_sources.py
python tools/check_targets_numeric.py
python tools/check_targets2_numeric.py
python -m unittest discover -s tools -p 'test_*.py' -v
mkdir -p .runtime/drift && touch .runtime/drift/start && sleep 1
python tools/check_power_bracket.py
python proposals/constants/bias_audit.py
python proposals/constants/uniform_constant_checks.py
python constants/score_constants.py constants/candidate.json
cp results/constants_last.json .runtime/drift/constants_candidate.json
python constants/score_constants.py constants/candidate_theory.json
cp results/constants_last.json .runtime/drift/constants_candidate_theory.json
python constants/score_constants.py constants/candidate_finite_grid.json
python benchmark/verify_real.py
python benchmark/verify_production.py
python tools/check_results_drift.py --rewritten-since .runtime/drift/start --extra .runtime/drift/constants_candidate.json=results/constants_theory.json --extra .runtime/drift/constants_candidate_theory.json=results/constants_theory.json
```

The shorter `python -m unittest discover -s tools -p 'test_*.py' -v` runs all validation test modules present in the checkout. Constant scoring without `--accept` evaluates the recorded configurations without changing the best-score ledger. Each run overwrites `results/constants_last.json`, so the candidates run in CI's order, which scores `candidate_finite_grid.json` last as in the committed record. `check_results_drift.py` then compares the five records these commands rewrite in place, and the kept copies of the first two constants runs, with the committed versions, ignoring line endings, wall-clock fields and last-digit float noise; a difference means a replay changed a published result. With `--rewritten-since` every record must also be newer than the marker, so a check that stopped writing its record fails instead of leaving the committed bytes in place. CI creates the marker at the start of its numerical job, before the first rewriting check. `verify_experiment_lock.py` requires the held-out record to hold exactly the locked selection's cells and recomputes every summary and the accept decision from the stored samples; it does not repeat the held-out experiment. CI runs it with `--strict`, before `verify_real.py` rewrites its locked record with the platform's line endings. `verify_lean_sources.py` scans every project Lean source with the strengthened proof-escape pattern: the frozen Tier 3–6 verifiers also scan unfrozen proof modules, with a pattern that misses `admit`, `#guard_msgs`, metaprogramming entry points such as `elab_rules`, and code hidden from its comment stripper by a string literal, an escaped identifier or the doc-comment opener `/--/`. The strengthened pattern rejects these forms; it is a textual guard, not a Lean parser. The locked `verify_real.py` compares tape copies of the benchmark's stopping state machines with an independent classifier; `verify_production.py` replays the production routines' exact draws across every recorded training and tuning configuration and checks them against the same kind of classifier. Full benchmark resimulation is a separate procedure in [benchmark/README.md](../benchmark/README.md).

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

A passing audit shows only that the exact Lean type is proved. The
[model-fidelity brief](MODEL_FIDELITY.md) compares the central Lean
definitions with the paper's model and lists what the audits do not cover.

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
| Frozen specifications and tools | [FROZEN.sha256](../FROZEN.sha256), [TIER3_FROZEN.sha256](../TIER3_FROZEN.sha256), [TIER4_FROZEN.sha256](../TIER4_FROZEN.sha256), [TIER5_FROZEN.sha256](../TIER5_FROZEN.sha256), [TIER6_FROZEN.sha256](../TIER6_FROZEN.sha256) |
| Workflow definition | [checks.yml](../.github/workflows/checks.yml) |

The completed research commit `23988c7` passed [Linux CI](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/40468287646). Later runs are available on the [workflow page](https://github.com/davidiach/adaptive-threshold-estimation/actions/workflows/checks.yml). Historical logs retain the terminology and checkpoints used when each result was produced.

## Fixed confidence for every known gap law

Run `python tools/verify_stopping_confidence.py` and
`python tools/verify_confidence_amplification.py` with the pinned Lean
toolchain. These audits check the actual reference work, effective-budget
lower bound, pathwise cap and the two minimax rates.
[Exact statements and native logs](../results/known-law-confidence-20261104/README.md)

## Stochastic-envelope corollary

Run `python tools/verify_stochastic_envelope.py` for the two minimax rates,
the unbiased existence equivalence and the variance–work product in the
unknown-law class. [Native record](../results/stochastic-envelope-20261105/README.md)

## Arbitrary-law Psi lower bound

Run `python tools/verify_psi_selection.py` for six exact statements and ten
transitive axiom reports: the comparison $\Psi(B^{-1/2})\le\mathcal K(B)$ and
the two minimax lower bounds with coefficient $10^{-17}$ that follow from the
entropy-tail law. Every declaration in `PsiSelection/` is an audit root.
[Native record](../results/psi-selection-20261109/README.md)

## Closed form of Psi

Run `python tools/verify_psi_closed_form.py` for six exact statements and 36
transitive axiom reports: the comparisons $\mathcal K^0\le\mathcal K$,
$\mathcal Q^0\le\mathcal Q$ and $\mathcal K^0\le\mathcal Q^0$, the chain
$\mathcal Q^0\le\sqrt2\,\Psi$, $\Psi\le\mathcal K^0\le\mathcal Q^0$, and
$\Psi=\mathcal Q^0=\rho$ when the resolution is at least the quantile
threshold. The restatements write out the entropy-free functionals. Every
declaration in `PsiClosedForm/` is an audit root. The two-atom sharpness
example and the rest of v6 §14.8 are outside this audit.
[Native record](../results/psi-closed-form-20261116/README.md)

## Distance of Psi from the rate

Run `python tools/verify_psi_gap.py` for eight exact statements and 18
transitive axiom reports: the decomposition $\Gamma_\kappa=A_\kappa(1+E_\kappa)$
of the quantile core with $0\le E_\kappa\le\log\log_2(1/t)$, the chain
$\Psi\le\mathcal K\le\mathcal Q\le\sqrt{1+E_\kappa}\,\mathcal Q^0$ and
$\mathcal Q\le\sqrt{2(1+E_\kappa)}\,\Psi$, the risk bounds with
coefficients $10^{-17}$ and $30001\sqrt{2(1+E_\kappa)}$, and the reverse
bound under its two conditions. The restatements write out the core cost and
the core entropy. Every declaration in `PsiGap/` is an audit root. The bound
by the number of occupied bands and the power-law statements of v6 §14.8 are
outside this audit.
[Native record](../results/psi-gap-20261116/README.md)

## Psi sharpness and power-law foundation

Run `python tools/verify_psi_sharpness.py` for five exact statements and
15 transitive axiom reports: the two-atom equality, a concrete sharpness
instance and the entropy bound by the finite positive occupied-band count.
[Record](../results/psi-sharpness-20261116/README.md).

Run `python tools/verify_power_window.py` for 16 exact statements and
78 transitive axiom reports. It checks all five frozen power-window targets:
the Phi formula, actual core cost and uniform entropy bounds, deterministic
quantile comparison, RMS bounds and both confidence bounds. This includes
exponent two and arbitrary scale. Independent restatements retain every
assumption and the explicit constants. Corollary 14.14 and Remark 14.15
are outside this audit; the next one checks them. [Record](../results/power-window-complete-20261116/README.md).

Run `python tools/verify_critical_window.py --replay` for 17 exact statements
and 55 transitive axiom reports over the five modules of
`lean/ThresholdHC/CriticalWindow`. It checks Corollary 14.14 and Remark 14.15
on top of the power-window targets: the window rate within the factor $5.13$
for $3/2\le\alpha\le3$, display (W9) with the paper's constants $10^{-18}$ and
$3.4\cdot10^5$, the bounds on $\Psi$, the ratio of the risk to $\Psi$, the
quadratic law against the critical rate, and the regimes away from and near
exponent two, with the near-two risk. With `--replay` the five modules also
go through the independent kernel checker. Its 11-test guard suite is
`test_critical_window.py`. [Record](../results/critical-window-20261120/README.md).

Run `python tools/verify_paper_corollaries.py --replay` for 5 exact statements
and 11 transitive axiom reports over the four modules of
`lean/ThresholdHC/PaperCorollaries`: the RMS constants $1/6$ and $12$ under a
stochastic envelope, the coefficient $1/6$ under a pathwise cap, and the
paper's divergence sequence for $\Psi$ at the quadratic law. Its 11-test guard
suite is `test_paper_corollaries.py`. [Record](../results/paper-corollaries-20261120/README.md).

Run `python tools/verify_paper_statements.py --replay` for 20 exact statements
and 63 transitive axiom reports over the six modules of
`lean/ThresholdHC/PaperStatements`: the critical theorem with the explicit
constants $10^{-18}$ and $100000$, the arithmetic of the slow-divergence remark
and the $\Psi$ sequence in the critical model, the unbiased coefficient $1/16$
attained at every fixed gap, the endpoint case of `prop:bounded`, the known
point-mass constant $1/2$, the 713 second moment, $c_*>1.462554551279$ and
selection stability with $20Q/31$ and $Q/c_*$. Its 11-test guard suite is
`test_paper_statements.py`. [Record](../results/paper-statements-20261120/README.md).

Run `python tools/verify_pilot_feedback.py --replay` for 14 exact statements
and 126 transitive axiom reports over the 18 modules of
`lean/ThresholdHC/PilotFeedback`, promoted from the pilot-feedback and
scheduled-update research packages: the precommitted and one-update lower
bounds $0.18735887$ and $0.186960371$ at gap $1/5$ with budget $25$, in RMS
form, and their separations from the adaptive witness. The replay re-evaluates
the integer certificates (about six minutes). Its 11-test guard suite is
`test_pilot_feedback.py`. [Record](../results/pilot-feedback-20261120/README.md).

Run `python tools/verify_explicit_constants.py --replay` for 5 exact statements
and 10 transitive axiom reports over the two modules of
`lean/ThresholdHC/ExplicitConstants`: the hidden-model confidence coefficient
$15/(256\sqrt2)$ for each algorithm and the minimax radius, the rare-event
lower coefficient $1/256$ and the single-coin second moment $28\rho$, which the
frozen statements leave existential or state only per algorithm. Its 11-test
guard suite is `test_explicit_constants.py`. [Record](../results/explicit-constants-20261121/README.md).

Run `python tools/verify_nonnegative_unbiased.py --replay` for 4 exact
statements and 14 transitive axiom reports over the three modules of
`lean/ThresholdHC/NonnegativeUnbiased`: Proposition `prop:bounded`, first
sentence, with the support comparison, the empty tail after stopping and tape
recovery. Its 11-test guard suite is `test_nonnegative_unbiased.py`.
[Record](../results/nonnegative-unbiased-20261121/README.md).

Run `python tools/verify_finite_gap_corollaries.py --replay` for 6 exact
statements and 15 transitive axiom reports over the three modules of
`lean/ThresholdHC/FiniteGapCorollaries`: Corollary `cor:one-gap` of the
finite-gap manuscript, with the entropy–tail constants $10^{-17}$ and $28000$,
and both displays of Corollary `cor:mse`, with $c_0=10^{-20}$ and $C_0=30001$.
Its 11-test guard suite is `test_finite_gap_corollaries.py`.
[Record](../results/finite-gap-corollaries-20261121/README.md).

Run `python tools/verify_stopped_time_uniform.py --replay` for 6 exact
statements and 12 transitive axiom reports over the three modules of
`lean/ThresholdHC/StoppedTimeUniform`: the fixed-budget coefficient $10^{-17}$
for estimates from the seed and the first $n$ observations, its consequence
for time-uniform interval envelopes, and display (TU1) with $10^{-22}$ at every
$n\ge2$ with $\log\log n\le(10^{10}-1)\log(1/\delta)$. Its 11-test guard
suite is `test_stopped_time_uniform.py`.
[Record](../results/stopped-time-uniform-20261121/README.md).

Run `python tools/verify_latent_threshold.py --replay` for 2 exact statements
and 4 transitive axiom reports over the three modules of
`lean/ThresholdHC/LatentThreshold`: $\theta=G_{\mu,q}(P>1/2)$ for every gap
law and sign law. Its 11-test guard suite is `test_latent_threshold.py`.
[Record](../results/latent-threshold-20261121/README.md).

Run `python tools/verify_zero_atom_split.py --replay` for 5 exact statements
and 11 transitive axiom reports over the three modules of
`lean/ThresholdHC/ZeroAtomSplit`: the identity
$K_\alpha=\min\{\rho,z+(1-z)K_{\eta,\rho/(1-z)}\}$ and its arbitrary-law form.
Its 11-test guard suite is `test_zero_atom_split.py`.
[Record](../results/zero-atom-split-20261121/README.md).

Run `python tools/verify_program_factor.py --replay` for 7 exact statements and
37 transitive axiom reports over the five modules of
`lean/ThresholdHC/ProgramFactor`: $R\le P_\infty\le(3\sqrt7/2)R$, the
finite-cap factor $3\sqrt7$ for $N\ge4B/9$, the genie test and $3\sqrt7R<8R$.
CI runs it in the `stopping-program` job. Its 11-test guard suite is
`test_program_factor.py`.
[Record](../results/program-factor-20261121/README.md).

Run `python tools/verify_cap_identification_estimate.py --replay` for 4 exact
statements and 13 transitive axiom reports over the three modules of
`lean/ThresholdHC/CapIdentificationEstimate`: the explicit estimate
$\Delta_N/2\ge\rho\|h\|_2^2/(4\|h\|_\infty)$ after the fixed-cap
identification theorem. CI runs it in the `stopping-program` job. Its 11-test
guard suite is `test_cap_identification_estimate.py`.
[Record](../results/cap-identification-estimate-20261121/README.md).

Run `python tools/verify_psi_null.py --replay` for 6 exact statements and 29
transitive axiom reports over the six modules of `lean/ThresholdHC/PsiNull`:
Proposition `prop:psi-null`, the null-work obstruction
$\mathfrak J_0(b)\ge(\Psi(h)-4b)_+^2/(192h^2)$ for every gap law, and its
corollary $R\ge\Psi(B^{-1/2})/8192$. CI runs it in the `entropy-tail-upper`
job. Its 11-test guard suite is `test_psi_null.py`.
[Record](../results/psi-null-20261121/README.md).

Run `python tools/verify_confidence_transfer_steps.py --replay` for 6 exact
statements and 14 transitive axiom reports over the four modules of
`lean/ThresholdHC/ConfidenceTransferSteps`: equation (17) of the
confidence-transfer note, $r^{\rm exp}\ge\Psi(\sqrt{\log(1/\delta)/B})/8192$ for
every gap law, and its equation (22), the exact-power-law confidence rate
above two under both budget conventions. CI runs it in the
`entropy-tail-upper` job. Its 11-test guard suite is
`test_confidence_transfer_steps.py`.
[Record](../results/confidence-transfer-steps-20261121/README.md).

Run `python tools/verify_bias_subtraction.py --replay` for 5 exact statements
and 24 transitive axiom reports over the three modules of
`lean/ThresholdHC/BiasSubtraction`: the remark after Proposition
`prop:psi-null` that the bias term $4b$ cannot be lowered. Its 11-test guard
suite is `test_bias_subtraction.py`.
[Record](../results/bias-subtraction-20261121/README.md).

Run `python tools/verify_critical_pair_rms.py --replay` for 2 exact statements
and 4 transitive axiom reports over the two modules of
`lean/ThresholdHC/CriticalPairRMS`: the critical common pair composed with the
RMS transfer, with an existential constant. Its 11-test guard suite is
`test_critical_pair_rms.py`.
[Record](../results/critical-pair-rms-20261121/README.md).

Run `python tools/verify_restricted_rms.py --replay` for 7 exact statements and
16 transitive axiom reports over the three modules of
`lean/ThresholdHC/RestrictedRMS`: the coefficient $1/6$ for budgets through
four, for both oracles there, for three flips per coin and, conditionally,
for any class containing the four-fresh-flip protocols. CI runs it in the
`lean-kernel` job. Its 11-test guard suite is `test_restricted_rms.py`.
[Record](../results/restricted-rms-20261121/README.md).

Run `python tools/verify_sharp_strict.py --replay` for 9 exact statements and
29 transitive axiom reports over the three modules of
`lean/ThresholdHC/SharpStrict`: the bound $\omega/6$ is strict for every gap
law and every $B\ge1$ other than four, also under both oracles. CI runs it in
the `lean-kernel` job. Its 11-test guard suite is `test_sharp_strict.py`.
[Record](../results/sharp-strict-20261121/README.md).

Run `python tools/verify_global_cut.py --replay` for 6 exact statements and 25
transitive axiom reports over the three modules of `lean/ThresholdHC/GlobalCut`:
Corollary 6 of the certified-selection note, $\mathcal K\le V\le Q\le\frac85\mathcal K$
for the best global upper-gap cut, its top-$k$ form on finite laws and its
non-exactness. Its 11-test guard suite is `test_global_cut.py`.
[Record](../results/global-cut-20261121/README.md).

Run `python tools/verify_entropy_tail_forms.py --replay` for 10 exact
statements and 37 transitive axiom reports over the four modules of
`lean/ThresholdHC/EntropyTailForms`: the selection and three-piece forms of
Theorem 13.2, their equality before and after the cap, the law with
$0<c<C$, hard measurable partitions and a hard minimizer on finite laws. CI
runs it in the `entropy-tail-upper` job. Its 11-test guard suite is
`test_entropy_tail_forms.py`.
[Record](../results/entropy-tail-forms-20261121/README.md).

Run `python tools/verify_noninterval_selection.py --replay` for 8 exact
statements and 59 transitive axiom reports over the five modules of
`lean/ThresholdHC/NonintervalSelection`: the noninterval optimal assignment of
the rare-event discussion, with eight kernel-checked interval certificates for
the paper's table. CI runs it in the `entropy-tail-upper` job. Its 11-test
guard suite is `test_noninterval_selection.py`.
[Record](../results/noninterval-selection-20261121/README.md).

Run `python tools/verify_oracle_upper.py --replay` for 6 exact statements and
97 transitive axiom reports over the seven modules of
`lean/ThresholdHC/OracleUpper`: both magnitude-oracle minimax risks are at most
$\omega_\mu(B^{-1/2})/2$, so $1/2$ is exactly the best oracle coefficient. CI
runs it in the `lean-kernel` job. Its 11-test guard suite is
`test_oracle_upper.py`.
[Record](../results/oracle-upper-20261121/README.md).

Run `python tools/verify_oracle_sharpness.py --replay` for 4 exact statements
and 9 transitive axiom reports over the five modules of
`lean/ThresholdHC/OracleSharpness`: no magnitude-oracle upper coefficient below
$1/2$, since point masses at small gaps have oracle risk near $1/2$. CI runs it
in the `lean-kernel` job. Its 11-test guard suite is `test_oracle_sharpness.py`.
[Record](../results/oracle-sharpness-20261121/README.md).

Run `python tools/verify_clipping_boundary.py --replay` for 8 exact statements
and 55 transitive axiom reports over the seven modules of
`lean/ThresholdHC/ClippingBoundary`: the bounded-kurtosis transfer of the
variance to the clipped risk, its uniform corollary, and the seed-noise
counterexample. CI runs it in the `entropy-tail-upper` job. Its 11-test guard
suite is `test_clipping_boundary.py`.
[Record](../results/clipping-boundary-20261121/README.md).

Run `python tools/verify_fixed_plan.py --replay` for 14 exact statements and 85
transitive axiom reports over the six modules of `lean/ThresholdHC/FixedPlan`:
the toolkit's fixed majority plan, its exact work, bias, variance and RMS
bounds, and the closed form of $e_m$ for uniform rates. CI runs it in the
`entropy-tail-upper` job. Its 11-test guard suite is `test_fixed_plan.py`.
[Record](../results/fixed-plan-20261121/README.md).

Each audit pins its new specification, restates the checked targets and
reports every new declaration's transitive axioms. Their six-test guard
suites are `test_psi_sharpness.py` and `test_power_window.py`; CI runs both
suites and both audits, and also the critical-window, paper-corollary,
paper-statement, pilot-feedback, explicit-constant, nonnegativity,
finite-gap corollary, stopped time-uniform, latent-threshold, zero-atom
split, critical common-pair, bias-subtraction, global-cut, psi-null,
confidence-transfer-steps, entropy-tail-forms, noninterval-selection, fixed-plan and clipping-boundary
suites and audits, the
`lean-kernel` job also the restricted-class, sharp-strictness,
oracle-sharpness, oracle-upper, clipped-output and revisit-upper suites and
audits; the `stopping-program` job also runs the fixed-cap
estimate and program-factor suites and audits. Existing published records retain their original scope.

## Sharp RMS coefficient and square-root cap

Run `python tools/verify_sharp_rms.py --replay` for 38 exact statements and
343 transitive axiom reports over the 54 modules of `lean/ThresholdHC/SharpRMS`.
It checks the sharp RMS lower coefficient $1/6$ for every gap law and every
$B\ge1$, its optimality, the stronger coefficient for $B\ge25$, the reduction
to one gap, and the same bounds under both magnitude oracles. With `--replay`
every module also goes through the independent kernel checker, which
re-evaluates the 140 integer comparisons of the intermediate budgets. Seven
window modules hold those comparisons, so Lake builds them in parallel.
Run `python tools/verify_square_root_cap.py` for the square-root cap
comparison of the optimized stopping programs and its $4B/9$ corollary: two
exact statements and six axiom reports. Both specifications were written
after the proofs and are pinned from these audits onward. The proofs keep
helper lemmas private; those are not audit roots here, and
`verify_project_axioms.py` checks their axioms with every other constant.
The guard suites are `test_sharp_rms.py` and `test_square_root_cap.py`; CI
runs both suites and both audits.
[Record](../results/sharp-rms-20261117/README.md).

Run `python tools/verify_large_budget_rms.py --replay` for the bracket
$[0.175198,0.186752]$ on the best RMS lower coefficient at budgets of at least
25: 25 exact statements and 147 transitive axiom reports over the 28 modules
of `lean/ThresholdHC/LargeBudgetRMS`. It checks the lower coefficient in all
three models, $0.17807955$ for $B\ge100$, the adaptive 25-flip witness at gap
$1/5$ and the upper bound on the coefficient. The modules build on
`SharpRMS`; with `--replay` they also go through the independent kernel
checker. The guard suite is `test_large_budget_rms.py`; CI runs it and the
audit. [Record](../results/large-budget-rms-20261118/README.md).

Run `python tools/verify_revisit_upper.py --replay` for 5 exact statements and
23 transitive axiom reports over the eight modules of
`lean/ThresholdHC/RevisitUpper`: the 20+5 revisit witness with RMS at most
$0.188087$ at the gap $1/5$ under a hard cap of 25 flips. The replay
re-evaluates its integer risk certificate. CI runs it in the `lean-kernel`
job. Its 11-test guard suite is `test_revisit_upper.py`.
[Record](../results/revisit-upper-20261121/README.md).

Run `python tools/verify_upper_constant.py --replay` for the upper constant
$119$ of the RMS law: 7 exact statements and 22 transitive axiom reports over
the 4 modules of `lean/ThresholdHC/UpperConstant`. It checks that the
distribution-blind family of `BlindUpper` has RMS risk at most $119$ times the
modulus at every budget of at least one, the matching minimax bound, and the
sharper call moments behind them. The frozen `BlindUpper` targets with $512$
are unchanged. The guard suite is `test_upper_constant.py`; CI runs it and the
audit. [Record](../results/upper-constant-20261118/README.md).

Run `python tools/verify_upper_work.py --replay` for the upper constant $45$
of the RMS law: 11 exact statements and 36 transitive axiom reports over the 7
modules of `lean/ThresholdHC/UpperWork`. Besides the two targets with $45$, it
restates the sharper per-level work bound and its parts: the offset sum
$49/10$ with the dyadic term written out, the survival sum with the Hoeffding
survival bound written out, the expected work of the early-stopping classifier
for both signs of the coin, the level sum $248/25$, the call cost, the batch
mean-square error $6304/25$ and the batch RMS bound $397/25$. The guard suite
is `test_upper_work.py`; CI runs it and the audit.
[Record](../results/upper-work-20261118/README.md).

Run `python tools/verify_upper_moment.py --replay` for the upper constant $36$
of the RMS law: 10 exact statements and 21 transitive axiom reports over the 6
modules of `lean/ThresholdHC/UpperMoment`. Besides the two targets with $36$, it
restates the sharper call second moment and its parts: the disagreement pair
bound $113/100$ with the error prefactor written out, the squared increment of
the classifier decisions for both signs of the coin, the level sum $72/5$, the
call second moment, the batch mean-square error $19781/125$ and the batch RMS
bound $63/5$. The guard suite is `test_upper_moment.py`; CI runs it and the
audit. [Record](../results/upper-moment-20261118/README.md).

Run `python tools/verify_upper_mixture.py --replay` for the upper constant $27$
of the RMS law: 8 exact statements and 26 transitive axiom reports over the 3
modules of `lean/ThresholdHC/UpperMixture`. Besides the two targets with $27$, it
restates the mixture identities and the budget step: the expected work and the
squared risk of a coin mixture of two estimators with the same seed law, each
the clip-weighted mixture of the two; the modulus scaling
$N\,\omega(N^{-1/2})^2\le B\,\omega(B^{-1/2})^2$ for $0<N\le B$; the batch
mean-square factor $19781/125$; and the uniform budget and risk bound $27$ of
the mixture of levels $L$ and $L+1$. The guard suite is `test_upper_mixture.py`;
CI runs it and the audit. [Record](../results/upper-mixture-20261118/README.md).

Run `python tools/verify_upper_cost.py --replay` for the upper constant $19$
of the RMS law: 13 exact statements and 34 transitive axiom reports over the 7
modules of `lean/ThresholdHC/UpperCost`. Besides the two targets with $19$, it
restates the sharper padded call cost and its parts: the offset bounds $89/20$
and $17/4$ with the survival term written out, the grid sum, the identity that
puts the survival bound of the check `k` of level `k + J` on the grid of scale
$1+J\log2$, the constant $11/2$, the padded level sum, the per-coin and
population padded costs, the batch mean-square factor $401/5$, the budget
mixture for any batch factor, and its risk bound $19$. The guard suite is
`test_upper_cost.py`; CI runs it and the audit.
[Record](../results/upper-cost-20261118/README.md).

Run `python tools/verify_upper_disagreement.py --replay` for the upper constant
$17$ of the RMS law: 14 exact statements and 71 transitive axiom reports over
the 9 modules of `lean/ThresholdHC/UpperDisagreement`. Besides the two targets
with $17$, it restates the sharper call second moment and its parts: the
cap-term offset bound $321/100$ and the cap grid sum with the terms written
out, the telescoping grid bound $(2+\sqrt2)/c$, the early-stopping level sum
$41/100$ with the union-bound terms written out, the per-level disagreement
bound for both signs of the coin, the second-moment and padded-cost level sums
with their regime term, the per-coin second moment and padded cost, the batch
mean-square factor $637/10$, and the risk bound $17$. The guard suite is
`test_upper_disagreement.py`; CI runs it and the audit.
[Record](../results/upper-disagreement-20261119/README.md).

Run `python tools/verify_upper_sign.py --replay` for the upper constant $15$ of
the RMS law: 13 exact statements and 67 transitive axiom reports over the 11
modules of `lean/ThresholdHC/UpperSign`. Besides the two targets with $15$, it
restates the sign-change bound and its use: the bound one half for the success
counts of two halves of the flips, the disagreement bound one half plus the
early-stop bound on the tape, the drift steps, the coefficient $1613/1000$ below
the split, the offset bound $247/100$ with the cap terms written out, the grid
sum, the per-level bound on the tape, the level sum with its regime term, the
per-coin second moment, the batch mean-square factor $999/20$, and the risk
bound $15$. The guard suite is `test_upper_sign.py`; CI runs it and the audit.
[Record](../results/upper-sign-20261119/README.md).

Run `python tools/verify_upper_quarter.py --replay` for the upper constant $13$
of the RMS law: 13 exact statements and 75 transitive axiom reports over the 12
modules of `lean/ThresholdHC/UpperQuarter`. Besides the two targets with $13$, it
restates the vote-change bound and its use: the bound one quarter for the
success counts of two blocks of $n$ flips, the disagreement bound one quarter
plus the early-stop bound on the tape at every level, the drift steps of the
four bands, the coefficients below the split, the band offsets $89/50$ with the
cap terms written out, the grid sum, the per-level bound on the tape, the level
sum with its regime term, the per-coin second moment, the batch mean-square
factor $147/4$, and the risk bound $13$. The guard suite is
`test_upper_quarter.py`; CI runs it and the audit.
[Record](../results/upper-quarter-20261119/README.md).

Run `python tools/verify_upper_scale.py --replay` for the upper constant $12$
of the RMS law: 14 exact statements and 90 transitive axiom reports over the 8
modules of `lean/ThresholdHC/UpperCallCost` and `lean/ThresholdHC/UpperScale`.
Besides the two targets with $12$, it restates the call cost and the
calibration scale: the offset bound $399/100$ for $v\ge307/100$ with the tail
terms written out, the weighted sum of the offsets $26/5$, the padded call cost
alone and with its regime term, the per-coin cost moment, the population cost
bound, the scaled seed mark, the budget $4t\,2^L$ of the scaled machine, its
squared risk as the calibrated mean-square error, the variance times the cost
$169/5$, the mean-square bound at scale $t\,2^L$, and the risk bound $12$. The
guard suite is `test_upper_scale.py`; CI runs it and the audit.
[Record](../results/upper-scale-20261119/README.md).

Run `python tools/verify_clipped_output.py --replay` for 6 exact statements and
19 transitive axiom reports over the three modules of
`lean/ThresholdHC/ClippedOutput`: clipping the output to $[0,1]$ keeps the
budget and cannot raise the RMS risk, and the family with constant $12$ can be
taken $[0,1]$-valued. CI runs it in the `lean-kernel` job. Its 11-test guard
suite is `test_clipped_output.py`.
[Record](../results/clipped-output-20261121/README.md).

## Whole-project build, axioms and kernel replay

Run `python tools/verify_project_axioms.py --replay-main-theorem`. It builds
every module under `lean/ThresholdHC`, including files that no result audit
names, and fails unless no project module declares an axiom and every
constant depends only on `propext`, `Classical.choice` and `Quot.sound`. The
replay runs the toolchain's `leanchecker`, one process per module, on the
import closure of `Tier6/Full.lean` and `BlindUpper/Full.lean`. The audit
catches a `sorry` that the textual source scanner cannot see, for example a
proof closed with the `stop` tactic. It also checks every exported instance
and compares a fingerprint of every project definition, proofs erased, with
`tools/definition_lock.json`; a new definition is added with
`--add-definitions`. It does not check statement types.
CI runs it in the `lean-all-modules` job.
[First record](../results/project-axioms-20261109/README.md) ·
[instances and definition lock](../results/project-definitions-20261114/README.md)

## Rare-event margins below one

Run `python tools/verify_sublinear_power.py` for five exact statements and ten transitive axiom reports. [Native record](../results/sublinear-power-20261105/README.md)

## Logarithmic and intermediate rare margins

Run `python tools/verify_shifted_power.py` for ten exact statements and 35 transitive axiom reports. The finite Poisson controller is checked through the original observable experiment. [Native record](../results/shifted-power-20261105/README.md)

## Observable time-uniform confidence

Run `python tools/verify_anytime_confidence.py` for nine exact statements and 29 transitive axiom reports. Both interval endpoints use the same observed prefix and private seed. [Native record](../results/anytime-confidence-20261105/README.md)

## Smooth-density robustness

Run `python tools/verify_smooth_density.py` for 15 exact statements and 46 transitive axiom reports. The audit covers uniform derivative bounds, the normalized density pair, its original parameter law, both expected-complexity bounds, and unbiased impossibility. [Native record](../results/smooth-density-20261105/README.md)

## Finite-cell observed states

Run `python tools/verify_observed_states.py` for 22 exact statements and 58 transitive axiom reports. The audit covers the finite partition, magnitude envelope, target separation, physical observation law and exact lower bound. [Native record](../results/finite-observed-20261105/README.md)

## Continuous-magnitude observed states

Run `python tools/verify_continuous_observed.py` for 34 exact statements and 87 transitive axiom reports. The audit covers the physical query law, exact uniform gap distribution, normalized density and moments, and both complexity lower bounds. [Native record](../results/continuous-observed-lower-20261105/README.md)

## Fresh-state upper-bound transfer

Run `python tools/verify_observed_upper.py` for 21 exact statements and 42 transitive axiom reports. The audit covers the parameter law, complete transcript, actual work and risk identities, universal modulus upper bounds and uniform-gap complexity. [Native record](../results/observed-state-upper-20261105/README.md)

## Selected-type information transfer

Run `python tools/verify_typed_confidence.py` for 48 exact statements and 48 transitive axiom reports. The audit covers heterogeneous parameter laws, quarter-mixture hybrids, actual local and total work, randomized countable populations, stopped reconstruction and the final $16/3$ null-work transfer. [Native record](../results/adaptive-types-20261105/README.md)

## Common-pair construction

Run `python tools/verify_confidence_localization.py` for 40 exact statements and 40 transitive axiom reports. The audit covers zero-density Hellinger identities, support regularization, the bounded estimator, policy-wise pairs, finite mixtures, simultaneous feasibility and the estimator/minimax confidence coefficient $1/128$. [Native record](../results/common-pair-20261105/README.md)

## Additive confidence localization

Run `python tools/verify_additive_confidence.py` for 41 exact statements and 41 transitive axiom reports. The audit covers overlapping submeasures, clipped Radon–Nikodym priors, positive and negative sign measures, exact parameter and finite-statistic laws, residual mass, weighted original work, and the estimator/minimax coefficient $1/128$. [Native record](../results/additive-confidence-20261105/README.md)

## Sharper general-law confidence coefficient

Run `python tools/verify_confidence_entropy.py` for six exact statements and six transitive axiom reports. The audit covers the retained-core bound at the stopping-program infimum, the direct closed-quantile comparison, estimator and minimax lower coefficients $10^{-17}$, and the two-sided confidence law with hard-cap upper coefficient $750000$. [Native record](../results/entropy-confidence-20261105/README.md)

## RMS obstruction transfer and localization

Run `python tools/verify_rms_localization.py` for 15 exact statements and 15 transitive axiom reports. The audit covers countable-label creation, arbitrary private seeds, midpoint-work charging, stopped finite decisions, the sharper binary risk inequality, and the generic and additive RMS coefficient $1/128$. [Native record](../results/rms-localization-20261105/README.md)

## Sharp finite-vector quantile factor

Run `python tools/verify_optimal_quantile.py` for 54 exact statements and 54 transitive axiom reports. The audit covers the Gibbs criterion, square-root tangents, finite-to-infinite limit, joint continuity, compact maximum, strict monotonicity, analytic endpoint bounds, unique root and the unrestricted finite-vector equivalence. The all-law comparison is checked by the separate audit below. [Native record](../results/optimal-quantile-root-20261105/README.md)

## Sharp finite-core selection reduction

The finite-core checkpoint records 49 exact statements and 49 transitive axiom reports. It covers entropy Lipschitz continuity, skipped-tail absorption, concavity, disjoint-coordinate reduction, entropy interaction, dyadic weights and both boundary-band cases. The current audit also checks the all-law comparison, as described below. [Native record](../results/quantile-core-reduction-20261105/README.md)

## All-law comparison at the exact scalar root

Run `python tools/verify_quantile_sharp_law.py` for 84 exact statements and 84 transitive axiom reports. The audit includes the original selection functional, countable tail merging, moment and work bounds, normalization, fractional quantile atoms, saturation and the selection infimum. [Native record](../results/sharp-quantile-upper-20261105/README.md)

## Exact quantile factor and finite-law optimality

Run `python tools/verify_quantile_optimality.py` for 81 exact statements and 81 transitive axiom reports. It verifies the finite probability-law family, support, fractional quantile split, entropy and selection prices, clipping, the limiting counterexample and exact least-factor equivalences. Together with the scalar and all-law audits above, this gives 219 exact statements and 219 transitive axiom reports. The decimal bracket retains the separate rational verifier `python tools/verify_optimal_quantile_factor.py`; its lower end is also Lean-checked by `verify_paper_statements.py` ([record](../results/paper-statements-20261120/README.md)). [Complete native record](../results/quantile-optimality-20261105/README.md)

## Time-uniform lower-bound families

Run `python tools/verify_anytime_lower.py` for 15 exact statements and transitive axiom reports. The audit covers central-segment information/work scaling, quarter-smoothing inversion, physical prefix work, admissibility, exact target separation and the observable prefix KL bound from an arbitrary four-prior certificate, plus posterior Lipschitz and per-flip Bernoulli KL inequalities. Run `python tools/verify_anytime_sequential.py` for eight exact statements and transitive axiom reports covering [observable sequential testing](ANYTIME_SEQUENTIAL.md). Run `python tools/verify_anytime_asymptotics.py` for fourteen exact statements and transitive axiom reports covering the finite-coefficient branch, dense and sparse infinite-moment branches, the full all-law theorem and observable interval half-widths. [Final native record](../results/anytime-asymptotic-20261105/README.md). [Native record](../results/anytime-lower-20261105/README.md). Run `python tools/verify_anytime_lower_profiles.py` for the separate exact finite profile checks.

Run `python tools/verify_anytime_tail.py` for fifteen exact statements and transitive axiom reports covering the [infinite-moment tail family](ANYTIME_TAIL.md), its original observable-prefix KL bound, and arbitrarily late physical-budget violations. The final selection-rate comparison is outside this audit.

## Finite-family unknown-law adaptation components

Run `python tools/verify_law_adaptation.py` for 17 independently restated exact
types and transitive axiom reports. It checks finite-prefix even-parity means,
bounded-average concentration, separated-signature identification and error
calibration, selection of simultaneous guarantees, physical budget arithmetic,
and the delayed comparison with the actual entropy-tail selection functional.
Run `python tools/verify_law_adaptation_realization.py` for 22 further exact
statements and transitive axiom reports. It verifies moment determinacy,
finite signature separation, the original population-tape parity pilot,
its actual read history, the selected observable controller, unconditional
caps and compatibility, joint all-budget coverage and oracle width, nesting,
and the original-experiment endpoint law. The
[full construction record](../results/law-adaptation-realization-20261105/README.md)
binds eight fresh empty compiler logs and the complete 648-source closure.
The [theorem and boundary](FINITE_FAMILY_ADAPTATION.md) retain the finite-family
premise; the arbitrary-law theorem has its own audits below.
Run `python -m unittest discover -s toolkit/tests -p test_law_identification.py -v`
for the executable rational pilot. Those tests do not formally verify Python.

[Native record for the finite-family components](../results/law-adaptation-20261105/README.md).

## Arbitrary-law adaptation components

Run `python tools/verify_arbitrary_law_entropy.py` for 15 exact statements and
transitive axiom reports covering finite entropy transport and its factor-three
band penalty. The [scope](ARBITRARY_LAW_FORMALIZATION.md) separates this from
the countable measure and statistical controller work, which have their own
audits below.

Run `python tools/verify_arbitrary_law_envelope.py` for 25 exact statements
and 24 transitive reports for the deterministic finite CDF envelope. The
statistical pilot event that supplies the grid bounds is proved by a later
audit below.

Run `python tools/verify_arbitrary_law_stage.py` for 17 exact statements and
16 transitive reports for observable paid-pilot/selected-continuation stages.
The [formal scope](ARBITRARY_LAW_FORMALIZATION.md) distinguishes this execution
component from the statistical instantiation and the final controller, which
later audits below check.

Run `python tools/verify_arbitrary_law_countable.py` for 16 exact statements
and transitive reports for countable entropy transport and its canonical
Gamma connection. Individual destination columns must be summable, but the
full entropy and moment may be infinite. The coupling-to-cell construction
is outside this component; see the [formal scope](ARBITRARY_LAW_FORMALIZATION.md).

Run `python tools/verify_arbitrary_law_coupling.py` for 19 exact statements
and transitive axiom reports: measurable canonical band indices, countable
cell integrals, and the factor-three Gamma comparison for finite increasing
couplings on positive gaps. Run `python tools/verify_arbitrary_law_selection.py`
for 13 more: Radon--Nikodym selection lifts, preserved mass and domination,
residual tail contraction, and the square-root-three comparison of the
original capped infimum. Neither result assumes a finite inverse moment.
CDF-to-coupling existence and the zero-atom extension are checked below.

Run `python tools/verify_arbitrary_law_cdf_coupling.py` for 11 exact statements
and transitive reports proving the common-uniform coupling for bounded
nonnegative laws. Run `python tools/verify_arbitrary_law_zero.py` for 36 more:
the zero-atom functional, exact agreement with positive-gap K, entropy and
selection transport on `[0,1/2]`, and the comparison starting from CDF
domination. Atoms and infinite inverse moments and entropy are allowed.

The dominated-mass comparison (A5) is checked by
`python tools/verify_arbitrary_law_dominated.py`: 22 exact statements and
22 transitive reports. Bounded density restriction transfers fractional
selections and controls their residuals. For finite measures,
`lambda <= c eta + e delta_0` gives `K(lambda) <= c K(eta) + e`
when `c >= 1` and `e >= 0`, retaining infinite entropy and the cap.

Run `python tools/verify_arbitrary_law_light_entropy.py` for 36 exact statements
and transitive reports: product-reference entropy, explicit numerical budgets,
two-band product geometry and the factor-1024 entropy bound for actual product
measure cells. Run `python tools/verify_arbitrary_law_light.py` for 26 more
exact statements and transitive reports: residual tails, the constructed
multiplier's exact CDF, and the full capped selection comparison with factor 32.
The final result imposes no inverse-moment or entropy condition on the input law.
Run `python tools/verify_arbitrary_law_tail_test.py` for 91 exact statements
and transitive reports on the sign-neutral single-coin tail test: its work cap,
dependence on the observed prefix, flip symmetry, the sign-neutral law on the
original population, both unresolved-probability bounds, the comparison with
the constructed multiplier, and the expected-work bound.
Run `python tools/verify_arbitrary_law_tail_probe.py` for 69 exact statements
and transitive reports on one capped probe over fresh coins: its caps and
charge, dependence on the bought flips, coverage of the small-gap mass at every
budget with probability at least 7/8, and the fixed-budget performance bound
with probability at least 3/4, with and without the coin cap.
Run `python tools/verify_arbitrary_law_tail_median.py` for 51 exact statements
and transitive reports on the median over independent probes: the majority
transfer to the median, Hoeffding across probes, statement (1) of the tail
certificate with its pathwise flip cap, the statement at every depth at once,
and both on a single coin array.
Run `python tools/verify_arbitrary_law_tail_oracle.py` for 26 exact statements
and transitive reports on the oracle comparison of the tail certificate: the
kernel bounds, the split of the gap law at its quantile, the onset condition
and its existence, and the bound of the median by 524288 times the selection
functional, at one depth and at every depth at once.
Run `python tools/verify_arbitrary_law_tail_observable.py` for 68 exact
statements and transitive reports on the tail certificate in the observable
experiment: the probe's reader and its invariant, consecutive blocks on
separate coin labels, the certificate as a function of the observed word, the
transfer of events about that word to the law of the original experiment, and
statements (1) and (3) for the estimator's output, at one depth and at every
depth up to a horizon.
Run `python tools/verify_arbitrary_law_pilot.py` for 66 exact statements and
transitive reports on the capped multi-depth pilot: the budgets and coin cap
(A6), the cap inequalities (A10), the depth-one certificate, the event (A8)
with a common number of probes, for the pilot alone and for the pilot in the
learning stage, and the learned law (A9) with its domination of the gap law.
Run `python tools/verify_arbitrary_law_pilot_onset.py` for 25 exact statements
and transitive reports on the first part of the learned law's oracle
comparison: the lowest-gap split of the gap law, the pilot's work estimates
(A12), its onset condition and its existence, and the bounds of the work and
of the coin cap by the selection functional.
Run `python tools/verify_arbitrary_law_learned_oracle.py` for 31 exact
statements and transitive reports on the rest of that comparison: the
multiplier law and its bound on the unresolved probabilities, the learned-CDF
bound (A13), the slack bound (A14), the clipped-CDF witness, and the
comparison (A11) with its finite onset and on the pilot event.
Run `python tools/verify_arbitrary_law_zero_quantile.py` for 22 exact
statements and transitive reports on the quantile design of a law with mass
at zero: its definition from the normalized positive part, the comparison
(A16) with the selection functional, and the converse.
Run `python tools/verify_known_law_planner.py` for 49 exact statements and
transitive reports on the known-law plan: the level races at the plan's caps,
the level price, the cap search, the counts from weights, and the validity of
the plan's squared-error certificate.
Run `python tools/verify_known_law_plan_rate.py` for 18 exact statements and
transitive reports on the rate of the exact plan: the least caps, the
multilevel sum, the terminal rule, the comparison of the certified risk with
the selection functional for the quantile split, the constant fallback and
the reported radius.
Run `python tools/verify_known_law_plan_tight_rate.py` for 31 exact statements
and transitive reports on the rate of a plan computed from upper bounds
within a factor two: the caps and prices against the next level, the
multilevel sum, the rate for the quantile split, and the plan of a reference
law with mass at zero with the planned coefficient and the radius
coefficient.
Run `python tools/verify_known_law_planner_output.py` for 9 exact statements
and transitive reports on the planner end to end: the constructed quantile
split, the plan in minimax form, the minimax rate from upper bounds and from
exact integrals for every law, and the design of a reference law with mass
at zero. The minimax statements name no estimator.
Run `python tools/verify_known_law_planner_estimator.py` for 8 exact
statements and transitive reports in which the estimator the planner returns
is named: its choice between the plan and the constant `ρ/2`, and in both
branches budget `B` and risk at most `44801 K` with exact integrals, or the
factor-two coefficient for every tight enclosure.
Run `python tools/verify_dyadic_summability.py` for 7 exact statements and
5 transitive reports proving that the dyadic series of the frozen targets H3
and H4 converge, with their frozen bounds as `HasSum` statements.
Run `python tools/verify_robust_error_transfer.py` for 33 exact statements
and transitive reports on the first part of the robust continuation: the
order on tapes of flips, the monotone ordinary classifier and race, the
downward and upward banks, and the transfer of the race's population error
to a true law coupled above its reference.
Run `python tools/verify_robust_coin_work.py` for 9 exact statements and
transitive reports on the work of the race for a coin with a larger gap
than the reference: the ordinary kernel, the negative bank and the positive
bank, each at the reference gap.
Run `python tools/verify_robust_level_certificates.py` for 18 exact
statements and transitive reports on the level certificates of the race
under a true law coupled above its reference: the split of a coupling along
the design, the selected core, resolved tail and unresolved part, and the
level work and level error.
Run `python tools/verify_robust_plan.py` for 20 exact statements and
transitive reports on the plan of a reference law under the true law: the
level races designed from the reference, the validity of an admissible
plan, and one estimator with risk at most `C_0 K_alpha` under every true law
coupled above the reference.

Run `python tools/verify_robust_cdf_bridge.py` for 12 exact statements and
transitive reports deriving that coupling from CDF domination, including
the zero-atom split, the original sign mass and rarity budget, and direct
budget/risk guarantees for the named plan and one reference-dependent
estimator valid for every CDF-dominated true law.

Run `python tools/verify_clipping_pilot_independence.py` for 26 exact
statements and transitive reports: clipping preserves the experiment and
work and cannot increase risk; the production stream and private seed
retain their original joint law after a positive-probability pilot history,
including the installed multi-depth pilot and its selected continuation.

Run `python tools/verify_paid_median.py` for 48 exact statements and
transitive reports: a reference-law base including the large-zero-atom
fallback, the physical-cap median, and its conditional and unconditional
coverage in the actual paid stage. The cap includes the pilot, the reported
radius is determined by the learned law, and total failure is at most the
sum of the pilot and continuation allowances. The full all-budget controller
and finite-law numerical implementation remain outside this audit.

## Full arbitrary-law all-budget controller

Run `python tools/verify_arbitrary_law_controller.py` for 99 exact statements
and transitive axiom reports from all twelve modules of
`ThresholdHC.ArbitraryLawController`. The audit covers the concrete schedule,
zero-work fallback, chronological controller, unconditional caps and prefix
consistency, nested intervals, joint pilot-and-coverage event, (A17)–(A18),
finite onset and final same-event width `2^32 C_* K(B/Lambda)`. The theorem
assumes no statistical stage oracle. CI also replays these twelve modules
through the independent kernel checker. Finite-law numerical enclosures,
Python/PRNG verification and manuscript/PDF publication remain separate.

## Deterministic output certificates

Run `python tools/verify_deterministic_certificates.py` to build the new checker,
check eight exact statements and all declared roots, replay its four modules
through the independent kernel checker, and check actual toolkit outputs plus
adversarial certificates. The output goes to a fresh directory under
`.runtime/deterministic-certificates/`. See the [contract and API inventory](DETERMINISTIC_VERIFICATION.md).
Run `python -m unittest discover -s tools -p test_deterministic_certificates_audit.py -v`
for the audit guards and the toolkit suite for input/runner rejection tests.
The proof covers checker soundness; concrete examples are finite execution
evidence. Global selection and planner implementation remain outside this audit.

## Finite-law objective and oracle certificates

Run `python tools/verify_finite_law_certificates.py` for the locked measure
bridges, exact statements, transitive axioms, five-module kernel replay and
actual-output certificates. Run `python -m unittest discover -s tools -p
test_finite_law_certificates_audit.py -v` for audit guards. Fresh results go to
`.runtime/finite-law-certificates/`; see [scope and limits](FINITE_LAW_CERTIFICATES.md).

## Envelope, rounding and transfer output certificates

Run `python tools/verify_envelope_transfer_certificates.py`, followed by
`python -m unittest discover -s tools -p test_envelope_transfer_certificates_audit.py -v`.
The audit checks twelve exact types, all declaration axioms, independent kernel
replay of the three new modules, actual outputs and numerical rejection cases.
It preserves source/compiler/artifact hashes under a fresh
`.runtime/envelope-transfer-certificates/`; see [contracts and limits](ENVELOPE_TRANSFER_CERTIFICATES.md).
CI uploads both this directory and `.runtime/finite-law-certificates/`.

## Global selection output certificates

Run `python tools/verify_global_selection_certificates.py`, followed by
`python -m unittest discover -s tools -p test_global_selection_certificates_audit.py -v`.
The focused audit checks eleven exact statements, all declaration roots and
independent replay of two new modules, then actual bounded exhaustive/DP/approximation
outputs and adversarial rejections. Evidence is written under
`.runtime/global-selection-certificates/`. The [scope](GLOBAL_SELECTION_CERTIFICATES.md)
distinguishes global output proofs from internal solver execution and polynomial
verification cost. The normal toolkit suite covers parser and failure boundaries.
