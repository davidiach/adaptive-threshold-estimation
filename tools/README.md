# Verification and manuscript tools

Run tools from the repository root. Start with the
[task-to-command table](../docs/VERIFY.md#choose-checks-by-task) for checks and
[Lean map](../lean/README.md) for theorem-specific audits. Read a script's output
behavior before running it in a checkout that contains published evidence.

## Tool families

| Family | Entry points | Purpose and output |
|---|---|---|
| Assembled finite-law approximation | [verify_finite_selection_approximation.py](verify_finite_selection_approximation.py) | Checks the new specification/dependency lock, 12 exact statements and all 93 declaration axioms; writes a new `.runtime/finite-selection/` record. Covers original-K rational endpoints, finite precision, `S` states and `Q*S` extensions. Bit complexity and numerical/Python execution remain outside the [scope](../docs/FINITE_SELECTION_APPROXIMATION.md). |
| Entropy perturbation and approximate state compression | [verify_selection_approximation.py](verify_selection_approximation.py) | Rebuilds all six local modules into fresh `.runtime/selection-lean/` output, checks two locked exact targets and all new declaration axioms. Accepts `--lean-exe` and `--package-cache`; the [scope](../lean/ThresholdHC/SelectionApproximation/README.md) excludes the full FPTAS and Python execution. |
| Frozen and imported identities | [verify_locks.py](verify_locks.py), [freeze.py](freeze.py) with `--verify`, [verify_inputs.py](verify_inputs.py) | Read-only identity checks. `verify_locks.py` checks `FROZEN.sha256`, the Tier 3 to Tier 6 locks and the checksum manifests of the published manuscripts and records, and also fails when a line is deleted from `FROZEN.sha256`, which `freeze.py --verify` (itself frozen) misses. `freeze.py --init` is an authorized initialization operation, not a repair command. |
| Integrated research replay | [verify_research.py](verify_research.py) | Frozen/research identities and finite diagnostics; fresh temporary directory by default, or a new directory supplied with `--output-dir`. |
| Population and feedback replay | [verify_population_research.py](verify_population_research.py) | Sealed research identities and selected experiment replay in disposable copies under `.runtime/`. |
| Rare-event manuscript replay | [verify_rare_event_manuscript.py](verify_rare_event_manuscript.py) | Publication manifests and finite certificates in a temporary copy; prints the report and preserves the published payload. |
| Original Lean and tier audits | [verify_lean_checkpoint.py](verify_lean_checkpoint.py), [verify_uniform713.py](verify_uniform713.py), `verify_tier3.py` through `verify_tier6.py` | Build and audit frozen targets; write logs/status into tracked `results/`. Use a disposable checkout. |
| Scalar constant lemmas | [verify_uniform_arithmetic.py](verify_uniform_arithmetic.py) | Runs `lake env lean` on the unfrozen `proposals/constants/UniformArithmetic.lean` and checks its seven lemmas' axiom reports with the shared proof-escape and `sorry` guards; writes `results/constants_uniform_lean_audit.log` and `_status.json`. |
| Later theorem audits | `verify_*_components.py`, `verify_critical_psi.py`, `verify_critical_all_sizes.py`, `verify_unbiased_converse.py`, `verify_observable713.py`, `verify_confidence.py`, `verify_oracle_lower.py`, `verify_rare_above_two.py`, `verify_entropy_tail.py`, `verify_entropy_tail_upper.py`, `verify_entropy_tail_components.py`, `verify_entropy_tail_assembly.py`, `verify_quantile_comparison.py`, and the sixteen [stopping-program, identification and genie audits](../docs/VERIFY.md#stopping-program-identification-and-genie-certificates): `verify_stopping_components.py`, `verify_stopping_flow_mixture.py`, `verify_finite_stopping_program.py`, `verify_rarity_support.py`, `verify_stopping_dual.py`, `verify_information_bellman.py`, `verify_reference_absorption.py`, `verify_ordered_information.py`, `verify_adaptive_information.py`, `verify_stopping_program_upper.py`, `verify_finite_risk_certificate.py`, `verify_infinite_cap_dual.py`, `verify_genie_brackets.py`, `verify_genie_conic.py`, `verify_genie_convergence.py`, `verify_genie_counterexample.py` (three of them check the specification lock through `stopping_program_lock.py`) | Exact targets, source identities, and transitive axioms; timestamped directories under `.runtime/`, with an `--output-dir` option. The build options differ: the older audits accept `--sequential`; `verify_entropy_tail_upper.py`, `verify_entropy_tail_assembly.py`, `verify_entropy_tail_lower_components.py` and the sixteen stopping-program audits accept `--cached-dependencies` instead (`verify_stopping_components.py` also `--audit-only`), and in those modes Lake must first confirm that every reused module is up to date; `verify_entropy_tail_components.py` accepts neither. See the [theorem map](../lean/README.md#main-theorem-entry-points). |
| Guarded experiment persistence | [run_real_guarded.py](run_real_guarded.py) | Opt-in launcher for distinct fresh direct-real experiments; exclusive ownership, once-only held-out intent and atomic stage snapshots. See the [transition audit](../docs/EXPERIMENT_PERSISTENCE.md). Never adopts or restarts archived results. |
| Numerical and experiment checks | `check_targets*_numeric.py`, [check_power_bracket.py](check_power_bracket.py), [verify_experiment_lock.py](verify_experiment_lock.py), with [benchmark/verify_production.py](../benchmark/verify_production.py) | Finite/numerical diagnostics, stored-sample replay, the held-out record recomputed from its raw data, and exact replays of the production benchmark routines, with the scope described in [VERIFY.md](../docs/VERIFY.md#integrity-numerics-and-unit-tests). Some write `results/`; use a disposable checkout for the full sequence. |
| Results drift check | [check_results_drift.py](check_results_drift.py) | Run after the numerical and experiment checks. Compares the five records they rewrite in place with the committed versions, ignoring line endings, wall-clock fields and last-digit float noise. Reads files only. |
| Whole-project build and axiom audit | [verify_project_axioms.py](verify_project_axioms.py), [definition_lock.json](definition_lock.json) | Registers no theorem. Builds every module under `lean/ThresholdHC`, imports them all, and fails unless no project module declares an axiom and every constant depends only on `propext`, `Classical.choice` and `Quot.sound`. It also fails on any exported instance that is scoped, prioritised, not a project constant, or a new data-carrying instance on a type the project does not define, and on any change to the locked fingerprint, proofs erased, of a project definition or inductive type. A new definition fails until `--add-definitions` adds it; that option never rewrites an existing entry. `--replay-main-theorem` also replays the modules behind both halves of the main RMS law through the toolchain's `leanchecker`. Prints its report and writes only with `--add-definitions`. It complements the exact-type audits: the lock pins what each definition is, not what it means. |
| Lean source guard | [verify_lean_sources.py](verify_lean_sources.py) | Scans every project Lean source (`lean/`, without `.lake` and `.audit`, plus `proposals/constants/`) with the strengthened shared proof-escape pattern after comment stripping. Read-only and needs no Lean build; a textual guard, not a parser. |
| Finite-menu cost grouping | [verify_band_cost_selection.py](verify_band_cost_selection.py) | Checks 14 exact statements and transitive axioms for compression, optimality, state counts, entropy prices, exact comparisons and interval certificates. |
| Concrete gap-law menus | [verify_gap_law_menus.py](verify_gap_law_menus.py) | Checks 13 exact statements and transitive axioms connecting actual finite-law menus, atomic costs and savings, and the compressed optimum to the original $K$. |
| Finite-law bandwise-suffix theorem | [verify_bandwise_suffix.py](verify_bandwise_suffix.py) | Builds the optimizer and candidate bound, checks exact theorem types and audits transitive axioms. |
| Selection stability and finite approximation | [verify_selection_stability.py](verify_selection_stability.py) | Checks five exact statements and audits the transitive axioms. |
| Quarter smoothing for arbitrary laws | [verify_quarter_smoothing.py](verify_quarter_smoothing.py) | Checks both KL directions and the Hellinger normalization. |
| Finite, seeded and stopped population confidence transfer | [verify_confidence_population.py](verify_confidence_population.py) | Checks physical work, endpoint smoothing and the common-pair rate. |
| Hard observable flip budgets | [verify_hard_budget.py](verify_hard_budget.py) | Checks the target digest, original estimator, stage independence, risk bound and minimax rates. |
| Ordinary cap square-root convergence | [verify_finite_cap_truncation.py](verify_finite_cap_truncation.py) | Checks ten exact theorem types and transitive axioms for truncation, the ordinary program rate and its risk consequence. |
| Quantitative finite-cap convergence | [Lean audit](verify_genie_rate.py), [rational checks](verify_finite_cap_rate.py) | Checks the optimized programs and risk certificate, and replays finite Bellman comparisons. |
| Critical confidence lower bound | [Kernel audit](verify_critical_confidence.py) | Checks the gap density, common pair and unconditional minimax lower rate. |
| Quantile-factor bounds | [Sharp-factor audit](verify_quantile_optimality.py), [31/20 Lean audit](verify_quantile_price_upper.py), [rational inequalities](verify_quantile_price_bounds.py), [sharp-root certificate](verify_optimal_quantile_factor.py) | Checks the exact factor and finite-law optimality in Lean. The numerical endpoints have separate exact-rational verification. |
| Full quantile-selection comparison | [verify_quantile_selection.py](verify_quantile_selection.py) | Checks the two entropy lemmas, Theorem 4 and its statistical selection functional against their exact types and audits the transitive axioms. |
| Explicit general-law entropy-tail audit | [verify_entropy_tail_sharp.py](verify_entropy_tail_sharp.py) | Checks the explicit constants against their advance statement, the original model lock, the estimator converse and transitive axioms. |
| Direct finite-law quantile audit | [verify_finite_quantile.py](verify_finite_quantile.py) | Builds the finite-law theorem, the estimator witness and the converse with Lake. Checks the target, direct proof dependencies and transitive axioms. The exact statements are the seven `example` declarations of the committed `FiniteQuantile/Audit.lean`, which is pinned by hash. |
| Arbitrary-law Psi lower bound | [verify_psi_selection.py](verify_psi_selection.py) | Pins the specification, restates the comparison $\Psi\le\mathcal K$ and both minimax corollaries in full, and reports the transitive axioms of every declaration in `PsiSelection/`. Prints its report; writes nothing. |
| Closed form of Psi | [verify_psi_closed_form.py](verify_psi_closed_form.py) | Pins the specification, restates the comparisons of the entropy-free functionals, the chain $\mathcal Q^0\le\sqrt2\,\Psi\le\sqrt2\,\mathcal K^0\le\sqrt2\,\mathcal Q^0$ and the regime $h\ge t$ with the definitions written out, and reports the transitive axioms of every declaration in `PsiClosedForm/`. Prints its report; writes nothing. |
| Distance of Psi from the rate | [verify_psi_gap.py](verify_psi_gap.py) | Pins the specification, restates the entropy decomposition of the quantile core, the chain $\mathcal Q\le\sqrt{2(1+E_\kappa)}\,\Psi$, the two-sided risk bound and the reverse bound with the core cost and core entropy written out, and reports the transitive axioms of every declaration in `PsiGap/`. Prints its report; writes nothing. |
| Psi sharpness and occupied bands | [verify_psi_sharpness.py](verify_psi_sharpness.py) | Pins the specification, independently restates both targets and a concrete sharpness instance, and audits every declaration. Five exact statements, fifteen axiom reports. |
| Uniform power-law window | [verify_power_window.py](verify_power_window.py) | Pins the unchanged specification and checks all five targets, with 16 exact statements and 78 transitive axiom reports. Includes actual core entropy, the deterministic quantile comparison and unconditional RMS/confidence bounds. |
| Sharp universal RMS coefficient | [verify_sharp_rms.py](verify_sharp_rms.py) | Pins the specification and restates all eight targets and thirty component theorems: the lower coefficient $1/6$ for every gap law and $B\ge1$, its optimality, the stronger coefficient for $B\ge25$, the reduction to one gap, and the same bounds for both magnitude oracles. 38 exact statements and 343 transitive axiom reports over 54 registered modules. Private helper lemmas are not roots; `verify_project_axioms.py` covers them. `--replay` sends every module through the independent kernel checker, which re-evaluates the 140 integer comparisons. Prints its report; writes nothing. |
| Square-root cap comparison | [verify_square_root_cap.py](verify_square_root_cap.py) | Pins the specification and restates both targets: $P_N\le kG_N$ once $B\le N(k-1/k)^2$, and the factor-two test with the factor-sixteen certificate at $N\ge4B/9$. Two exact statements, six axiom reports. Prints its report; writes nothing. |
| Closed-quantile minimax audit | [verify_closed_quantile.py](verify_closed_quantile.py) | Full universal two-sided corollary in the original experiment; full local rebuild by default, or explicit `--cached-dependencies`, which requires Lake to confirm reused dependencies are up to date (`--build-dependencies` builds them). Fresh logs under `.runtime/closed-quantile/`. |
| Entropy-tail lower supporting audit | [verify_entropy_tail_lower_components.py](verify_entropy_tail_lower_components.py) | The complete finite-certificate lower proof, including packing and the finite-prefix limit; the canonical lower/law targets are checked separately by `verify_entropy_tail.py --require-complete`. Full dependency rebuild by default, or explicit `--cached-dependencies` with the same Lake up-to-date check and `--build-dependencies` option; fresh logs under `.runtime/entropy-tail-lower-components/`. |
| Known-law fixed confidence | [verify_stopping_confidence.py](verify_stopping_confidence.py), [verify_confidence_amplification.py](verify_confidence_amplification.py) | Build the original observable experiment and check the [fixed-confidence statements](../results/known-law-confidence-20261104/README.md) and minimax radii. |
| Stochastic envelope | [verify_stochastic_envelope.py](verify_stochastic_envelope.py) | The [unknown-law envelope corollary](../results/stochastic-envelope-20261105/README.md). |
| Power margins below two | [verify_sublinear_power.py](verify_sublinear_power.py), [verify_shifted_power.py](verify_shifted_power.py) | The [row below one](../results/sublinear-power-20261105/README.md) and the [logarithmic and intermediate rows](../results/shifted-power-20261105/README.md). |
| Time-uniform confidence | [verify_anytime_confidence.py](verify_anytime_confidence.py) | The [online confidence theorem](../results/anytime-confidence-20261105/README.md). |
| Smooth densities | [verify_smooth_density.py](verify_smooth_density.py) | The [smooth-density theorem](../results/smooth-density-20261105/README.md), its analytic construction and original-experiment identification. |
| Observed states | [verify_observed_states.py](verify_observed_states.py), [verify_continuous_observed.py](verify_continuous_observed.py), [verify_observed_upper.py](verify_observed_upper.py) | The [finite-cell theorem](../results/finite-observed-20261105/README.md), the [continuous-magnitude lower bounds and regularity](../results/continuous-observed-lower-20261105/README.md), and the [fresh-state upper-bound transfer and uniform-gap rates](../results/observed-state-upper-20261105/README.md). |
| Confidence localization | [verify_typed_confidence.py](verify_typed_confidence.py), [verify_confidence_localization.py](verify_confidence_localization.py), [verify_additive_confidence.py](verify_additive_confidence.py), [verify_confidence_entropy.py](verify_confidence_entropy.py), [verify_rms_localization.py](verify_rms_localization.py) | The [selected-type transfer](../results/adaptive-types-20261105/README.md), [common-pair construction](../results/common-pair-20261105/README.md), [fractional-submeasure localization](../results/additive-confidence-20261105/README.md), [sharper general-law coefficient](../results/entropy-confidence-20261105/README.md) and [generic RMS transfer](../results/rms-localization-20261105/README.md). |
| Sharp quantile factor | [verify_optimal_quantile.py](verify_optimal_quantile.py), [verify_quantile_sharp_law.py](verify_quantile_sharp_law.py), [verify_quantile_optimality.py](verify_quantile_optimality.py) | The [finite-vector factor and unique scalar root](../results/optimal-quantile-root-20261105/README.md), the [entropy Lipschitz bound and finite-core reduction](../results/quantile-core-reduction-20261105/README.md) together with the [all-law comparison](../results/sharp-quantile-upper-20261105/README.md), and [finite-law sharpness and exact optimality](../results/quantile-optimality-20261105/README.md). The numerical bracket is the separate exact-arithmetic tool `verify_optimal_quantile_factor.py`. |
| Time-uniform lower bound | [verify_anytime_asymptotics.py](verify_anytime_asymptotics.py), [verify_anytime_sequential.py](verify_anytime_sequential.py), [verify_anytime_tail.py](verify_anytime_tail.py), [verify_anytime_lower.py](verify_anytime_lower.py), [verify_anytime_lower_profiles.py](verify_anytime_lower_profiles.py) | The [final audit](../results/anytime-asymptotic-20261105/README.md) checks fourteen exact statements: the finite coefficient, dense and sparse cases, the full all-law theorem and the observable interval consequence. The sequential audit checks eight statements on first-crossing summability and infinitely many width violations; the [tail audit](../docs/ANYTIME_TAIL.md) checks fifteen on the infinite-moment family, adaptive acquisition and the testing schedule; the [information audit](../results/anytime-lower-20261105/README.md) checks 15 inequalities. Each also checks transitive axioms. The profile tool replays 32,768 exact rational comparisons on 16 atomic examples as regression checks ([note](../docs/TIME_UNIFORM_LOWER.md)). |
| Scoring and search | [score.py](score.py), [tune_constants.py](tune_constants.py), [constant scorers](../constants/) | Historical scoring/search protocol; may write evidence and acceptance state. Read [BRIEF.md](../BRIEF.md) as history and preserve the frozen and held-out constraints. These are not onboarding commands. |
| Manuscript assembly | [build_v6.py](build_v6.py), [build_v5.py](build_v5.py), [build_critical_review.py](build_critical_review.py), [build_status_docs.py](build_status_docs.py) | `--check` compares generated sources byte for byte without rewriting them. Without `--check`, regenerates TeX; PDF compilation is separate. `build_v6.py` also generates the v6 abstract and introduction status sentences from `paper/v6/status.json`; `build_status_docs.py` renders the same entries as the status tables in `README.md` and `docs/RESULTS.md`. |
| Current v6 build record | [check_build_record.py](check_build_record.py) | Reads the build that `paper/v6/README.md` links as the current manuscript. Fails when the record does not match its PDF (hash, size, page count), lacks a required field, or lists a changed page it did not visually check. Warns, or fails with `--strict`, when the record's TeX and `status.json` hashes no longer match the sources. Reads files only. |
| Regression tests | `test_*.py` | Exercise verification guards and manuscript assembly. Run the matching module for a focused change; the full command is below. |

```sh
python -m unittest discover -s tools -p 'test_*.py' -v
```

Regression tests do not replace the Lean kernel audits. The
[CI workflow](../.github/workflows/checks.yml) is the integration sequence. It
runs on pull requests and on pushes to `main`. The research and numerical
jobs always run. The four Lean jobs run when `.github/lean_ci.py` selects
them from the changed files; a manual run, or a change to proofs, the
toolchain or the workflow, runs all of them. A full run covers every
maintained audit except `verify_entropy_tail_components.py` and
`verify_entropy_tail_assembly.py`, which CI does not run.
[Toolkit CI](../.github/workflows/toolkit.yml) separately checks the Python
package, and two further workflows build the v6 PDF and test experiment
persistence.

## Registries and locks

`targets.json`, tier target registries, and `blind_upper_components.json` identify
the declarations and modules an audit expects. Specification freeze/lock JSON
files record exact source identities and dependency snapshots. Some tools
are themselves frozen: `freeze.py`, `score.py`, `check_targets_numeric.py`,
`check_targets2_numeric.py`, `verify_uniform713.py`, `verify_tier3.py` to
`verify_tier6.py`, and the registries `targets.json`, `tier3_targets.json` to
`tier6_targets.json` and `uniform713_targets.json`. Inspect the relevant lock before editing a
registry or tool, and never regenerate hashes to suppress a failure.

For fresh outputs, keep the source commit and actual verification scope with
the record. See [results/README.md](../results/README.md) before publishing any
new evidence. Historical research validators can intentionally reject the
integrated checkout; use the maintained replay entry points above instead of
altering the original snapshots.

Most Lean kernel audits added from 4 November onward take no build options
(two accept only `--lake`). They build with Lake, check exact statements and
transitive axioms, print the report and write no files. The exceptions are
`verify_sharp_rms.py` (`--replay`, `--jobs`), `verify_project_axioms.py`
(`--replay-main-theorem`, `--jobs`, `--add-definitions` and others), and the
output-certificate audits and `verify_finite_selection_approximation.py`,
which accept `--no-build` and `--output-dir`, and
`verify_selection_approximation.py` (`--lean-exe`, `--package-cache`,
`--output-dir`). All of these write a fresh directory under `.runtime/`.

## Unknown-law adaptation audits

These 36 audits check the adaptation theorems for an unknown gap law. Each
builds with Lake, restates its exact statements and reports transitive
axioms. The verification guide describes every one with its statement count;
the links below go to those sections.

| Scripts | Checks | Details |
|---|---|---|
| `verify_law_adaptation.py`, `verify_law_adaptation_realization.py` | Adaptation over a supplied finite family of gap laws: 17 component statements and the 22 statements of the observable construction | [VERIFY.md](../docs/VERIFY.md#finite-family-unknown-law-adaptation-components), [record](../results/law-adaptation-realization-20261105/README.md) |
| `verify_arbitrary_law_cdf_coupling.py`, `verify_arbitrary_law_countable.py`, `verify_arbitrary_law_coupling.py`, `verify_arbitrary_law_dominated.py`, `verify_arbitrary_law_entropy.py`, `verify_arbitrary_law_envelope.py`, `verify_arbitrary_law_learned_oracle.py`, `verify_arbitrary_law_light.py`, `verify_arbitrary_law_light_entropy.py`, `verify_arbitrary_law_pilot.py`, `verify_arbitrary_law_pilot_onset.py`, `verify_arbitrary_law_selection.py`, `verify_arbitrary_law_stage.py`, `verify_arbitrary_law_tail_median.py`, `verify_arbitrary_law_tail_observable.py`, `verify_arbitrary_law_tail_oracle.py`, `verify_arbitrary_law_tail_probe.py`, `verify_arbitrary_law_tail_test.py`, `verify_arbitrary_law_zero.py`, `verify_arbitrary_law_zero_quantile.py` | The components of the arbitrary-law proof: entropy transport, the conservative envelope, couplings, the pilot and the tail certificate | [VERIFY.md](../docs/VERIFY.md#arbitrary-law-adaptation-components), [formal scope](../docs/ARBITRARY_LAW_FORMALIZATION.md) |
| `verify_known_law_plan_rate.py`, `verify_known_law_plan_tight_rate.py`, `verify_known_law_planner.py`, `verify_known_law_planner_estimator.py`, `verify_known_law_planner_output.py` | The known-law plan, its rate and the named estimator | [VERIFY.md](../docs/VERIFY.md#arbitrary-law-adaptation-components) |
| `verify_robust_cdf_bridge.py`, `verify_robust_coin_work.py`, `verify_robust_error_transfer.py`, `verify_robust_level_certificates.py`, `verify_robust_plan.py`, `verify_clipping_pilot_independence.py`, `verify_paid_median.py` | The plan under a dominated true law, pilot independence and paid-median coverage | [VERIFY.md](../docs/VERIFY.md#arbitrary-law-adaptation-components) |
| `verify_dyadic_summability.py` | The dyadic series behind the frozen targets H3 and H4: 7 exact statements and 5 transitive axiom reports | [record](../results/dyadic-summability-20261114/README.md) |
| `verify_arbitrary_law_controller.py` | The all-budget controller, which completes the arbitrary-law theorem: 99 exact statements from twelve modules. CI also replays those modules through the independent kernel checker | [VERIFY.md](../docs/VERIFY.md#full-arbitrary-law-all-budget-controller), [record](../results/arbitrary-law-controller-20261116/README.md) |

## Deterministic certificate checker

`python tools/verify_deterministic_certificates.py` audits eight exact statements,
all declarations and four independently replayed modules, then checks actual
sqrt/log/entropy outputs and rejects invalid numerical certificates in Lean.
It records input/output proof source, axiom reports, source hashes and toolchain
identity under `.runtime/deterministic-certificates/`. See the
[implementation boundary](../docs/DETERMINISTIC_VERIFICATION.md).

`python tools/verify_finite_law_certificates.py` checks ten exact types and
52 transitive reports, replays five modules and tests actual objective/oracle
certificates with adversarial rejections. See the [finite-law scope](../docs/FINITE_LAW_CERTIFICATES.md).

`verify_envelope_transfer_certificates.py` checks twelve exact types, all roots
and independent kernel replay for three envelope/transfer modules, then actual
output and rejection cases. It snapshots sources and writes fresh evidence to
`.runtime/envelope-transfer-certificates/`. See the [scope](../docs/ENVELOPE_TRANSFER_CERTIFICATES.md).

`verify_global_selection_certificates.py` checks eleven exact types, all roots
and independent replay of two modules for complete menus and pruning primitives,
then bounded actual global output certificates and rejection cases. Evidence is
written to `.runtime/global-selection-certificates/`; the matching audit guards
are `test_global_selection_certificates_audit.py`. See the
[contract and limits](../docs/GLOBAL_SELECTION_CERTIFICATES.md).
