# Verification and manuscript tools

Run tools from the repository root. Start with the
[task-to-command table](../docs/VERIFY.md#choose-checks-by-task) for checks and
[Lean map](../lean/README.md) for theorem-specific audits. Read a script's output
behavior before running it in a checkout that contains published evidence.

## Tool families

| Family | Entry points | Purpose and output |
|---|---|---|
| Entropy perturbation and approximate state compression | [verify_selection_approximation.py](verify_selection_approximation.py) | Rebuilds all six local modules into fresh `.runtime/selection-lean/` output, checks two locked exact targets and all new declaration axioms. Accepts `--lean-exe` and `--package-cache`; the [scope](../lean/ThresholdHC/SelectionApproximation/README.md) excludes the full FPTAS and Python execution. |
| Frozen and imported identities | [freeze.py](freeze.py) with `--verify`, [verify_inputs.py](verify_inputs.py) | Read-only identity checks. `freeze.py --init` is an authorized initialization operation, not a repair command. |
| Integrated research replay | [verify_research.py](verify_research.py) | Frozen/research identities and finite diagnostics; fresh temporary directory by default, or a new directory supplied with `--output-dir`. |
| Population and feedback replay | [verify_population_research.py](verify_population_research.py) | Sealed research identities and selected experiment replay in disposable copies under `.runtime/`. |
| Rare-event manuscript replay | [verify_rare_event_manuscript.py](verify_rare_event_manuscript.py) | Publication manifests and finite certificates in a temporary copy; prints the report and preserves the published payload. |
| Original Lean and tier audits | [verify_lean_checkpoint.py](verify_lean_checkpoint.py), [verify_uniform713.py](verify_uniform713.py), `verify_tier3.py` through `verify_tier6.py` | Build and audit frozen targets; write logs/status into tracked `results/`. Use a disposable checkout. |
| Scalar constant lemmas | [verify_uniform_arithmetic.py](verify_uniform_arithmetic.py) | Runs `lake env lean` on the unfrozen `proposals/constants/UniformArithmetic.lean` and checks its seven lemmas' axiom reports with the shared proof-escape and `sorry` guards; writes `results/constants_uniform_lean_audit.log` and `_status.json`. |
| Later theorem audits | `verify_*_components.py`, `verify_critical_psi.py`, `verify_critical_all_sizes.py`, `verify_unbiased_converse.py`, `verify_observable713.py`, `verify_confidence.py`, `verify_oracle_lower.py`, `verify_rare_above_two.py`, `verify_entropy_tail.py`, `verify_entropy_tail_upper.py`, `verify_entropy_tail_components.py`, `verify_entropy_tail_assembly.py`, `verify_quantile_comparison.py`, and the sixteen [stopping-program, identification and genie audits](../docs/VERIFY.md#stopping-program-identification-and-genie-certificates) (`stopping_program_lock.py` checks their specification lock) | Exact targets, source identities, and transitive axioms; timestamped directories under `.runtime/`, with an `--output-dir` option. The build options differ: the older audits accept `--sequential`; `verify_entropy_tail_upper.py`, `verify_entropy_tail_assembly.py`, `verify_entropy_tail_lower_components.py` and the sixteen stopping-program audits accept `--cached-dependencies` instead; `verify_entropy_tail_components.py` accepts neither. See the [theorem map](../lean/README.md#main-theorem-entry-points). |
| Guarded experiment persistence | [run_real_guarded.py](run_real_guarded.py) | Opt-in launcher for distinct fresh direct-real experiments; exclusive ownership, once-only held-out intent and atomic stage snapshots. See the [transition audit](../docs/EXPERIMENT_PERSISTENCE.md). Never adopts or restarts archived results. |
| Numerical and experiment checks | `check_targets*_numeric.py`, [check_power_bracket.py](check_power_bracket.py), [verify_experiment_lock.py](verify_experiment_lock.py), with [benchmark/verify_production.py](../benchmark/verify_production.py) | Finite/numerical diagnostics, stored-sample replay, the held-out record recomputed from its raw data, and exact replays of the production benchmark routines, with the scope described in [VERIFY.md](../docs/VERIFY.md#integrity-numerics-and-unit-tests). Some write `results/`; use a disposable checkout for the full sequence. |
| Results drift check | [check_results_drift.py](check_results_drift.py) | Run after the numerical and experiment checks. Compares the five records they rewrite in place with the committed versions, ignoring line endings, wall-clock fields and last-digit float noise. Reads files only. |
| Whole-project build and axiom audit | [verify_project_axioms.py](verify_project_axioms.py) | Registers nothing. Builds every module under `lean/ThresholdHC`, imports them all, and fails unless no project module declares an axiom and every constant depends only on `propext`, `Classical.choice` and `Quot.sound`. `--replay-main-theorem` also replays the modules behind both halves of the main RMS law through the toolchain's `leanchecker`. Prints its report; writes nothing. It complements the exact-type audits and says nothing about what a statement means. |
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
[CI workflow](../.github/workflows/checks.yml) is the complete integration
sequence; [toolkit CI](../.github/workflows/toolkit.yml) separately checks the
Python package.

## Registries and locks

`targets.json`, tier target registries, and `blind_upper_components.json` identify
the declarations and modules an audit expects. Specification freeze/lock JSON
files record exact source identities and dependency snapshots. Some verifier
scripts are themselves frozen. Inspect the relevant lock before editing a
registry or tool, and never regenerate hashes to suppress a failure.

For fresh outputs, keep the source commit and actual verification scope with
the record. See [results/README.md](../results/README.md) before publishing any
new evidence. Historical research validators can intentionally reject the
integrated checkout; use the maintained replay entry points above instead of
altering the original snapshots.

The Lean kernel audits added from 4 November onward take no build options
(two accept only `--lake`). They build with Lake, check exact statements and
transitive axioms, print the report and write no files.

Run `verify_law_adaptation.py` for 17 exact types and transitive axiom reports
covering [finite-family unknown-law adaptation components](../docs/FINITE_FAMILY_ADAPTATION.md):
sign-neutral parity, bounded-average concentration, identification, probability
transfer, physical cap arithmetic and the delayed oracle-rate comparison.

Run `verify_law_adaptation_realization.py` for 22 exact types and transitive
axiom reports covering moment determinacy, the actual shared-prefix pilot,
the full selected controller, unconditional physical caps and history
compatibility, joint all-budget coverage and oracle width, nesting, and the
original-experiment endpoint law.
[Native record](../results/law-adaptation-realization-20261105/README.md).

Run `verify_arbitrary_law_entropy.py` for the 15 finite entropy-transport
statements in `ArbitraryLawAdaptation`. See the [formal scope](../docs/ARBITRARY_LAW_FORMALIZATION.md);
the full arbitrary-law adaptation theorem remains a paper proof.

Run `verify_arbitrary_law_envelope.py` for 25 exact statements and 24 transitive
reports covering prefix minima, the finite probability measure, its zero atom,
and CDF domination from finitely many grid bounds.

Run `verify_arbitrary_law_stage.py` for 17 exact statements and 16 transitive
reports covering observable paid learning stages: fresh continuation labels,
physical caps, history readback and the joint original-experiment output law.

Run `verify_arbitrary_law_countable.py` for 16 exact statements and transitive
reports covering extended-valued countable entropy transport and its canonical
Gamma connection. No finite total inverse-square moment is assumed; the
destination-column summability condition remains explicit.

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
