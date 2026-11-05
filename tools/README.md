# Verification and manuscript tools

Run tools from the repository root. Start with the
[task-to-command table](../docs/VERIFY.md#choose-checks-by-task) for checks and
[Lean map](../lean/README.md) for theorem-specific audits. Read a script's output
behavior before running it in a checkout that contains published evidence.

## Tool families

| Family | Entry points | Purpose and output |
|---|---|---|
| Frozen and imported identities | [freeze.py](freeze.py) with `--verify`, [verify_inputs.py](verify_inputs.py) | Read-only identity checks. `freeze.py --init` is an authorized initialization operation, not a repair command. |
| Integrated research replay | [verify_research.py](verify_research.py) | Frozen/research identities and finite diagnostics; fresh temporary directory by default, or a new directory supplied with `--output-dir`. |
| Population and feedback replay | [verify_population_research.py](verify_population_research.py) | Sealed research identities and selected experiment replay in disposable copies under `.runtime/`. |
| Rare-event manuscript replay | [verify_rare_event_manuscript.py](verify_rare_event_manuscript.py) | Publication manifests and finite certificates in a temporary copy; prints the report and preserves the published payload. |
| Original Lean and tier audits | [verify_lean_checkpoint.py](verify_lean_checkpoint.py), [verify_uniform713.py](verify_uniform713.py), `verify_tier3.py` through `verify_tier6.py` | Build and audit frozen targets; write logs/status into tracked `results/`. Use a disposable checkout. |
| Scalar constant lemmas | [verify_uniform_arithmetic.py](verify_uniform_arithmetic.py) | Runs `lake env lean` on the unfrozen `proposals/constants/UniformArithmetic.lean` and checks its seven lemmas' axiom reports with the shared proof-escape and `sorry` guards; writes `results/constants_uniform_lean_audit.log` and `_status.json`. |
| Later theorem audits | `verify_*_components.py`, `verify_critical_psi.py`, `verify_critical_all_sizes.py`, `verify_unbiased_converse.py`, `verify_observable713.py`, `verify_confidence.py`, `verify_oracle_lower.py`, `verify_rare_above_two.py`, `verify_entropy_tail.py`, `verify_entropy_tail_upper.py`, `verify_entropy_tail_components.py`, `verify_entropy_tail_assembly.py`, `verify_quantile_comparison.py`, and the sixteen [stopping-program, identification and genie audits](../docs/VERIFY.md#stopping-program-identification-and-genie-certificates) (`stopping_program_lock.py` checks their specification lock) | Exact targets, source identities, and transitive axioms; timestamped directories under `.runtime/`, with `--output-dir` and `--sequential` options. See the [theorem map](../lean/README.md#main-theorem-entry-points). |
| Numerical and experiment checks | `check_targets*_numeric.py`, [check_power_bracket.py](check_power_bracket.py), [verify_experiment_lock.py](verify_experiment_lock.py), with [benchmark/verify_production.py](../benchmark/verify_production.py) | Finite/numerical diagnostics, stored-sample replay, the held-out record recomputed from its raw data, and exact replays of the production benchmark routines, with the scope described in [VERIFY.md](../docs/VERIFY.md#integrity-numerics-and-unit-tests). Some write `results/`; use a disposable checkout for the full sequence. |
| Lean source guard | [verify_lean_sources.py](verify_lean_sources.py) | Scans every project Lean source (`lean/`, without `.lake` and `.audit`, plus `proposals/constants/`) with the strengthened shared proof-escape pattern after comment stripping. Read-only and needs no Lean build; a textual guard, not a parser. |
| Finite-law bandwise-suffix theorem | [verify_bandwise_suffix.py](verify_bandwise_suffix.py) | Builds the optimizer and candidate bound, checks exact theorem types and audits transitive axioms. |
| Selection stability and finite approximation | [verify_selection_stability.py](verify_selection_stability.py) | Checks five exact statements and audits the transitive axioms. |
| Quarter smoothing for arbitrary laws | [verify_quarter_smoothing.py](verify_quarter_smoothing.py) | Checks both KL directions and the Hellinger normalization. |
| Finite, seeded and stopped population confidence transfer | [verify_confidence_population.py](verify_confidence_population.py) | Checks physical work, endpoint smoothing and the common-pair rate. |
| Hard observable flip budgets | [verify_hard_budget.py](verify_hard_budget.py) | Checks the target digest, original estimator, stage independence, risk bound and minimax rates. |
| Quantitative finite-cap convergence | [Lean audit](verify_genie_rate.py), [rational checks](verify_finite_cap_rate.py) | Checks the optimized programs and risk certificate, and replays finite Bellman comparisons. |
| Critical confidence lower bound | [Kernel audit](verify_critical_confidence.py) | Checks the gap density, common pair and unconditional minimax lower rate. |
| Quantile-factor bounds | [Sharp-factor audit](verify_quantile_optimality.py), [31/20 Lean audit](verify_quantile_price_upper.py), [rational inequalities](verify_quantile_price_bounds.py), [sharp-root certificate](verify_optimal_quantile_factor.py) | Checks the exact factor and finite-law optimality in Lean. The numerical endpoints have separate exact-rational verification. |
| Full quantile-selection comparison | [verify_quantile_selection.py](verify_quantile_selection.py) | Checks the two entropy lemmas, Theorem 4 and its statistical selection functional against their exact types and audits the transitive axioms. |
| Explicit general-law entropy-tail audit | [verify_entropy_tail_sharp.py](verify_entropy_tail_sharp.py) | Checks the explicit constants against their advance statement, the original model lock, the estimator converse and transitive axioms. |
| Direct finite-law quantile audit | [verify_finite_quantile.py](verify_finite_quantile.py) | Builds the finite-law theorem, the estimator witness and the converse with Lake. Checks the target, direct proof dependencies and transitive axioms. |
| Closed-quantile minimax audit | [verify_closed_quantile.py](verify_closed_quantile.py) | Full universal two-sided corollary in the original experiment; full local rebuild by default, or explicit `--cached-dependencies`, which requires Lake to confirm reused dependencies are up to date (`--build-dependencies` builds them). Fresh logs under `.runtime/closed-quantile/`. |
| Entropy-tail lower supporting audit | [verify_entropy_tail_lower_components.py](verify_entropy_tail_lower_components.py) | The complete finite-certificate lower proof, including packing and the finite-prefix limit; the canonical lower/law targets are checked separately by `verify_entropy_tail.py --require-complete`. Full dependency rebuild by default, or explicit `--cached-dependencies` with the same Lake up-to-date check and `--build-dependencies` option; fresh logs under `.runtime/entropy-tail-lower-components/`. |
| Scoring and search | [score.py](score.py), [tune_constants.py](tune_constants.py), [constant scorers](../constants/) | Historical scoring/search protocol; may write evidence and acceptance state. Read [BRIEF.md](../BRIEF.md) as history and preserve the frozen and held-out constraints. These are not onboarding commands. |
| Manuscript assembly | [build_v6.py](build_v6.py), [build_v5.py](build_v5.py), [build_critical_review.py](build_critical_review.py) | `--check` compares generated sources without rewriting them. Without `--check`, regenerates TeX; PDF compilation is separate. |
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

Run `verify_stopping_confidence.py` and `verify_confidence_amplification.py`
for the [fixed-confidence statements and native record](../results/known-law-confidence-20261104/README.md).
They build the original observable experiment before checking the minimax radii.

Run `verify_stochastic_envelope.py` for the unknown-law envelope corollary.
[Statements and native logs](../results/stochastic-envelope-20261105/README.md)

Run `verify_sublinear_power.py` for [the power-margin row below one](../results/sublinear-power-20261105/README.md).

Run `verify_shifted_power.py` for [the logarithmic and intermediate power-margin rows](../results/shifted-power-20261105/README.md).

Run `verify_anytime_confidence.py` for [the online confidence theorem](../results/anytime-confidence-20261105/README.md).

Run `verify_smooth_density.py` for the [smooth-density theorem](../results/smooth-density-20261105/README.md), its analytic construction and original-experiment identification.

Run `verify_observed_states.py` for the [finite-cell observed-state theorem](../results/finite-observed-20261105/README.md), its construction and selected-query experiment.

Run `verify_continuous_observed.py` for the [continuous-magnitude lower bounds and regularity](../results/continuous-observed-lower-20261105/README.md).

Run `verify_observed_upper.py` for the [full fresh-state upper-bound transfer and uniform-gap rates](../results/observed-state-upper-20261105/README.md).

Run `verify_typed_confidence.py` for the [selected-type information transfer](../results/adaptive-types-20261105/README.md), including exact work charging and stopped reconstruction.

Run `verify_confidence_localization.py` for the [common-pair construction and its confidence consequence](../results/common-pair-20261105/README.md).

Run `verify_additive_confidence.py` for [fractional-submeasure additive confidence localization](../results/additive-confidence-20261105/README.md).

Run `verify_confidence_entropy.py` for the [sharper general-law confidence coefficient](../results/entropy-confidence-20261105/README.md).

Run `verify_rms_localization.py` for [generic RMS obstruction transfer and additive localization](../results/rms-localization-20261105/README.md).

Run `verify_optimal_quantile.py` for the [sharp finite-vector factor and unique scalar root](../results/optimal-quantile-root-20261105/README.md). The numerical bracket uses the separate exact-arithmetic tool `verify_optimal_quantile_factor.py`.

Run `verify_quantile_sharp_law.py` for the [entropy Lipschitz and finite-core reduction](../results/quantile-core-reduction-20261105/README.md). The same audit now includes the all-law upper comparison below.

The `verify_quantile_sharp_law.py` audit now includes the [all-law upper comparison](../results/sharp-quantile-upper-20261105/README.md) at the exact scalar-root coefficient.

Run `verify_quantile_optimality.py` for [finite-law realization and exact least-factor equivalences](../results/quantile-optimality-20261105/README.md).

Run `verify_anytime_lower.py` for the [law-dependent prior-family and observable information bounds](../docs/TIME_UNIFORM_LOWER.md). It audits 15 exact statements and their transitive axioms. Run `verify_anytime_sequential.py` for eight exact statements covering first-crossing summability and infinitely many width violations in the observable experiment. Run `verify_anytime_asymptotics.py` for fourteen exact statements covering the finite coefficient, dense and sparse cases, full all-law theorem, and observable interval consequence. [Native record](../results/anytime-asymptotic-20261105/README.md).

Run `verify_anytime_tail.py` for fifteen exact statements covering the infinite-moment tail family, adaptive acquisition transfer, and explicit unbounded testing schedule. See the [construction and its boundary](../docs/ANYTIME_TAIL.md).
