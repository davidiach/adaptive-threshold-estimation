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
| Later theorem audits | `verify_*_components.py`, `verify_critical_psi.py`, `verify_critical_all_sizes.py`, `verify_unbiased_converse.py`, `verify_observable713.py`, `verify_confidence.py`, `verify_oracle_lower.py`, `verify_rare_above_two.py` | Exact targets, source identities, and transitive axioms; timestamped directories under `.runtime/`, with `--output-dir` and `--sequential` options. See the [theorem map](../lean/README.md#main-theorem-entry-points). |
| Entropy-tail and quantile audits | [verify_entropy_tail_components.py](verify_entropy_tail_components.py), [verify_entropy_tail_assembly.py](verify_entropy_tail_assembly.py), [verify_entropy_tail_upper.py](verify_entropy_tail_upper.py) | Deterministic comparison, analytic assembly, and full observable upper targets respectively. Default rebuilds the local closure; optional cached-dependency modes record their narrower scope. Fresh `.runtime/` output. Statistical lower and two-sided flags remain false. |
| Stopping and cap identification | [verify_stopping_components.py](verify_stopping_components.py) | Exact types, all transitive axioms and source identities for the separate stopping/identification development; `.runtime/` output. Full stopping duality and genie flags remain false. |
| Infinite-divergence counterexample | [verify_genie_counterexample.py](verify_genie_counterexample.py) | Explicit uniform-gap example and arbitrary stopping-flow bound. Cached mode rebuilds eight new modules. |
| Direct risk and finite genie SOCP | [verify_genie_conic.py](verify_genie_conic.py) | Original minimax direct certificate and exact finite atom SOCP, including zero scales. Cached mode rebuilds eleven new modules. |
| Convergent genie certificates | [verify_genie_convergence.py](verify_genie_convergence.py) | Actual posterior information, vanishing reveal residual, optimized convergence and finite stopping. Cached mode rebuilds twelve new modules. |
| Monotone genie brackets and Bellman certificates | [verify_genie_brackets.py](verify_genie_brackets.py) | Extended ratio brackets, finite-divergence residual error bound, exact Bellman certificate and attainment. Cached mode rebuilds nine modules. Convergence remains separate. |
| Exact attained infinite-cap dual | [verify_infinite_cap_dual.py](verify_infinite_cap_dual.py) | Attained maximum, midpoint and original minimax comparisons, monotone cap limits. Cached mode rebuilds 14 modules. |
| Exact factor-sixteen finite certificate | [verify_finite_risk_certificate.py](verify_finite_risk_certificate.py) | All three unchanged finite stopping-program targets, original minimax risk, sharp truncation and Bernoulli-label floor. Cached mode rebuilds nine modules. |
| Adaptive information and finite-prefix risk | [verify_adaptive_information.py](verify_adaptive_information.py) | Sharp affinity testing, original adaptive experiment, exact prior contraction, and factor-eight finite-prefix comparison. Cached mode rebuilds nine modules. |
| Ordered stopping and local information | [verify_ordered_information.py](verify_ordered_information.py) | Arbitrary seeded ordered procedures, exact work, midpoint Hellinger comparison and local information/work bound. Cached mode rebuilds eleven modules. |
| Actual information-ratio Bellman characterization | [verify_information_bellman.py](verify_information_bellman.py) | Deterministic attainment, unique price zero, singular-state criterion and information increments; exact types and transitive axioms. Cached mode rebuilds seven modules. |
| Reference absorption and midpoint modulus | [verify_reference_absorption.py](verify_reference_absorption.py) | Global rarity preservation, extended information-ratio contraction and the factor-three comparison; exact types and transitive axioms. Cached mode rebuilds five modules. |
| Observable stopping-program upper bound | [verify_stopping_program_upper.py](verify_stopping_program_upper.py) | Original minimax upper theorem, actual certificate realization, exact types and all transitive axioms. Cached mode rebuilds fourteen statistical-realization modules; risk-comparison and genie flags remain false. |
| Finite flow mixtures and observable calls | [verify_stopping_flow_mixture.py](verify_stopping_flow_mixture.py) | Flow conservation, Bellman upper bounds, finite decision-table decomposition and bounded observable calls. Statistical moment/realization flags remain false. Cached mode rebuilds ten modules. |
| Exact finite-law stopping program | [verify_finite_stopping_program.py](verify_finite_stopping_program.py) | Equivalence to the original robust feasibility constraints; finite linear excess variables and the unchanged flow cone. Exact types, transitive axioms and source identities; cached mode rebuilds two modules. |
| Rarity support formula | [verify_rarity_support.py](verify_rarity_support.py) | Explicit fractional cutoff optimizer, raw supremum and attained scalar minimum; exact types, all transitive axioms and source identities. Cached mode rebuilds six new modules. |
| Attained four-prior conic dual | [verify_stopping_dual.py](verify_stopping_dual.py) | Both primal and dual attainment, exact specification and expanded type, all transitive axioms and source identities. Default rebuilds all local dependencies; `--cached-dependencies` rebuilds six attainment modules. Statistical realization, risk-certificate and genie flags remain false. |
| Numerical and experiment checks | `check_targets*_numeric.py`, [check_power_bracket.py](check_power_bracket.py), [verify_experiment_lock.py](verify_experiment_lock.py), with [benchmark/verify_production.py](../benchmark/verify_production.py) | Finite/numerical diagnostics, stored-sample replay, the held-out record recomputed from its raw data, and exact replays of the production benchmark routines, with the scope described in [VERIFY.md](../docs/VERIFY.md#integrity-numerics-and-unit-tests). Some write `results/`; use a disposable checkout for the full sequence. |
| Lean source guard | [verify_lean_sources.py](verify_lean_sources.py) | Scans every project Lean source (`lean/`, without `.lake` and `.audit`, plus `proposals/constants/`) with the strengthened shared proof-escape pattern after comment stripping. Read-only and needs no Lean build; a textual guard, not a parser. |
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
