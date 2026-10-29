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
| Later theorem audits | `verify_*_components.py`, `verify_critical_psi.py`, `verify_critical_all_sizes.py`, `verify_unbiased_converse.py`, `verify_observable713.py`, `verify_confidence.py`, `verify_oracle_lower.py` | Exact targets, source identities, and transitive axioms; timestamped directories under `.runtime/`, with `--output-dir` and `--sequential` options. See the [theorem map](../lean/README.md#main-theorem-entry-points). |
| Numerical and experiment checks | `check_targets*_numeric.py`, [check_power_bracket.py](check_power_bracket.py), [verify_experiment_lock.py](verify_experiment_lock.py) | Finite/numerical diagnostics and stored-sample replay, with the scope described in [VERIFY.md](../docs/VERIFY.md#integrity-numerics-and-unit-tests). Some write `results/`; use a disposable checkout for the full sequence. |
| Scoring and search | [score.py](score.py), [tune_constants.py](tune_constants.py), [constant scorers](../constants/) | Historical scoring/search protocol; may write evidence and acceptance state. Read [BRIEF.md](../BRIEF.md) as history and preserve the frozen and held-out constraints. These are not onboarding commands. |
| Manuscript assembly | [build_v5.py](build_v5.py), [build_critical_review.py](build_critical_review.py) | `--check` compares generated sources without rewriting them. Without `--check`, regenerates TeX; PDF compilation is separate. |
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
