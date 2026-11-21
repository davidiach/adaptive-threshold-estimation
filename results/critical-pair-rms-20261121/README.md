# Critical common-pair RMS bound: library audit

The [model-fidelity brief](../../docs/MODEL_FIDELITY.md) notes that the
common-pair premise consumed by the RMS transfer is Lean-proved for the
quadratic critical law, with $b=\rho/32$ and an existential constant in $J$
([`critical_common_pair_bound`](../../lean/ThresholdHC/ConfidenceTransfer/CriticalRate.lean)),
but that no theorem states the composed RMS bound for that law. Lean now
states it, in
[`lean/ThresholdHC/CriticalPairRMS`](../../lean/ThresholdHC/CriticalPairRMS/Full.lean).
The audit runs below were made at commit
[`e9e45a1`](https://github.com/davidiach/adaptive-threshold-estimation/commit/e9e45a1).

## Statements

[`Specification.lean`](../../lean/ThresholdHC/CriticalPairRMS/Specification.lean)
states two targets, for the critical law of density $32d$ on $(0,1/4]$, with
$L=1+\log(1/\rho)$ and `criticalLogFactor` $\rho=L(1+\log L)$.

| Target | Statement |
|---|---|
| `critical_pair_rms` | For some $a>0$: every algorithm with rare budget $B>0$ at rarity $0<\rho\le1/4$ has RMS risk at least $\min\{\rho/32,\sqrt{a\rho L(1+\log L)/B}\}/128$. |
| `critical_pair_minimax_rms` | The same bound for the rare-event minimax risk. |

The constant $a$ is existential, as in the common-pair theorem. The critical
RMS law with explicit constants is checked separately
([`critical_explicit_constants`](../paper-statements-20261120/README.md));
these targets record only that the common-pair route reaches the same rate.

## How the proofs go

The proofs are in [`Full.lean`](../../lean/ThresholdHC/CriticalPairRMS/Full.lean).
The common pair at $b=\rho/32$, $J=a\rho L(1+\log L)$ is fed to
[`rms_rate_of_common_pair`](../../lean/ThresholdHC/RMSLocalization/CommonPair.lean),
which gives $R\ge\min\{b,\sqrt{J/B}\}/128$ for each algorithm; the minimax
form takes the infimum.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_critical_pair_rms.py --replay --jobs 3` | 2 exact statements (the 2 targets) and 4 transitive axiom reports over the 2 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 2 modules replayed through the independent kernel checker. | [critical-pair-rms-audit.log](critical-pair-rms-audit.log) |
| `python -m unittest discover -s tools -p 'test_critical_pair_rms.py'` | 11 guard tests pass. | |
| `python tools/verify_project_axioms.py` | 17,139 constants (13,766 theorems) in 1,474 modules, same axioms. 147 exported instances. 3,233 locked definition fingerprints. | [project-audit.log](../bias-subtraction-20261121/project-audit.log) of the bias-subtraction record, the same run |
| `python tools/verify_lean_sources.py` | 1,475 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added six
entries to `tools/definition_lock.json`: the statement and the helpers
`remarkLaw`, `remarkBias` and `oneFlipProcedure` of `BiasSubtraction`, and the
two statements of `CriticalPairRMS`. No existing entry changed. The run
recorded here is a later one without that flag; it covers both groups.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The specification was written after the proofs; it is pinned by
hash from this audit onward. The general-law $1/128$ transfers remain
conditional on their common-pair or obstruction premises for every other law.

## Review

Before the specification was pinned, a reviewer that had not written the
proofs checked that `criticalPositiveLaw` is the critical law, that
`criticalLogFactor` is $L(1+\log L)$, that the budget class is nonempty and the
minimax risk finite, and that the targets are the composition. It found no
blocking problem and asked that the existential constant be stated plainly;
the docstrings and this record now do. This was a review by an AI agent, not
a specialist referee report.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
