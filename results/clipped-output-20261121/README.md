# Clipping the output to $[0,1]$ can only help: library audit

The upper-constant study
([`research/2026-11-18-upper-constant`](../../research/2026-11-18-upper-constant/README.md),
paragraph **Clipping** of its results) says that clipping the output to
$[0,1]$ can only help, and that the Lean theorem does not use it. Its
simulations, over 7 gaps and 3 sign fractions, give worst clipped ratios of
about $3.76$ at $N=2^8$ and $4.95$ at $N=2^{10}$, a gain of a factor $1.3$ to
$1.6$ at those budgets. The qualitative sentence had no proof in the
repository. Lean now checks it in the original adaptive experiment, in
[`lean/ThresholdHC/ClippedOutput`](../../lean/ThresholdHC/ClippedOutput/Full.lean),
with two consequences that go beyond the source. The research package and the
`UpperScale` and `HardBudget` groups are unchanged. The audit runs below were
made at commit
[`4b7bfa9`](https://github.com/davidiach/adaptive-threshold-estimation/commit/4b7bfa9).

## Statements

[`Specification.lean`](../../lean/ThresholdHC/ClippedOutput/Specification.lean)
states three targets against the existing `AdaptiveEstimator`,
`expectedWork`, `UniformBudget`, `rootMeanRisk`, `maximalRMSRisk`,
`minimaxRisk` and `modulus` of `Tier6`.

| Target | Statement |
|---|---|
| `unit_clip_monotone` | Every estimator $A$ has a version $A'$ with the same seed law and policy and output $\max(0,\min(1,\cdot))$ of $A$'s. For every probability law of gaps, $A'$ has the same expected work for every sign law and the same uniform budgets, its RMS risk is at most $A$'s for every sign law, and its maximal RMS risk is at most $\min(1,\text{that of }A)$. |
| `unit_output_minimax` | For every gap law and real $B$, the minimax RMS risk over estimators with outputs in $[0,1]$ equals `minimaxRisk`. Beyond the source. |
| `clipped_blind_upper_12` | One budget-indexed family with outputs in $[0,1]$, chosen before the gap law, has uniform budget $B$ and maximal RMS risk at most $\min(1,12\,\omega_\mu(B^{-1/2}))$ for every $B\ge1$ and every gap law. Beyond the source. |

The witness of the last target is the audited blind family with constant
$12$, `UpperScale.scaledFamily`, with its output clipped. The clipped
estimator of the first target is determined by its seed law, policy and
output, since its remaining fields are propositions. The simulated clipped
factors are not stated; nothing here gives a constant below $12$.

## How the proofs go

[`Clip.lean`](../../lean/ThresholdHC/ClippedOutput/Clip.lean) defines
`unitClip A`, which replaces the output by `HardBudget.clipEstimate 1` of it
and keeps every other field. The seed law, the policy, the experiment, the
expected work and the uniform budget are then unchanged by definition. The
target `signMean μ q` lies in $[0,1]$, so clipping cannot increase the squared
error at any outcome (`HardBudget.clip_loss_le`), and the clipped squared
error is at most $1$. Integrating gives both risk bounds.
[`Full.lean`](../../lean/ThresholdHC/ClippedOutput/Full.lean) derives the
three targets; the minimax identity follows by antisymmetry, since clipping
maps every admissible estimator into the restricted class without raising its
risk.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_clipped_output.py --replay --jobs 3` | 6 exact statements (the 3 targets and 3 components) and 19 transitive axiom reports over the 3 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 3 modules replayed through the independent kernel checker. | [clipped-output-audit.log](clipped-output-audit.log) |
| `python -m unittest discover -s tools -p 'test_clipped_output.py'` | 11 guard tests pass. | |
| `python tools/verify_project_axioms.py` | 17,953 constants (14,446 theorems) in 1,531 modules, same axioms. 150 exported instances; 6 registered orphans, unchanged. 3,367 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python tools/verify_lean_sources.py` | 1,532 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added four
entries to `tools/definition_lock.json`: `unitClip` and the three statements.
No existing entry changed. The run recorded here is a later one without that
flag.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The specification was written after the proofs; it is pinned by
hash from this audit onward. Outputs and targets both lie in $[0,1]$ after
clipping, so the bound by $1$ is automatic; the clause $12\,\omega$ adds
information only when $12\,\omega_\mu(B^{-1/2})<1$. The simulated clipped
ratios remain numerical evidence. The research package describes its own
checkpoint and is unchanged.

## Review

The item was planned by one agent, criticized by a second, which rewrote the
statements and advised building the clipped estimator locally rather than
importing the robust-continuation group, and written by a third. Before the
specification was pinned, a fourth agent that had not written the proofs
rebuilt the modules, restated the targets, printed the axioms, ran the
audit's scans and probed non-vacuity: the restricted minimax class is
nonempty for every real $B$, a raw constant estimator with output $3$ has
maximal RMS risk at least $2$, so the bound by $1$ does real work, and at the
point mass $\delta_{1/2}$ with $B=10^4$ the clause $12\,\omega=0.24$ is
informative. It found one minor point: the specification header quoted the
source sentence short and said only that sentence was stated, although two
further statements follow. The header was reworded before this audit. These
were reviews by AI agents, not a specialist referee report.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
