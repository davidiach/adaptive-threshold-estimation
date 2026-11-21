# Restricted-class RMS coefficient: library audit

The research note [`rms-gap.tex`](../../research/2026-11-17-rms-constants/README.md)
finds the RMS coefficient exactly $1/6$ in several restricted settings: for
budgets through four, for protocols with at most three flips per coin, and
for two classes with unlimited revisits. These had no Lean statement. Lean's
sharp-coefficient theorem
([`SharpRMS`](../../lean/ThresholdHC/SharpRMS/Full.lean)) proves $1/6$ for
every protocol, with equality at the endpoint gap $1/2$ and $B=4$. Lean now
states the restricted settings, in
[`lean/ThresholdHC/RestrictedRMS`](../../lean/ThresholdHC/RestrictedRMS/Full.lean).
The research package is unchanged. The audit runs below were made at commit
[`acfc8f2`](https://github.com/davidiach/adaptive-threshold-estimation/commit/acfc8f2).

## Statements

[`Specification.lean`](../../lean/ThresholdHC/RestrictedRMS/Specification.lean)
states four targets. Each has the form of the sharp-coefficient statement: a
real $c$ satisfies $R_\mu(B)\ge c\,\omega_\mu(B^{-1/2})$ at every gap law and
every admissible budget exactly when $c\le1/6$. The note writes this as
$\inf R_\mu(B)/\omega_\mu(B^{-1/2})=1/6$; the forms agree because $\omega>0$.

| Target | Setting |
|---|---|
| `small_budget_coefficient` | Every protocol, budgets $1\le B\le4$. |
| `oracle_small_budget_coefficient` | The same with every magnitude revealed, and with each fresh magnitude selected by the algorithm. |
| `three_flip_coefficient` | Protocols that flip each coin at most three times, with revisits, interleaving, private randomness and unbounded stopping, budgets $B\ge1$. |
| `restricted_coefficient` | Any class of protocols that contains every four-fresh-flip protocol and any set of budgets at least one that contains four. |

The three-flip condition counts the earlier flips of the requested coin at
every seed and every history, reachable or not, so the class is contained in
the note's; the conclusion is unchanged, because the lower bound holds for
every protocol and the witness lies in the class. The three-flip and class
statements are for the ordinary model only. The note states the budget
restriction for the ordinary model; the oracle form rests on the companion
note's statement that both magnitude oracles have the same sharp constant.
The preassigned local experiments and the adaptively selected sign-symmetric
rules of the note are not defined in Lean. That the four-flip witness belongs
to them is the note's claim, so for those classes the result is conditional
on it, through `restricted_coefficient`.

## How the proofs go

The proofs are in [`Restricted.lean`](../../lean/ThresholdHC/RestrictedRMS/Restricted.lean).
A restricted class can only raise the minimax risk, so the all-protocol
theorem keeps $1/6$ valid. Conversely, the four-fresh-flip protocol has budget
four, belongs to every class considered, and has worst RMS risk at most $1/6$
at the endpoint gap, where $\omega(1/2)=1$ (`four_flips_rms_le`,
`endpoint_modulus_one`), so no larger coefficient is valid. The oracle forms
use the oracle endpoint equality and lower bound of `SharpRMS`. The note's
class-specific arguments (the small-budget Fisher argument, the three-flip
certificate tree and the paired-bias inequality) are not formalized; they are
not needed for these statements.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_restricted_rms.py --replay --jobs 3` | 7 exact statements (the 4 targets and 3 components) and 16 transitive axiom reports over the 3 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 3 modules replayed through the independent kernel checker. | [restricted-rms-audit.log](restricted-rms-audit.log) |
| `python -m unittest discover -s tools -p 'test_restricted_rms.py'` | 11 guard tests pass. | |
| `python tools/verify_project_axioms.py` | 17,160 constants (13,783 theorems) in 1,477 modules, same axioms. 147 exported instances. 3,237 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python tools/verify_lean_sources.py` | 1,478 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added four
entries to `tools/definition_lock.json`, the four statements of
`RestrictedRMS`. No existing entry changed. The run recorded here is a later
one without that flag.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The specification was written after the proofs; it is pinned by
hash from this audit onward. The note's other numbers, the four-flip
obstruction and the intermediate lower coefficients, are not targets.

## Review

Before the specification was pinned, a reviewer that had not written the
proofs checked the form of each statement against the note, that the
three-flip predicate counts flips of the coin the policy requests at each
history, that the classes are nonempty and the upper direction uses the
witness, and the soundness of the proofs. It found no blocking problem and
asked for precise wording on the oracle form and on class membership; the
docstrings and this record now give it. This was a review by an AI agent,
not a specialist referee report.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
