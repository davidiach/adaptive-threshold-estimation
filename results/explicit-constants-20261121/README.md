# Explicit constants: library audit

Three constants that the guides cite were proved in Lean only for each
algorithm, or only as the witness inside a proof of a frozen statement that
asserts a positive constant. Lean now states them as exact targets, in
[`lean/ThresholdHC/ExplicitConstants`](../../lean/ThresholdHC/ExplicitConstants/Full.lean).
The frozen statements and their locks are unchanged. The audit runs below were
made at commit
[`4a64b683402c07d5866f0d0328699febb22d5e9c`](https://github.com/davidiach/adaptive-threshold-estimation/commit/4a64b683402c07d5866f0d0328699febb22d5e9c).

## Statements

| Target | Statement | Before |
|---|---|---|
| `hidden_confidence` | In the hidden model, every algorithm with uniform expected budget $B\ge1$ and uniform confidence radius $r$ at level $0<\delta\le1/4$ has $r\ge\frac{15}{256\sqrt2}\,\omega_\mu(\sqrt{\log(1/\delta)/B})$. | Per-algorithm theorem [`hidden_confidence_lower`](../../lean/ThresholdHC/OracleLower/Confidence.lean), axiom-audited but not an exact-type target; the frozen statement has $1/64$. |
| `hidden_confidence_minimax` | The minimax confidence radius lies between $\frac{15}{256\sqrt2}$ and $8192$ times that modulus. | The frozen characterization has $1/64$ and $8192$. |
| `rare_lower_256` | For every gap law supported below $a$, every algorithm with rare budget $B\ge1$ has risk at least $\frac1{256}\min\{\rho,\sqrt\rho/(a\sqrt B)\}$. | The frozen `RareSupportedLowerStatement` asserts a positive constant; the proof uses $1/256$. |
| `rare_minimax_256` | The same lower bound for the rare-event minimax risk. | Lean had the minimax form only for exact power laws, with an existential constant. |
| `rare_single_coin_28` | The frozen single-coin statement with $K=28$: one family that flips only coin $0$ is unbiased with second moment at most $28\rho$ and work at most $W_\alpha/a^2$ for every power margin with $\alpha>2$ and every sign law with $\int q\,d\mu\le\rho$. | The frozen statement asserts a positive $K$; the proof uses $28$. |

The hidden model is the Tier 6 experiment, in which the algorithm sees only its
seed and the flips; the magnitude oracle appears only inside the proof, through
an embedding of hidden algorithms.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_explicit_constants.py --replay --jobs 3` | 5 exact statements and 10 transitive axiom reports over the 2 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. Both modules replayed through the independent kernel checker. | [explicit-constants-audit.log](explicit-constants-audit.log) |
| `python -m unittest discover -s tools -p 'test_explicit_constants.py'` | 11 guard tests pass. | |
| `python tools/verify_project_axioms.py` | 17,021 constants (13,664 theorems) in 1,454 modules, same axioms. 147 exported instances. 3,217 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python tools/verify_lean_sources.py` | 1,455 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added nine
entries to `tools/definition_lock.json`: the five statements of
`ExplicitConstants`, and the statement and the helpers `pad`, `hist` and
`stopEvent` of `NonnegativeUnbiased`. No existing entry changed. The run
recorded here is a later one without that flag; it covers both groups.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The specification was written after the proofs; it is pinned by
hash from this audit onward. Each proof instantiates the constant the existing
proof already uses; no constant is improved.

## Review

Before the specification was pinned, a reviewer that had not written it
compared each statement line by line with the frozen statement it extends and
checked the hidden model, vacuity and Lean conventions. It found nothing false
or vacuous: each statement keeps the frozen hypotheses and fixes only the
constant, and the minimax infimum sets are nonempty. Its wording fixes to two
docstrings were applied. This was a review by an AI agent, not a specialist
referee report.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
