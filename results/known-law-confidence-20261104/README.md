# Fixed confidence for every known positive-gap law

At [the proof checkpoint](https://github.com/davidiach/adaptive-threshold-estimation/commit/46e1fa5925173d6c081c80d89b45ed4955ebe225),
the budget in the original observable experiment counts individual flips.
For positive budget and failure probability at most one quarter, evaluate
the stopping program at the budget divided by the log inverse failure
probability. One thirtieth of its value bounds the expected-budget radius
from below for any rarity up to one half. At rarity up to one quarter,
both budget models obey the entropy–tail rate with lower coefficient
$10^{-17}/30$ and upper coefficient $750000$. For the quadratic law the
critical rate has upper coefficient $2670000$ and a universal positive lower
coefficient. [Derivation](../../docs/STOPPING_CONFIDENCE.md) ·
[Manuscript Appendix S](../../paper/v6/appendix-known-confidence.tex)

| Audit | Exact statements | Transitive reports |
|---|---:|---:|
| [Direct stopping-program lower bound](stopping_confidence.lean) · [output](stopping_confidence.log) | 3 | 15 |
| [Observable median and minimax rates](confidence_amplification.lean) · [output](confidence_amplification.log) | 5 | 22 |
| [Earlier hard-budget guarantees](hard_budget.lean) · [output](hard_budget.log) | 10 | 39 |
| [Earlier critical confidence lower bound](critical_confidence.lean) · [output](critical_confidence.log) | 3 | 12 |
| [Earlier population confidence guarantees](confidence_population.lean) · [output](confidence_population.log) | 6 | 21 |

The [native record](status.json) identifies all 615 project modules in the
combined dependency closure. It records 29 recompiled module objects and
their compiler logs. Of the 586 inherited objects, 582 matched earlier
published object hashes and four have their first hashes in this record.
All five exact audits passed with only `propext`, `Classical.choice` and
`Quot.sound` allowed. One successful compilation emitted a tactic suggestion.
The tests distinguish the expected-work constraint from the pathwise cap.

Run `python tools/verify_stopping_confidence.py` and
`python tools/verify_confidence_amplification.py` from the repository root.
The stronger general-law lower coefficient in the localization paper,
the adaptive-type transfer and the known-law time-uniform width bound
remain separate formalization targets.
