# Charging a fee per created coin: library audit

The model paragraph of the v6 paper
([`paper/v6/core.tex`](../../paper/v6/core.tex), section `sec:model`) ends
with two sentences: every coin actually created by the upper algorithm
receives at least one observation, and charging a fixed additional amount per
new outer draw therefore changes its cost by at most a constant factor. The
model-fidelity guide called the remark immediate in the Lean model, with no
separate creation-cost model
([`docs/MODEL_FIDELITY.md`](../../docs/MODEL_FIDELITY.md#3-physical-flip-cost)).
Lean now checks it, with the explicit factor $1+c$ and two consequences
beyond the source, in
[`lean/ThresholdHC/CreationCharge`](../../lean/ThresholdHC/CreationCharge/Full.lean).
The paper and the existing groups are unchanged. The audit runs below were
made at commit
[`5269d93`](https://github.com/davidiach/adaptive-threshold-estimation/commit/5269d93).

## Statements

The Lean model has no creation action separate from selection: the gap array
of the seed is drawn in advance, and an entry that is never selected has no
effect. A coin is therefore created when its label is first selected.
[`Specification.lean`](../../lean/ThresholdHC/CreationCharge/Specification.lean)
defines `createdLabels` (the distinct labels selected before step $n$),
`totalCreated` (its supremum over $n$, in $[0,\infty]$), the charged expected
cost `chargedExpectedWork` (one per observation plus $c$ per created coin),
the charged budget class and its minimax risk `chargedMinimaxRisk`.

| Target | Statement |
|---|---|
| `created_observed` | For every adaptive estimator and sign law, almost surely every created label was selected at an earlier observed step, and the number of created coins is at most the work. |
| `charged_work` | For a fee $c\ge0$, the expected work is at most the charged cost, which is at most $(1+c)$ times the expected work. |
| `charged_blind_upper` | One budget-indexed family, fixed before the gap law, has uniform budget $B$, charged budget $(1+c)B$ for every $c\ge0$, and RMS risk at most $12\,\omega_\mu(B^{-1/2})$. |
| `charged_minimax` | Beyond the source: for $c\ge0$, $R(B)\le R_c(B)\le R(B/(1+c))$. |
| `charged_rate` | Beyond the source: for $c\ge0$ and $B\ge1+c$, $\omega_\mu(B^{-1/2})/6\le R_c(B)\le12\sqrt{1+c}\,\omega_\mu(B^{-1/2})$. |

The source states the first sentence for the upper algorithm; Lean states it
for every adaptive estimator. Its first conjunct holds by construction of the
model, so the content is the counting inequality. Distinct labels are counted,
not the largest label used: the audited upper family encodes its labels with
`Nat.pair`, so counting pre-drawn gaps up to the largest label would break the
factor $1+c$ for it. Coins created but never observed, which the paper's model
allows, cannot be represented. The constant $12\sqrt{1+c}$ is one valid
choice, not a sharp one. The remark that finite internal computation between
observations is implicit has no target.

## How the proofs go

- [`Count.lean`](../../lean/ThresholdHC/CreationCharge/Count.lean): almost
  surely a step is observed exactly when the policy selects a label
  (`Tier5.realized_creation_valid_step` through `Tier6.population_realization`),
  so each created label was selected at an observed step, and the number of
  labels selected before step $n$ is at most the number of observations before
  $n$.
- [`Charge.lean`](../../lean/ThresholdHC/CreationCharge/Charge.lean): the
  charged cost lies between $W$ and $(1+c)W$ almost surely, hence in
  expectation, using only monotonicity of the lower integral, so no
  measurability of `totalCreated` is needed. Budgets transfer in both
  directions.
- [`Full.lean`](../../lean/ThresholdHC/CreationCharge/Full.lean): the blind
  family is `UpperScale.scaledFamily`; the rate combines the sharp lower bound
  of `SharpRMS`, the upper bound $12\,\omega$ of `UpperScale` at budget
  $B/(1+c)$ and $\omega(sh)\le s\,\omega(h)$ for $s=\sqrt{1+c}\ge1$.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_creation_charge.py --replay --jobs 2` | 8 exact statements (the 5 targets and 3 components) and 29 transitive axiom reports over the 4 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 4 modules replayed through the independent kernel checker. | [creation-charge-audit.log](creation-charge-audit.log) |
| `python -m unittest discover -s tools -p 'test_creation_charge.py'` | 11 guard tests pass. | |
| `python tools/verify_project_axioms.py` | 18,944 constants (15,258 theorems) in 1,592 modules, same axioms. 151 exported instances; 6 registered orphans, unchanged. 3,543 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python tools/verify_lean_sources.py` | 1,593 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added 10
entries to `tools/definition_lock.json`: the five statements, `createdLabels`,
`totalCreated`, `chargedExpectedWork`, `ChargedUniformBudget` and
`chargedMinimaxRisk`. No existing entry changed. The run recorded here is a
later one without that flag.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The specification was written before the proofs, reviewed, and
pinned by hash from this audit onward. The created-coin count is a reading of
"new outer draw" in a model where coins exist only once selected; it is not a
model of coins created and left unobserved.

## Review

The item was planned by one agent and criticized by a second, which replaced
the first statement by one with the source's quantifier, asked for the
counting choice to be documented and marked the minimax and rate targets as
going beyond the source. A third agent wrote the proofs. Before the
specification was pinned, a fourth agent that had not written them rebuilt the
modules, restated each target with its type written out, printed the axioms,
ran the audit's scans, checked by `decide` that `createdLabels` counts
distinct labels rather than selections, and showed that the charged class is
nonempty with finite minimax risk for $B\ge1+c$. It found no defect in the
Lean; its three minor points concerned docstrings (the existential form of
the blind-family statement and the reading of a negative fee as zero) and the
implementer's notes, and the docstrings were corrected before the pin. These
were reviews by AI agents, not a specialist referee report.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
