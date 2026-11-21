# The 64-band selection example: library audit

The finite-law section of the v6 paper
([`paper/v6/finite-laws.tex`](../../paper/v6/finite-laws.tex), section
`fg:sec:model`) says that the selection algorithm certifies an optimizer on a
64-band example using 65 terminal states. The band-cost guide
([`docs/BAND_COST_SELECTION.md`](../../docs/BAND_COST_SELECTION.md), *Example
with 64 occupied bands*) defines the example: $d_i=2^{-i}$ with masses
proportional to $d_i^2$ for $i=1,\dots,64$, $\rho=1/4$ and budget $B=2^{32}$.
Every nonempty suffix has the same cost, the run checks 4,160 transitions and
65 terminal states, and retaining the two largest gaps attains $K$. That run
is a Python toolkit run. Lean now checks the example and the run of the
formal solver, in
[`lean/ThresholdHC/BandCostExample`](../../lean/ThresholdHC/BandCostExample/Full.lean).
The `BandCostSelection` and `GapLawMenus` groups and the toolkit are
unchanged. The audit runs below were made at commit
[`1563371`](https://github.com/davidiach/adaptive-threshold-estimation/commit/1563371).

## Statements

[`Specification.lean`](../../lean/ThresholdHC/BandCostExample/Specification.lean)
defines the 64 atoms (atom $i$ is the gap $2^{-(i+1)}$, the source's
$d_{i+1}$, in canonical band $i$), the law, the hard retained part of a mask
and the mask `topTwo` of the two largest gaps, and states five targets
against the existing `selection`, `selectionObjective`, `GapLawMenus` menus
and costs and `BandCostSelection.solve`.

| Target | Statement |
|---|---|
| `setup` | The law is a probability law on the 64 atoms, atom $i$ lies in band $i$, $B^{-1/2}=2^{-16}$, and every hard retained part is a submeasure. |
| `equal_cost` | Each one-atom suffix $\{d\}$ has the same positive inverse-square cost $1/\sum_jd_j^2$. |
| `unique_hard_minimum` | Among all $2^{64}$ hard masks, the two largest gaps are the strict unique minimum of the objective. An added strengthening. |
| `optimizer` | The cap is inactive at that mask, the selection functional over all submeasures equals its objective, and the retained part is the restriction of the law to $\{1/2,1/4\}$. |
| `solver_run` | On the actual support menus: $2^{64}$ suffixes, 64 two-option menus, 4,160 transitions and 65 terminal states, and a terminal trace that selects $\{1/2,1/4\}$ with value $K$. |

Every menu is exactly $\{\emptyset,\{d\}\}$ for one atom $d$ (the component
`mem_menus`), so the one-atom suffixes are all the nonempty ones, as the
source says. The counts are those of the formal solver, which count what the
toolkit's counters count; the Python run and its interval certificate stay
unverified. No numerical value of $K$ is stated, as in the source.

## How the proofs go

[`Instance.lean`](../../lean/ThresholdHC/BandCostExample/Instance.lean)
matches the real-valued law with rational masses $g^2/\sum g^2$ and computes
$\sum_jd_j^2=(1-4^{-64})/3$.
[`Objective.lean`](../../lean/ThresholdHC/BandCostExample/Objective.lean)
writes the objective of a mask through its number $k$ of retained atoms.
[`Rearrange.lean`](../../lean/ThresholdHC/BandCostExample/Rearrange.lean)
bounds the sum of $k$ distinct dyadic gaps by that of the $k$ largest, and two
gaps other than $1/2,1/4$ by $5/8$.
[`Optimal.lean`](../../lean/ThresholdHC/BandCostExample/Optimal.lean) reduces
the comparison with the two-gap mask to an inequality in $k$ and the retained
gap sum, checked by cases on $k$, and shows the cap is inactive. [`Frontier.lean`](../../lean/ThresholdHC/BandCostExample/Frontier.lean)
and [`Solver.lean`](../../lean/ThresholdHC/BandCostExample/Solver.lean) count
the solver's states and transitions on the two-option menus.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_band_cost_example.py --replay --jobs 3` | 8 exact statements (the 5 targets and 3 components) and 147 transitive axiom reports over the 8 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 8 modules replayed through the independent kernel checker. | [band-cost-example-audit.log](band-cost-example-audit.log) |
| `python -m unittest discover -s tools -p 'test_band_cost_example.py'` | 11 guard tests pass. | |
| `python tools/verify_project_axioms.py` | 18,491 constants (14,902 theorems) in 1,566 modules, same axioms. 151 exported instances; 6 registered orphans, unchanged. 3,448 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python tools/verify_lean_sources.py` | 1,567 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added 27
entries to `tools/definition_lock.json`: the instance, the five statements and
the auxiliary definitions of the objective and the rational masses. No
existing entry changed. The run recorded here is a later one without that
flag.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The specification was written after the proofs; it is pinned by
hash from this audit onward. The new lemmas live in a new group because the
`GlobalSelectionCertificates` and `FiniteSelectionApproximation` statements
and the definitions behind them are pinned. The toolkit and its guide are
unchanged.

## Review

The item was planned by one agent, criticized by a second, which corrected
the statements and suggested the direct pair bound for the strict case, and
written by a third. Before the specification was pinned, a fourth agent that
had not written the proofs rebuilt the modules, checked each theorem against
its statement, printed the axioms, ran the audit's scans, compared the formal
counts with the toolkit's counters, and probed non-vacuity: the masses and
their normalizer are positive, and a competing mask has a finite objective,
so no strict inequality holds by an infinite right side. It found one minor
point: three docstrings said every nonempty suffix has the stated cost while
the statement covers the one-atom suffixes. They were reworded, and the
lemma that every menu has a single one-atom option is now an audited
component. These were reviews by AI agents, not a specialist referee report.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
