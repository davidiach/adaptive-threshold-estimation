# The noninterval optimal assignment: library audit

The discussion of the rare-event paper
([`rare-discussion.tex`](../../paper/v6/rare-discussion.tex), paragraph "A
noninterval optimal assignment"; preserved source
`paper/rare-event/v2/sections/discussion.tex`) gives a three-atom law at which
the optimal hard selection of the entropy-tail functional is not an interval of
gaps. Let $\varepsilon=1/1024$, put masses $(1-\varepsilon)/2$, $\varepsilon$,
$(1-\varepsilon)/2$ at the gaps $1/2$, $1/4$, $1/8$, and take $\rho=1/4$ and
$h=B^{-1/2}=1/1024$. The paper tabulates open rational enclosures of the inner
cost divided by $h$ for the eight hard retained sets; the unique minimum
retains $\{1/2,1/8\}$. The only previous check was the Python script
`paper/rare-event/v2/checks/verify_revisions.py`, which confirms the winner and
the inactive cap but not the table. Lean now checks the example, in
[`lean/ThresholdHC/NonintervalSelection`](../../lean/ThresholdHC/NonintervalSelection/Full.lean).
The audit runs below were made at commit
[`e40229b`](https://github.com/davidiach/adaptive-threshold-estimation/commit/e40229b).

## Statements

[`Specification.lean`](../../lean/ThresholdHC/NonintervalSelection/Specification.lean)
defines the atoms, masses, law, the hard retained part of each mask, the
optimal mask and the paper's table, and states five targets at $B=2^{20}$.

| Target | Statement |
|---|---|
| `setup` | The law is a probability law, $1/\sqrt{2^{20}}=1/1024$, every atom lies above $h$, and every hard retained part is below the law. |
| `enclosure` | The table covers the eight masks, and for each row the inner cost divided by $h$ lies strictly inside the row's open interval. |
| `unique_hard_minimum` | Retaining $\{1/2,1/8\}$ costs strictly less than every other hard retained set. |
| `original_optimizer` | That cost is below the cap $\rho$, the original functional `selection` (an infimum over all submeasures) equals it, and the retained part is the law restricted to $\{1/2,1/8\}$. |
| `noninterval` | The middle atom has positive mass, no interval of reals contains exactly the retained gaps, and every retention $\mu|_{\{d\in I\}}$ by an interval $I$ costs strictly more than the original functional. |

The inner cost is `EntropyTail.selectionObjective`, which keeps the tail term
$\min\{1,h/d\}$; since every gap exceeds $h$ it equals the paper's
$h\sqrt{\rho G}+\sum_jw_jh/d_j$. Uniqueness is over the eight hard sets, as in
the paper, not over fractional submeasures.

## How the proofs go

- [`Instance.lean`](../../lean/ThresholdHC/NonintervalSelection/Instance.lean)
  identifies the law with an atomic law of the finite-law certificate library
  and each retained part with a selection there, so the objective is the exact
  expression `objectiveExpr` of the deterministic checker. The bandwise suffix
  theorem gives attainment of `selection` by some hard mask; the three atoms lie
  in three different bands, so all eight masks are suffixes.
- [`Certificates.lean`](../../lean/ThresholdHC/NonintervalSelection/Certificates.lean)
  holds eight interval certificates, one per mask, checked by the existing
  checker's soundness theorem `accepted_sound`. Logarithms use the checker's
  series with ten terms; intermediate intervals are dyadic with denominators at
  most $2^{64}$, and each claimed interval is the paper's row shrunk by
  $10^{-7}$ and scaled by $h$. The evidence trees were produced by a
  generator outside the repository; Lean checks them, so the generator is not
  trusted.
- [`Table.lean`](../../lean/ThresholdHC/NonintervalSelection/Table.lean)
  derives the cap, the table and the strict minimum from the certificates, and
  [`Full.lean`](../../lean/ThresholdHC/NonintervalSelection/Full.lean) the five
  targets; for `noninterval`, the restriction of the law to an interval is the
  retained part of its membership mask, which is not the optimal mask.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_noninterval_selection.py --replay --jobs 3` | 8 exact statements (the 5 targets and 3 components) and 59 transitive axiom reports over the 5 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 5 modules replayed through the independent kernel checker. | [noninterval-selection-audit.log](noninterval-selection-audit.log) |
| `python -m unittest discover -s tools -p 'test_noninterval_selection.py'` | 11 guard tests pass. | |
| `python tools/verify_project_axioms.py` | 17,447 constants (14,024 theorems) in 1,498 modules, same axioms. 147 exported instances. 3,283 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python tools/verify_lean_sources.py` | 1,499 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added
fifteen entries to `tools/definition_lock.json`: the data of the example, the
five statements and the four definitions of the certificate instance. No
existing entry changed. The run recorded here is a later one without that flag.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The specification was written after the proofs; it is pinned by
hash from this audit onward. The paper's stated precision for its own
enclosures (90 series terms) is not used: the Lean certificates are an
independent check of the same open intervals.

## Review

The example was planned by one agent, criticized by a second, which added the
conjunct that every interval retention is strictly worse, and written by a
third. Before the specification was pinned, a fourth agent that had not
written the proofs rebuilt the five modules, recomputed the eight values to
fifty digits (the smallest margin inside the paper's intervals is
$2.24\cdot10^{-7}$, at $\{1/4,1/8\}$), restated the targets in full, printed
the axioms of all 59 declarations and ran the audit's token and namespace
scans. It found one defect, a module docstring of `Table.lean` that described
the inner cost where the module proves a bound on the checker value; it was
reworded before this audit. These were reviews by AI agents, not a specialist
referee report.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
