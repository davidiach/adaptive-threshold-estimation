# The selection and three-piece forms of the entropy-tail law: library audit

Theorem 13.2 of the v6 paper
([`entropy-tail-statement.tex`](../../paper/v6/entropy-tail-statement.tex),
`thm:entropy-tail-law`) states the general-law rate with universal constants
$0<c<C<\infty$, says that the functional $\mathcal K$ has the equivalent
selection form (61) and three-piece form (62), and says that hard measurable
assignments suffice. Lemma 13.1 (`lem:hard-selection`) adds that on a finite
atomic law a minimizing assignment can put each atom entirely in one of the
three pieces. Lean checked the law in form (61), with existential constants
not stated in order
([`EntropyTail`](../../lean/ThresholdHC/EntropyTail/Specification.lean)). The
order $c<C$, form (62) and its equivalence with (61) were paper steps. Lean now
checks them, in
[`lean/ThresholdHC/EntropyTailForms`](../../lean/ThresholdHC/EntropyTailForms/Full.lean).
The `EntropyTail` group and its records are unchanged. The audit runs below
were made at commit
[`f0f8d16`](https://github.com/davidiach/adaptive-threshold-estimation/commit/f0f8d16).

## Statements

[`Specification.lean`](../../lean/ThresholdHC/EntropyTailForms/Specification.lean)
defines $H_\tau=\int d^{-1}\,\tau(dd)$ (`inverseMass`), the bracket of (62),
$\zeta((0,1/2])+(\sqrt{\rho\Gamma_\sigma}+H_\tau)/\sqrt B$
(`threePieceObjective`), and form (62) capped at $\rho$
(`threePieceSelection`). All three take values in $[0,\infty]$ and are defined
for every measure. It states seven targets.

| Target | Statement |
|---|---|
| `fixed_core_split` | At a fixed core, the infimum over $\tau+\zeta=\nu$ of $\zeta((0,1/2])+hH_\tau$ is $\int\min\{1,h/d\}\,d\nu$, for $h\ge0$: each remaining magnitude goes to the cheaper cost. |
| `three_piece_inf` | For every finite measure and all real $\rho$, $B$: the infimum of (61) over $\sigma\le\mu$ equals the infimum of (62) over $\sigma+\tau+\zeta=\mu$. |
| `three_piece_form` | The same with the cap at $\rho$: `selection` $=$ `threePieceSelection`. |
| `ordered_law` | There are $0<c<C$ with $c\,\mathcal K\le R\le C\,\mathcal K$ for every law, $0<\rho\le1/4$ and $B>0$. |
| `three_piece_law` | The same law stated in form (62). |
| `hard_three_piece` | For probability laws, $0<\rho\le1/4$ and $B>0$: the infimum of (62) equals its infimum over measurable partitions $S,T,Z$ with pieces $\mu|_S,\mu|_T,\mu|_Z$. |
| `finite_hard_three_piece` | A law with finite support has a measurable partition $S,T,Z$ whose pieces minimize the bracket of (62) against every $\sigma+\tau+\zeta=\mu$. |

`three_piece_inf` and `three_piece_form` hold for every finite measure and all
real $\rho$ and $B$, which is wider than the paper; for $B\le0$ both sides
are $0$. `ordered_law` closes a bookkeeping gap only: any two-sided law gives
ordered constants after shrinking $c$. `hard_three_piece` reads the theorem's
clause that hard measurable assignments suffice for the three-piece form of a
general law; Lemma 13.1's literal sentence is `finite_hard_three_piece`.

## How the proofs go

The proofs are in [`Pieces.lean`](../../lean/ThresholdHC/EntropyTailForms/Pieces.lean)
and [`Hard.lean`](../../lean/ThresholdHC/EntropyTailForms/Hard.lean).

- At a fixed core the remainder splits on $\{h\le d\}$ and $\{d<h\}$, which
  attains $\int\min\{1,h/d\}$; any split $\tau+\zeta$ costs at least that, since
  $\min\{1,h/d\}$ is below both $1$ and $h/d$.
- (61) $=$ (62): every $\sigma+\tau+\zeta=\mu$ has $\sigma\le\mu$ and
  remainder $\tau+\zeta$, so (61) is at most (62); the split above attains
  (61) at each core.
- `ordered_law` takes the constants of the checked `entropy_tail_law` and
  replaces $c$ by $\min\{c,C/2\}$.
- Hard partitions: a hard core $\mu|_S$ (the checked `hard_selection`)
  with the split $T=\{h\le d\}\setminus S$, $Z=\{d<h\}\setminus S$ is a
  measurable partition. On finite laws the checked `bandwise_suffix` gives a
  hard minimizing core.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_entropy_tail_forms.py --replay --jobs 3` | 10 exact statements (the 7 targets and 3 components) and 37 transitive axiom reports over the 4 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 4 modules replayed through the independent kernel checker. | [entropy-tail-forms-audit.log](entropy-tail-forms-audit.log) |
| `python -m unittest discover -s tools -p 'test_entropy_tail_forms.py'` | 11 guard tests pass. | |
| `python tools/verify_project_axioms.py` | 17,354 constants (13,946 theorems) in 1,493 modules, same axioms. 147 exported instances. 3,268 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python tools/verify_lean_sources.py` | 1,494 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added ten
entries to `tools/definition_lock.json`: the three definitions above and the
seven statements. No existing entry changed. The run recorded here is a later
one without that flag.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The specification was written after the proofs; it is pinned by
hash from this audit onward. The explicit constants of the law,
$10^{-17}$ and $28000$, are the separate `EntropyTailSharp` targets.

## Review

The group was planned by one agent, criticized by a second and written by a
third. Before the specification was pinned, a fourth agent that had not
written the proofs compiled every module again, replayed them through the
kernel checker, restated the targets with the definitions unfolded, probed
non-vacuity ($0<$ `threePieceSelection` $<\infty$ on every admissible law, with
a case strictly below $\rho$) and ran the audit's token and namespace scans.
It found one defect: the docstring of `FiniteHardThreePieceStatement` read as
if every minimizer were hard, while the type says one is. The docstring was
reworded before this audit. These were reviews by AI agents, not a
specialist referee report.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
