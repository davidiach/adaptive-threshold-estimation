# The simpler unknown-law confidence sequence: library audit

[`docs/UNKNOWN_LAW_CONFIDENCE.md`](../../docs/UNKNOWN_LAW_CONFIDENCE.md#all-authorized-budgets)
describes a confidence sequence that uses neither the gap law nor a bound on
its small-gap tail. Stage $j$ has allowance $c_j$, buys $m_j=\lfloor
c_j/n_j\rfloor$ flips from each of $n_j=\lfloor\sqrt{c_j}\rfloor$ fresh items,
declares strict positive and negative items with Hoeffding margins, and
reports $[p_+-a-\tau,\,1-p_-+a+\tau]\cap[0,1]$; the interval at a budget
intersects $[0,u]$ with the stage intervals completed within it. For
$0<\delta<1$, iid fresh latent pairs with $0<D\le1/2$, any measurable
dependence of the sign on the gap and a supplied $u\ge\theta$ (or $u=1$),
the intervals cover $\theta$ simultaneously at every authorized integer budget
with probability at least $1-\delta$, the stage width is at most
$\mathbb P(D\le2r_j)+3a_j+3\tau_j$, and the width tends to zero. The note and
the secondary-claims guide kept this as a paper proof
([`docs/SECONDARY_CLAIMS.md`](../../docs/SECONDARY_CLAIMS.md#1-the-simpler-unknown-law-confidence-sequence)).
Lean now checks it, in
[`lean/ThresholdHC/UnknownLawConfidence`](../../lean/ThresholdHC/UnknownLawConfidence/Full.lean).
The note's time-uniform lower bound is not part of this group. The audit runs
below were made at commit
[`d70886e`](https://github.com/davidiach/adaptive-threshold-estimation/commit/d70886e).

## Statements

[`Specification.lean`](../../lean/ThresholdHC/UnknownLawConfidence/Specification.lean)
defines the Hoeffding count $H(k,e)$ (the least $H$ with
$k\lceil\log_2(1/e)\rceil\le2H^2$), the stage sizes, tolerances and radii,
the stage reader and interval, the controller `controller δ u B upper` in the
observable simulation of the repository (a trivial seed and a persistent iid
coin table under `streamLaw`, as in the arbitrary-law controller), its
interval at each budget, `widthBound μ δ j`, and the success event.

| Target | Statement |
|---|---|
| `unknown_law_confidence` | For $0<\delta<1$ and every real $u$: pathwise cap $B$, prefix compatibility, nesting in $B$ and range $[0,u]$ for every budget; for every probability gap law and sign law, the original simulation law is `streamLaw`, the success event has probability at least $1-\delta$ when $\theta\le u$ and, with no hypothesis, at $u=1$; `widthBound` tends to zero; and on the success event the half-width tends to zero. |
| `unknown_law_stopping` | On the success event, at any data-dependent budget $\tau(z)$, the interval covers $\theta$ and twice its half-width is at most `widthBound μ δ j` for every completed stage $j$. This only unfolds the event. |

The success event requires coverage at every integer budget and the stage
bound at every completed stage, which is stronger than the note's statement
at one checkpoint. $\lceil\log_2(1/e)\rceil$ is written with `Real.logb`; no
lemma links it to the toolkit's `bit_length` formula, and the toolkit's
execution is not certified. The width limit uses $\delta\le1$; coverage holds
for every $\delta>0$.

## How the proofs go

- [`Counts.lean`](../../lean/ThresholdHC/UnknownLawConfidence/Counts.lean)
  and [`Word.lean`](../../lean/ThresholdHC/UnknownLawConfidence/Word.lean):
  stage sizes, the Hoeffding count, and the stage reader on the coins
  `Nat.pair j (Nat.pair 1 (Nat.pair i 0))`.
- [`Item.lean`](../../lean/ThresholdHC/UnknownLawConfidence/Item.lean),
  [`Population.lean`](../../lean/ThresholdHC/UnknownLawConfidence/Population.lean)
  and [`Sample.lean`](../../lean/ThresholdHC/UnknownLawConfidence/Sample.lean):
  one item's false declaration probability, the population proportions, and
  the sampling deviations of the three empirical proportions.
- [`Controller.lean`](../../lean/ThresholdHC/UnknownLawConfidence/Controller.lean):
  each stage as a learned stage with no pilot, the controller's caps and law,
  and the union bound over stages for the success event.
- [`Limit.lean`](../../lean/ThresholdHC/UnknownLawConfidence/Limit.lean): the
  radii, sampling terms and tolerances tend to zero, and so does the small-gap
  mass at radius $2r_j$, by dominated convergence.
- [`Full.lean`](../../lean/ThresholdHC/UnknownLawConfidence/Full.lean): the
  targets, and the measurability of the success event.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_unknown_law_confidence.py --replay --jobs 2` | 5 exact statements (the 2 targets and 3 components: the measurability of the success event, its probability and the width limit) and 121 transitive axiom reports over the 9 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 9 modules replayed through the independent kernel checker. | [unknown-law-confidence-audit.log](unknown-law-confidence-audit.log) |
| `python -m unittest discover -s tools -p 'test_unknown_law_confidence.py'` | 11 guard tests pass. | |
| `python tools/verify_project_axioms.py` | 19,789 constants (15,950 theorems) in 1,657 modules, same axioms. 155 exported instances (one new, above); 6 registered orphans, unchanged. 3,693 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python tools/verify_lean_sources.py` | 1,658 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added 32
entries to `tools/definition_lock.json`: the two statements and the
definitions above with their helpers. No existing entry changed. The group
adds one exported instance, `streamLaw_probability`, named, global and
Prop-valued. The run recorded here is a later one without that flag.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The specification was written before the proofs, reviewed, and
pinned by hash from this audit onward. The note's Bernoulli-subfamily
time-uniform lower bound, which cites an external proposition, remains a
paper proof.

## Review

The item was planned by one agent and criticized by a second, which added an
unconditional coverage conjunct at $u=1$ and the width clause at the stopping
budget, and noted that the stopping statement is a corollary. A third agent
wrote the proofs. Before the specification was pinned, a fourth agent that
had not written them rebuilt the modules, printed the axioms, checked the
definitions against the note, instantiated the theorem at a Dirac gap law with
sign $1/2$, and checked concrete values ($n_0=m_0=2$, $n_3=5$, $m_3=6$,
$H(2,1/2)=1$). It found no defect in the statements or proofs. It noted that
the success event was not shown measurable, so the probability bound formally
concerned the outer measure; `measurableSet_successEvent` was added and is an
audited component. Its other minor point, a module docstring that left out the
premise $\theta\le u$, was corrected. These were reviews by AI agents, not a
specialist referee report.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
