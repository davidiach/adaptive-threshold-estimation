# RMS upper constant 13: library audit

The [previous record](../upper-sign-20261119/README.md) gave the constant
$15$ for the RMS law's upper bound with a distribution-blind mixture of two
budget levels. The exact probability of a vote change between consecutive
classifiers gives $13$ for the same mixture. The audit runs below were made
when the proof was added, at commit
[`85a86a245ce5b5241289b30a8b79843eb322a11f`](https://github.com/davidiach/adaptive-threshold-estimation/commit/85a86a245ce5b5241289b30a8b79843eb322a11f).

## Statements

[`lean/ThresholdHC/UpperQuarter/Specification.lean`](../../lean/ThresholdHC/UpperQuarter/Specification.lean)
states two targets against the original experiment, budget, risk and
modulus definitions, with $\omega_\mu(h)=\int\min(1,h/d)\,\mu(dd)$:

| Target | Statement |
|---|---|
| `blind_upper_13` | One budget-indexed family, chosen before the gap law, keeps the uniform expected-work budget $B$ and has RMS risk at most $13\,\omega_\mu(B^{-1/2})$ for every gap law and every $B\ge1$. |
| `minimax_upper_13` | $R_\mu(B)\le13\,\omega_\mu(B^{-1/2})$ for every gap law and every $B\ge1$. |

With the sharp lower constant $1/6$, the two sides of the RMS law are now a
factor $78$ apart, in place of $90$. The specification was written after the
proof; it is pinned by hash from this audit onward. The v6 paper still states
$15$, in Appendix AB.

## Where 15 became 13

The family is `budgetMixture` of
[`UpperMixture`](../../lean/ThresholdHC/UpperMixture/Full.lean), unchanged.
The [previous record](../upper-sign-20261119/README.md) bounded the
disagreement of consecutive classifiers below the split by one half plus an
early-stop term, and the first two levels by one.

**Vote change.** [`VoteChange.lean`](../../lean/ThresholdHC/UpperQuarter/VoteChange.lean)
counts the successes $N_1$ among the first $n$ flips and $N_2$ among the next
$n$. The majority votes after $n$ and $2n$ flips are $n<2N_1$ and
$n<N_1+N_2$, so they change exactly on
$\{n<2N_1,\ N_1+N_2\le n\}\cup\{2N_1\le n,\ n<N_1+N_2\}$. The two counts are
independent with the same law, so their joint law is the product of one law
with itself (`map_successes_pair`) and is invariant under the swap of
coordinates. The change and its swap are disjoint, and together they are the
event that exactly one of $N_1$ and $N_2$ exceeds $n/2$, which has probability
$2a(1-a)$ with $a=\Pr(n<2N_1)$. So the votes change with probability exactly
$a(1-a)\le\tfrac14$, for every coin and every $n$ (`count_voteChange_le`). The
previous record bounded the same event by the larger event
$\{m<N_1,\ N_2<m\}\cup\{N_1\le m,\ m<N_2\}$, of probability at most $\tfrac12$.

**Every level.** [`EarlyStop.lean`](../../lean/ThresholdHC/UpperQuarter/EarlyStop.lean)
applies this at every level, the first included: consecutive classifiers
disagree with probability at most one quarter plus the early-stop bound of
the smaller one (`disagree_tape_quarter`). At the first level the smaller
classifier has no early checks, so the bound is one quarter.

**Grid.** [`Grid.lean`](../../lean/ThresholdHC/UpperQuarter/Grid.lean) moves
the split to $x=19/20$ and weights each level by `quarterWeight`: the cap terms
$e^{-2x}+e^{-x}$ from the split on, one quarter plus the drift bounds of the
smaller classifier below it, and one at level zero. The first grid point $s$
at or above the split lies in $[19/20,19/10]$, which is cut into four bands.
In each band the drift bounds of the $(i+1)$-th level below $s$ are at most a
tabulated step (`band_step_le`), from tables in
[`DriftTable.lean`](../../lean/ThresholdHC/UpperQuarter/DriftTable.lean) at the
scales $h_k/2^{i+2}$ for the band's upper end $h_k$; this needs the drift
lemmas for scales up to one half
([`Drift.lean`](../../lean/ThresholdHC/UpperQuarter/Drift.lean)). The levels
below the split add at most the band coefficient times $\sqrt s$, for every
number of levels (`band_coef_le`): $0.96$, $0.997$, $1.035$ and $1.073$. With
the cap terms above the split,
[`Offset.lean`](../../lean/ThresholdHC/UpperQuarter/Offset.lean) bounds the
weighted grid sum by $89/50$, with 17 pieces in all (`band_offset_le`,
`quarter_grid_le`). The drift tables and the pieces were chosen and checked in
exact rational arithmetic by a script and emitted as one Lean lemma each.

**Level sum and chain.** [`Increment.lean`](../../lean/ThresholdHC/UpperQuarter/Increment.lean)
bounds the squared increment at level $l$ by one and by `quarterWeight` plus
the early-stopping terms of both classifiers (`quarter_increment_le`).
[`LevelSum.lean`](../../lean/ThresholdHC/UpperQuarter/LevelSum.lean) gives $d$
times the second moment at most
$(2+\sqrt2)\cdot\tfrac{89}{50}+\tfrac{41}{100}\le\tfrac{13}{2}$. With the regime
term of `UpperDisagreement`, the second moment is at most
$\tfrac{13}{2}\min(\sqrt N,1/d)+\tfrac{129}{25}B$ (`quarter_levelSum_le`). Since
$\tfrac{129}{25}\cdot\tfrac{11}{2}\le\tfrac{13}{2}\cdot\tfrac92$,
[`Batch.lean`](../../lean/ThresholdHC/UpperQuarter/Batch.lean) bounds the batch
mean-square error by $\tfrac{147}{4}=1+\tfrac{13}{2}\cdot\tfrac{11}{2}$ times
$\omega_\mu(N^{-1/2})^2$. [`Full.lean`](../../lean/ThresholdHC/UpperQuarter/Full.lean)
gives $\tfrac92\cdot\tfrac{147}{4}=\tfrac{1323}{8}\le13^2$.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_upper_quarter.py --replay --jobs 3` | 13 exact statements and 75 transitive axiom reports over 12 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 12 modules replayed through the independent kernel checker. | [upper-quarter-audit.log](upper-quarter-audit.log) |
| `python tools/verify_project_axioms.py` | 16,233 constants (13,090 theorems) in 1,408 modules, same axioms. 142 exported instances. 3,007 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python -m unittest discover -s tools -p 'test_upper_quarter.py'` | 10 guard tests pass. | |
| `python tools/verify_lean_sources.py` | 1,409 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added
seven entries to `tools/definition_lock.json`: the two statement
definitions, `quarterWeight`, `bandBot`, `bandTop`, `bandCoef` and `bandStep`.
No existing entry changed. The run recorded here is a later one without that
flag.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The frozen
[`BlindUpper`](../../lean/ThresholdHC/BlindUpper/Specification.lean) targets
with $512$, and the targets of the earlier stages ($119$, $45$, $36$, $27$,
$19$, $17$ and $15$), are unchanged. The v6 paper states $15$.

The [numerical study](../../research/2026-11-18-upper-constant/README.md)
puts the actual worst ratio of the single-level estimator near $7.6$. It does
not compute the mixture. Its route table gives sharp per-gap constants of about
$2.9$ for the call second moment and about $2.8$ to $3.6$ for the call cost,
against $13/2$ and $11/2$ here. Below the split the disagreement bound is one
quarter plus the drift terms, about $0.3$ to $0.6$. The budget mixture costs a
factor $9/2$ where a batch of size $B/4$ would cost $4$.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
