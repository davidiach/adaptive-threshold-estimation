# RMS upper constant 15: library audit

The [previous record](../upper-disagreement-20261119/README.md) gave the
constant $17$ for the RMS law's upper bound with a distribution-blind mixture
of two budget levels. A sign-change bound on the disagreement of consecutive
classifiers below the cap scale gives $15$ for the same mixture. The audit runs
below were made when the proof was added, at commit
[`ac9e4ae6e8d8c266bab05140dacc6abfdaacb04d`](https://github.com/davidiach/adaptive-threshold-estimation/commit/ac9e4ae6e8d8c266bab05140dacc6abfdaacb04d).

## Statements

[`lean/ThresholdHC/UpperSign/Specification.lean`](../../lean/ThresholdHC/UpperSign/Specification.lean)
states two targets against the original experiment, budget, risk and
modulus definitions, with $\omega_\mu(h)=\int\min(1,h/d)\,\mu(dd)$:

| Target | Statement |
|---|---|
| `blind_upper_15` | One budget-indexed family, chosen before the gap law, keeps the uniform expected-work budget $B$ and has RMS risk at most $15\,\omega_\mu(B^{-1/2})$ for every gap law and every $B\ge1$. |
| `minimax_upper_15` | $R_\mu(B)\le15\,\omega_\mu(B^{-1/2})$ for every gap law and every $B\ge1$. |

With the sharp lower constant $1/6$, the two sides of the RMS law are now a
factor $90$ apart, in place of $102$. The specification was written after the
proof; it is pinned by hash from this audit onward.

## Where 17 became 15

The family is `budgetMixture` of
[`UpperMixture`](../../lean/ThresholdHC/UpperMixture/Full.lean), unchanged.
The [previous record](../upper-disagreement-20261119/README.md) bounded the
disagreement of consecutive classifiers by one at the levels with
$x=2^ld^2<12/25$. Those levels carried most of the call second moment $57/5$.

**Sign change.** [`SignChange.lean`](../../lean/ThresholdHC/UpperSign/SignChange.lean)
counts the successes $N_1$ among the first $n=2m$ flips and $N_2$ among the
next $n$. The majority votes after $n$ and $2n$ flips are $m<N_1$ and
$2m<N_1+N_2$. They differ only if $m<N_1$ and $N_2<m$, or $N_1\le m$ and
$m<N_2$. The two counts are independent (`successes_indep`, from the
independence of the flips) and have the same law (`successes_law`, from the
shift of the tape, which preserves its law). So with $a=\Pr(m<N_1)$ the
votes differ with probability at most $a(1-a)+(1-a)a\le\tfrac12$ for every
coin (`count_signChange_le`).

**Early stops.** [`EarlyStop.lean`](../../lean/ThresholdHC/UpperSign/EarlyStop.lean)
shows that if the cap-$2^L$ classifier runs to its cap, the cap-$2^{L+1}$
classifier agrees with it unless those votes differ (`decision_ne_imp`).
The smaller classifier stops early at check $k$ only if the running mean is
more than its threshold from one half. For a coin with gap $d$, Hoeffding's
inequality bounds that by the drift term `driftBound` in the direction of the
drift and by the early-stopping error terms of `stopError` against it
(`early_positive`, `early_negative`). Past the first level, consecutive
classifiers on the tape disagree with probability at most one half plus that
early-stop bound `earlyBound` (`disagree_tape_le`).

**Drift steps.** [`Drift.lean`](../../lean/ThresholdHC/UpperSign/Drift.lean)
evaluates the drift terms below the split. With $J=L-k$ and $v_J=1+J\log2$, the
term at check $k$ is $\exp(-2(\sqrt{v_J}-\sqrt y)^2)$ with $y=2^kd^2$, which
increases with $y$ (`driftSum_le`). For $2^Ld^2\le(3/8)/2^m$, $m=0,\dots,4$,
the first six terms are bounded with rational bounds and an eight-term Taylor
sum, and the rest by a geometric tail (`driftSeries_le_0` to
`driftSeries_le_4`).

**Grid.** [`Grid.lean`](../../lean/ThresholdHC/UpperSign/Grid.lean) weights
each level by `signWeight` (`sign_grid_le`):

- from $x=3/4$ on, the cap part $e^{-2x}+e^{-x}$;
- below it, one half plus the drift bounds of the smaller classifier, at most
  `stepE i` at the $(i+1)$-th level below the first grid point
  (`drift_step_le`);
- one at the first two levels.

The halves add up to $(1+\sqrt2)/2$ exactly, and the first two levels are
covered by the halves of the geometric extension below them. So the levels
below the split add at most $\tfrac{1613}{1000}\sqrt s$ for the first grid
point $s\in[3/4,3/2]$ (`below_coef_le`). With the cap terms above it,
[`Offset.lean`](../../lean/ThresholdHC/UpperSign/Offset.lean) bounds the
weighted grid sum by $247/100$, with 14 pieces (`sign_offset_le`).

**Level sum and chain.** [`Increment.lean`](../../lean/ThresholdHC/UpperSign/Increment.lean)
bounds the squared increment at level $l$ by one and by `signWeight` plus the
early-stopping terms of both classifiers (`sign_increment_le`).
[`LevelSum.lean`](../../lean/ThresholdHC/UpperSign/LevelSum.lean) gives $d$
times the second moment at most
$(2+\sqrt2)\cdot\tfrac{247}{100}+\tfrac{41}{100}\le\tfrac{89}{10}$. With the
regime term of `UpperDisagreement`, the second moment is at most
$\tfrac{89}{10}\min(\sqrt N,1/d)+\tfrac{69}{25}B$ (`sign_levelSum_le`). Since
$\tfrac{69}{25}\cdot\tfrac{11}{2}\le\tfrac{89}{10}\cdot\tfrac92$,
[`Batch.lean`](../../lean/ThresholdHC/UpperSign/Batch.lean) bounds the batch
mean-square error by $\tfrac{999}{20}=1+\tfrac{89}{10}\cdot\tfrac{11}{2}$ times
$\omega_\mu(N^{-1/2})^2$. [`Full.lean`](../../lean/ThresholdHC/UpperSign/Full.lean)
gives $\tfrac92\cdot\tfrac{999}{20}=\tfrac{8991}{40}\le15^2$.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_upper_sign.py --replay --jobs 3` | 13 exact statements and 67 transitive axiom reports over 11 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 11 modules replayed through the independent kernel checker. | [upper-sign-audit.log](upper-sign-audit.log) |
| `python tools/verify_project_axioms.py` | 16,069 constants (12,933 theorems) in 1,396 modules, same axioms. 142 exported instances. 3,000 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python -m unittest discover -s tools -p 'test_upper_sign.py'` | 10 guard tests pass. | |
| `python tools/verify_lean_sources.py` | 1,397 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added
eight entries to `tools/definition_lock.json`: the two statement
definitions, `successes`, `driftBound`, `earlyBound`, `driftTerm`, `stepE` and
`signWeight`. No existing entry changed. The run recorded here is a later one
without that flag.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The frozen
[`BlindUpper`](../../lean/ThresholdHC/BlindUpper/Specification.lean) targets
with $512$, and the targets of the earlier stages ($119$, $45$, $36$, $27$,
$19$ and $17$), are unchanged. The v6 paper still states $512$.

The [numerical study](../../research/2026-11-18-upper-constant/README.md)
puts the actual worst ratio of the single-level estimator near $7.6$. It does
not compute the mixture. Its route table gives sharp per-gap constants of about
$2.9$ for the call second moment and about $2.8$ to $3.6$ for the call cost,
against $89/10$ and $11/2$ here. Below the split the disagreement bound is
about $0.6$ to $0.8$, where the exact disagreement probability is at most
$0.25$. The budget mixture costs a factor $9/2$ where a batch of size $B/4$
would cost $4$.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
