# RMS upper constant 19: library audit

The [previous record](../upper-mixture-20261118/README.md) gave the constant
$27$ for the RMS law's upper bound with a distribution-blind mixture of two
budget levels. A sharper bound on the padded cost of one call gives $19$ for
the same mixture. The audit runs below were made when the proof was added, at
commit
[`e0b1c1cf9517e654e60457ab382be55cdfb05592`](https://github.com/davidiach/adaptive-threshold-estimation/commit/e0b1c1cf9517e654e60457ab382be55cdfb05592).

## Statements

[`lean/ThresholdHC/UpperCost/Specification.lean`](../../lean/ThresholdHC/UpperCost/Specification.lean)
states two targets against the original experiment, budget, risk and
modulus definitions, with $\omega_\mu(h)=\int\min(1,h/d)\,\mu(dd)$:

| Target | Statement |
|---|---|
| `blind_upper_19` | One budget-indexed family, chosen before the gap law, keeps the uniform expected-work budget $B$ and has RMS risk at most $19\,\omega_\mu(B^{-1/2})$ for every gap law and every $B\ge1$. |
| `minimax_upper_19` | $R_\mu(B)\le19\,\omega_\mu(B^{-1/2})$ for every gap law and every $B\ge1$. |

With the sharp lower constant $1/6$, the two sides of the RMS law are now a
factor $114$ apart, in place of $162$. The specification was written after
the proof; it is pinned by hash from this audit onward.

## Where 27 became 19

The family is `budgetMixture` of
[`UpperMixture`](../../lean/ThresholdHC/UpperMixture/Full.lean), unchanged.
A call at level $l\le L$ runs the cap-$2^l$ early-stopping classifier, and a
call above $L$ takes one padding flip. The previous records bounded the
padded call cost by $\tfrac{273}{25}\min(\sqrt N,1/d)$ with $N=2^L$: the
cost $248/25$ of [`UpperWork`](../upper-work-20261118/README.md) plus one
for the padding.

**Survival by level difference.** The check with $n=2^k$ flips of the
cap-$2^l$ classifier survives with probability at most
$\exp(-2n(d-t)^2)$ once its threshold $t$ is below the gap $d$
(`UpperWork.survivalBound`). Its threshold is $t^2=(1+(l-k)\log2)/n$, so it
depends on $l$ and $k$ only through $j=l-k$, and it is below $d$ exactly
when $2^kd^2\ge v_j=1+j\log2$ (`survivalBound_eq_grid`). The
[`UpperWork`](../upper-work-20261118/README.md) bound instead used
$t\le\sqrt{u/n}$ with $u=1+\log(2^ld^2)$ and dropped $u$ from the exponent.

**Reordering.** [`LevelSum.lean`](../../lean/ThresholdHC/UpperCost/LevelSum.lean)
writes the padded call cost as a sum over pairs $k<l\le L$ and reorders it by
$j$ (`sum_triangle`). The pairs with a fixed $j$ carry the weight
$(1-r)r^j$, with $r=2^{-1/2}$, and follow one dyadic grid of $2^kd^2/v_j$.

**One grid.** [`Grid.lean`](../../lean/ThresholdHC/UpperCost/Grid.lean)
bounds the sum along one grid (`grid_sum_le`). The checks below the scale
$v$ add a geometric sum. Extended below $k=0$, it equals
$(1+\sqrt2)\sqrt{sv}$ for the first grid ratio $s\in[1,2]$ at or above one.
The checks from the scale on add $\sqrt v\,\sqrt t\,e^{-2v(\sqrt t-1)^2}$ at
the ratios $t=2^is$. So the sum is at most $\sqrt v\,C$ whenever $C$ bounds
the offset sum $(1+\sqrt2)\sqrt s+\sum_i\sqrt{2^is}\,e^{-2v(\sqrt{2^is}-1)^2}$.

**Offset bounds.** [`Offset.lean`](../../lean/ThresholdHC/UpperCost/Offset.lean)
proves $C=89/20$ for $v\ge169/100$, which covers $j=1$ since
$1+\log2>1.69$, and $C=17/4$ for $v\ge119/50$, which covers $j\ge2$. Each
proof splits $[1,2]$ into pieces, 11 and 9 of them. It bounds the first four
doubled terms on each piece by monotonicity and an eight-term Taylor sum, and
the rest by $1/80$.

**The constant.** With $\sqrt{v_j}\le(v_j+4)/4$ for $j\ge2$, the weighted sum
of $\sqrt{v_j}\,C$ is at most $11/2$ (`cost_constant_le`). The geometric
extensions below $k=0$ add $d(1+r)(1-r^L)\ge d$ once $L\ge3$. That covers the
levels' baseline flip and the padding flip, whose probabilities add to one.
So $d$ times the padded call cost is at most $11/2$ whenever $2^Ld^2>16$
(`padded_levelSum_le`). Otherwise the cap bound $\sqrt N$ suffices. In both
cases the padded call cost is at most $\tfrac{11}{2}\min(\sqrt N,1/d)$.

**Population and batch.** [`Moments.lean`](../../lean/ThresholdHC/UpperCost/Moments.lean)
and [`Batch.lean`](../../lean/ThresholdHC/UpperCost/Batch.lean) apply this
per coin. They show that the padding flip has probability exactly $r^{L+1}$
under the call law (`levelTail_integral`), so the population padded cost is
at most $\tfrac{11}{2}\int\min(\sqrt N,1/d)\,\mu(dd)$
(`paddedCutoff_work_upper`). With the call second moment $72/5$ of
[`UpperMoment`](../upper-moment-20261118/README.md), the batch mean-square
error is at most $1+\tfrac{72}{5}\cdot\tfrac{11}{2}=\tfrac{401}{5}$ times
$\omega_\mu(N^{-1/2})^2$.

**The mixture.** [`Full.lean`](../../lean/ThresholdHC/UpperCost/Full.lean)
proves, for any batch factor $K$, that the budget mixture has RMS risk at most
$c\,\omega_\mu(B^{-1/2})$ whenever $\tfrac92K\le c^2$ and $c\ge1$
(`budgetMixture_risk_of_batch`). Since
$\tfrac92\cdot\tfrac{401}{5}=\tfrac{3609}{10}\le19^2$, the constant is $19$.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_upper_cost.py --replay --jobs 3` | 13 exact statements and 34 transitive axiom reports over 7 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 7 modules replayed through the independent kernel checker. | [upper-cost-audit.log](upper-cost-audit.log) |
| `python tools/verify_project_axioms.py` | 15,840 constants (12,722 theorems) in 1,376 modules, same axioms. 142 exported instances. 2,984 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python -m unittest discover -s tools -p 'test_upper_cost.py'` | 10 guard tests pass. | |
| `python tools/verify_lean_sources.py` | 1,377 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added
four entries to `tools/definition_lock.json`: the two statement definitions,
`tailTerm` and `gridSurvival`. No existing entry changed. The run recorded
here is a later one without that flag.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The frozen
[`BlindUpper`](../../lean/ThresholdHC/BlindUpper/Specification.lean) targets
with $512$, and the targets of
[`UpperConstant`](../../lean/ThresholdHC/UpperConstant/Specification.lean)
with $119$, [`UpperWork`](../../lean/ThresholdHC/UpperWork/Specification.lean)
with $45$, [`UpperMoment`](../../lean/ThresholdHC/UpperMoment/Specification.lean)
with $36$ and [`UpperMixture`](../../lean/ThresholdHC/UpperMixture/Specification.lean)
with $27$, are unchanged. The v6 paper still states $512$.

The [numerical study](../../research/2026-11-18-upper-constant/README.md)
puts the actual worst ratio of the single-level estimator near $7.6$. It does
not compute the mixture. Its route table gives sharp per-gap constants of
about $2.9$ for the call second moment and about $2.8$ to $3.6$ for the call
cost. Against these, $72/5$ now holds most of the remaining slack. It rests
on the disagreement bound $\min\{1,1.13/x^2\}$ for consecutive classifiers,
whose exact value is at most $0.25$ and $0.115/x^2$.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
