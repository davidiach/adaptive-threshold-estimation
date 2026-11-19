# RMS upper constant 17: library audit

The [previous record](../upper-cost-20261118/README.md) gave the constant
$19$ for the RMS law's upper bound with a distribution-blind mixture of two
budget levels. A sharper bound on the second moment of one call gives $17$ for
the same mixture. The audit runs below were made when the proof was added, at
commit
[`c026119b580ca451419b7cbe6cc4bdbac46387c8`](https://github.com/davidiach/adaptive-threshold-estimation/commit/c026119b580ca451419b7cbe6cc4bdbac46387c8).

## Statements

[`lean/ThresholdHC/UpperDisagreement/Specification.lean`](../../lean/ThresholdHC/UpperDisagreement/Specification.lean)
states two targets against the original experiment, budget, risk and
modulus definitions, with $\omega_\mu(h)=\int\min(1,h/d)\,\mu(dd)$:

| Target | Statement |
|---|---|
| `blind_upper_17` | One budget-indexed family, chosen before the gap law, keeps the uniform expected-work budget $B$ and has RMS risk at most $17\,\omega_\mu(B^{-1/2})$ for every gap law and every $B\ge1$. |
| `minimax_upper_17` | $R_\mu(B)\le17\,\omega_\mu(B^{-1/2})$ for every gap law and every $B\ge1$. |

With the sharp lower constant $1/6$, the two sides of the RMS law are now a
factor $102$ apart, in place of $114$. The specification was written after
the proof; it is pinned by hash from this audit onward.

## Where 19 became 17

The family is `budgetMixture` of
[`UpperMixture`](../../lean/ThresholdHC/UpperMixture/Full.lean), unchanged.
One call at level $l$ returns the difference of two consecutive
early-stopping classifiers divided by $p_l$. Its second moment is
$\sum_l\Pr(Z_l\ne Z_{l-1})/p_l$. The [`UpperMoment`](../upper-moment-20261118/README.md)
bound $\min\{1,\tfrac{113}{100}/x^2\}$, with $x=2^ld^2$, gave $72/5$ times
$\min(\sqrt N,1/d)$.

**Per level.** [`Increment.lean`](../../lean/ThresholdHC/UpperDisagreement/Increment.lean)
bounds the disagreement by the two classifiers' error union bounds
(`Tier2.Model.errorUnionBound`). Each is a cap term $e^{-2\cdot\mathrm{cap}\cdot d^2}$
plus early-stopping terms $\exp(-2n(d+t_n)^2)$ (`stopError`). At level $l$ the
two cap terms are $e^{-2x}$ and $e^{-x}$. The squared increment is therefore
at most one and at most `levelBound`. That bound is `capWeight x` plus the
early-stopping terms of both classifiers, where `capWeight x` is one below
$x=12/25$ and $e^{-2x}+e^{-x}$ from there on.

**Cap terms.** [`CapGrid.lean`](../../lean/ThresholdHC/UpperDisagreement/CapGrid.lean)
sums $\sqrt x\,$`capWeight x` along the dyadic grid of levels (`cap_grid_le`).
The levels below $12/25$ add a geometric sum, at most $(1+\sqrt2)\sqrt s$ for
the first grid point $s\in[12/25,24/25]$. The levels from $s$ on add
$\sqrt t\,(e^{-2t}+e^{-t})$ at $t=2^is$.
[`CapOffset.lean`](../../lean/ThresholdHC/UpperDisagreement/CapOffset.lean)
bounds the total by $321/100$ (`cap_offset_le`). It splits $[12/25,24/25]$
into 20 pieces, chosen and checked in exact rational arithmetic, and bounds
the first six doubled terms on each piece by monotonicity and an eight-term
Taylor sum, and the rest by $1/1000$.

**Early-stopping terms.** [`ErrorSum.lean`](../../lean/ThresholdHC/UpperDisagreement/ErrorSum.lean)
keeps the cross term that the frozen Tier 2 proof drops. At the check $k$ of
the cap-$2^l$ classifier, $n(d+t_n)^2=(\sqrt{2^kd^2}+\sqrt{v_j})^2$ with
$j=l-k$ and $v_j=1+j\log2$, which is at least
$v_j+2\sqrt{v_j}\sqrt{2^kd^2}$. Along a grid of ratio $\sqrt2$,
$\sum u\,e^{-cu}\le(2+\sqrt2)/c$, by a telescoping sum (`grid_exp_le`). The
early-stopping terms of both classifiers, weighted by $1/p_l$, add at most
$\tfrac{41}{100}/d$ (`stopError_levelSum_le`).

**Level sums and the regime term.** [`LevelSum.lean`](../../lean/ThresholdHC/UpperDisagreement/LevelSum.lean)
combines the two into $d$ times the second moment at most
$(2+\sqrt2)\cdot\tfrac{321}{100}+\tfrac{41}{100}\le\tfrac{57}{5}$. When
$2^Ld^2\le1$, bounding every level by one gives $(6+4\sqrt2)\sqrt N$ instead,
which exceeds $\tfrac{57}{5}\sqrt N$. But there the padded call cost is at most
$\sqrt N$, far below $\tfrac{11}{2}\sqrt N$. So both bounds carry a regime term
$B$, equal to $\sqrt N$ in that regime and zero outside it:

- the second moment is at most $\tfrac{57}{5}\min(\sqrt N,1/d)+\tfrac{13}{50}B$
  (`disagreement_levelSum_le`);
- the padded cost is at most $\tfrac{11}{2}\min(\sqrt N,1/d)-\tfrac92B$
  (`padded_regime_le`).

**Population and batch.** [`Moments.lean`](../../lean/ThresholdHC/UpperDisagreement/Moments.lean)
and [`Batch.lean`](../../lean/ThresholdHC/UpperDisagreement/Batch.lean)
average these over the gap law. With $A$ and $B$ the averages of
$\min(\sqrt N,1/d)$ and of the regime term, the variance times the padded cost
is at most $(\tfrac{57}{5}A+\tfrac{13}{50}B)(\tfrac{11}{2}A-\tfrac92B)$. That is at
most $\tfrac{627}{10}A^2$, because
$\tfrac{13}{50}\cdot\tfrac{11}{2}\le\tfrac{57}{5}\cdot\tfrac92$. The batch
mean-square error is then at most $\tfrac{637}{10}$ times
$\omega_\mu(N^{-1/2})^2$.

**The mixture.** [`Full.lean`](../../lean/ThresholdHC/UpperDisagreement/Full.lean)
applies `UpperCost.budgetMixture_risk_of_batch`:
$\tfrac92\cdot\tfrac{637}{10}=\tfrac{5733}{20}\le17^2$.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_upper_disagreement.py --replay --jobs 3` | 14 exact statements and 71 transitive axiom reports over 9 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 9 modules replayed through the independent kernel checker. | [upper-disagreement-audit.log](upper-disagreement-audit.log) |
| `python tools/verify_project_axioms.py` | 15,932 constants (12,806 theorems) in 1,385 modules, same axioms. 142 exported instances. 2,992 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python -m unittest discover -s tools -p 'test_upper_disagreement.py'` | 10 guard tests pass. | |
| `python tools/verify_lean_sources.py` | 1,386 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added
eight entries to `tools/definition_lock.json`: the two statement
definitions, `capTerm`, `capWeight`, `stopError`, `levelBound`, `regimeTerm`
and `gapRegime`. No existing entry changed. The run recorded here is a later
one without that flag.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The frozen
[`BlindUpper`](../../lean/ThresholdHC/BlindUpper/Specification.lean) targets
with $512$, and the targets of
[`UpperConstant`](../../lean/ThresholdHC/UpperConstant/Specification.lean)
($119$), [`UpperWork`](../../lean/ThresholdHC/UpperWork/Specification.lean)
($45$), [`UpperMoment`](../../lean/ThresholdHC/UpperMoment/Specification.lean)
($36$), [`UpperMixture`](../../lean/ThresholdHC/UpperMixture/Specification.lean)
($27$) and [`UpperCost`](../../lean/ThresholdHC/UpperCost/Specification.lean)
($19$), are unchanged. The v6 paper still states $512$.

The [numerical study](../../research/2026-11-18-upper-constant/README.md)
puts the actual worst ratio of the single-level estimator near $7.6$. It does
not compute the mixture. Its route table gives sharp per-gap constants of
about $2.9$ for the call second moment and about $2.8$ to $3.6$ for the call
cost. Most of the remaining slack in $57/5$ is in the levels below the split,
whose disagreement is bounded by one; the exact disagreement probability is
at most $0.25$.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
