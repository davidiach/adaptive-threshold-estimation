# RMS upper constant 45: library audit

The [previous record](../upper-constant-20261118/README.md) gave the
constant $119$ for the RMS law's upper bound, using the existing per-level
bounds of the distribution-blind estimator. A sharper bound on one of them,
the expected number of flips of each early-stopping classifier, gives $45$.
The audit runs below were made when the proof was added, at commit
[`e7e58dda97a5fda4b9c6fbe1a48efc75dfea0892`](https://github.com/davidiach/adaptive-threshold-estimation/commit/e7e58dda97a5fda4b9c6fbe1a48efc75dfea0892).

## Statements

[`lean/ThresholdHC/UpperWork/Specification.lean`](../../lean/ThresholdHC/UpperWork/Specification.lean)
states two targets against the original experiment, budget, risk and
modulus definitions, with $\omega_\mu(h)=\int\min(1,h/d)\,\mu(dd)$:

| Target | Statement |
|---|---|
| `blind_upper_45` | One budget-indexed family, chosen before the gap law, keeps the uniform expected-work budget $B$ and has RMS risk at most $45\,\omega_\mu(B^{-1/2})$ for every gap law and every $B\ge1$. |
| `minimax_upper_45` | $R_\mu(B)\le45\,\omega_\mu(B^{-1/2})$ for every gap law and every $B\ge1$. |

With the sharp lower constant $1/6$, the two sides of the RMS law are now a
factor $270$ apart, in place of $714$. The specification was written after
the proof; it is pinned by hash from this audit onward.

## Where 119 became 45

The family is again `budgetEstimator` of
[`BlindUpper`](../../lean/ThresholdHC/BlindUpper/Full.lean), unchanged.
Each call runs early-stopping classifiers with caps $N=2^l$. The cap-$N$
classifier looks at its running mean after $n=1,2,4,\dots$ flips. It passes
the check at $n$ only if the mean stays within
$t_n=\sqrt{(1+\log(N/n))/n}$ of one half, and its expected number of flips
is $1+\sum_{n<N}n\,\Pr(\text{it passes the check at }n)$, summed over dyadic
$n$. The frozen Tier 2 proof bounds each probability by
$e^{-nd^2/2}$, plus $1$ when $d\le2t_n$. That gives at most
$17\,d^{-2}(1+\log(Nd^2))$ flips when $Nd^2\ge1$.

**Per level.** [`Survival.lean`](../../lean/ThresholdHC/UpperWork/Survival.lean)
applies Hoeffding's inequality at the gap minus the threshold: the
probability is at most $e^{-2n(d-t_n)^2}$ when $t_n\le d$. Let
$u=1+\log(Nd^2)$ and $s=nd^2/u$. Every check with $s>1$ has $t_n\le d$,
and its term is at most $(u/d^2)\,s\,e^{-2(\sqrt s-1)^2}$.
[`Dyadic.lean`](../../lean/ThresholdHC/UpperWork/Dyadic.lean) sums the
terms. Let $s_*\in(1,2]$ be the first dyadic ratio above $1$. The checks
below it contribute their caps, which add up to $s_*u/d^2-1$ and cancel the
leading $1$. The others contribute the terms at $s_*,2s_*,4s_*,\dots$.
`offset_sum_le` bounds $s+\sum_j 2^js\,e^{-2(\sqrt{2^js}-1)^2}$ by $49/10$
for every $s\in(1,2]$. It splits $(1,2]$ at $7/6$, $7/5$ and $5/3$. On each
piece it bounds the first four terms by monotonicity and an eight-term Taylor
lower bound of the exponential, and the remaining terms by $1/(10t)$ at
ratio $t\ge16$. Hence at most $\tfrac{49}{10}\,d^{-2}(1+\log(Nd^2))$ flips
when $Nd^2\ge1$, for coins of either sign.

**Over levels.** [`LevelSum.lean`](../../lean/ThresholdHC/UpperWork/LevelSum.lean)
sums $p_l$ times the expected flips at level $l$, with $p_l=(1-r)r^l$ and
$r=2^{-1/2}$. Levels with $2^ld^2\le32$ are bounded by their caps, and the
others by the per-level bound. Let $m$ be the last level of the first kind and
$q^2=2^md^2\in(16,32]$. The first part is then at most $q/d$, and the
second, an arithmetico-geometric series, at most $A/(qd)$ with
$A=\tfrac{49}{10}\,r\bigl(1+5\log2+\log2/(1-r)\bigr)\approx23.67$. Since
$4q\le A$, the sum is at most $(4+A/4)/d\le\tfrac{248}{25}/d$. The level sums
of [`Uniform713/Series.lean`](../../lean/ThresholdHC/Uniform713/Series.lean)
gave $(17/7)\cdot31=527/7$.

**The rest of the chain.** [`Moments.lean`](../../lean/ThresholdHC/UpperWork/Moments.lean),
[`Batch.lean`](../../lean/ThresholdHC/UpperWork/Batch.lean) and
[`Full.lean`](../../lean/ThresholdHC/UpperWork/Full.lean) repeat the steps
of `UpperConstant` with the call cost $248/25$ and its call second moment
$23$. The padded cost is at most $273/25$. The batch mean-square error is
at most $1+23\cdot273/25=6304/25$ times $\omega_\mu(N^{-1/2})^2$. The
level RMS is at most $\tfrac{397}{25}\,\omega_\mu(N^{-1/2})$, since
$6304/25\le(397/25)^2$. The budget factor $17/6$ then gives
$\tfrac{397}{25}\cdot\tfrac{17}{6}=\tfrac{6749}{150}<45$.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_upper_work.py --replay --jobs 3` | 11 exact statements and 36 transitive axiom reports over 7 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 7 modules replayed through the independent kernel checker. | [upper-work-audit.log](upper-work-audit.log) |
| `python tools/verify_project_axioms.py` | 15,669 constants (12,564 theorems) in 1,360 modules, same axioms. 141 exported instances. 2,971 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python -m unittest discover -s tools -p 'test_upper_work.py'` | 10 guard tests pass. | |
| `python tools/verify_lean_sources.py` | 1,361 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added
four definitions to `tools/definition_lock.json`: the two statements, the
dyadic term `bump` and the survival bound `survivalBound`. No existing entry
changed. The run recorded here is the later one without that flag.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The frozen
[`BlindUpper`](../../lean/ThresholdHC/BlindUpper/Specification.lean) targets
with $512$ and the [`UpperConstant`](../../lean/ThresholdHC/UpperConstant/Specification.lean)
targets with $119$ are unchanged. The v6 paper still states $512$.

The [numerical study](../../research/2026-11-18-upper-constant/README.md)
puts the actual worst ratio of this estimator near $7.6$. Most of the
remaining slack is in the call second moment $23$. It rests on the bound
$\min\{1,3/x^2\}$ on the probability that two consecutive classifiers
disagree, where the exact computation gives at most $0.25$ and at most
$0.115/x^2$.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
