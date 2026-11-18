# RMS upper constant 36: library audit

The [previous record](../upper-work-20261118/README.md) gave the constant
$45$ for the RMS law's upper bound by sharpening the expected work of the
distribution-blind estimator. Sharpening its call second moment as well
gives $36$. The audit runs below were made when the proof was added, at
commit
[`LEAN_COMMIT`](https://github.com/davidiach/adaptive-threshold-estimation/commit/LEAN_COMMIT).

## Statements

[`lean/ThresholdHC/UpperMoment/Specification.lean`](../../lean/ThresholdHC/UpperMoment/Specification.lean)
states two targets against the original experiment, budget, risk and
modulus definitions, with $\omega_\mu(h)=\int\min(1,h/d)\,\mu(dd)$:

| Target | Statement |
|---|---|
| `blind_upper_36` | One budget-indexed family, chosen before the gap law, keeps the uniform expected-work budget $B$ and has RMS risk at most $36\,\omega_\mu(B^{-1/2})$ for every gap law and every $B\ge1$. |
| `minimax_upper_36` | $R_\mu(B)\le36\,\omega_\mu(B^{-1/2})$ for every gap law and every $B\ge1$. |

With the sharp lower constant $1/6$, the two sides of the RMS law are now a
factor $216$ apart, in place of $270$. The specification was written after
the proof; it is pinned by hash from this audit onward.

## Where 45 became 36

The family is again `budgetEstimator` of
[`BlindUpper`](../../lean/ThresholdHC/BlindUpper/Full.lean), unchanged. One
call at level $l$ returns $V=(Z_l-Z_{l-1})/p_l$, the difference of two
consecutive early-stopping classifiers divided by $p_l=(1-r)r^l$, with
$r=2^{-1/2}$. Its second moment is
$\sum_l\Pr(Z_l\ne Z_{l-1})/p_l$, summed over levels.

**Per level.** [`Disagreement.lean`](../../lean/ThresholdHC/UpperMoment/Disagreement.lean)
bounds the disagreement probability. Each classifier errs with probability
at most $\tfrac53e^{-2}/(Nd^2)^2$ at cap $N$
(`Tier2.Model.error_positive_bound`). Two consecutive classifiers disagree
only if one of them errs, and the earlier one has half the cap. So they
disagree with probability at most
$\tfrac{25}{3}e^{-2}/(Nd^2)^2\le\tfrac{113}{100}/(Nd^2)^2$, since
$e^2\ge7.3746$ by an eight-term Taylor sum. The frozen Tier 2 proof rounds
$\tfrac{25}{3}e^{-2}\approx1.128$ up to $3$.

**Over levels.** [`LevelSum.lean`](../../lean/ThresholdHC/UpperMoment/LevelSum.lean)
sums $\min\{1,\tfrac{113}{100}/(2^ld^2)^2\}/p_l$. Since
$1/p_l=(2+\sqrt2)\,\sqrt2^{\,l}$, levels with $2^ld^2\le1$ are bounded by
$1$, and together contribute exactly
$(6+4\sqrt2)\sqrt2^{\,m}-(4+3\sqrt2)$ for the last such level $m$. The rest
form a geometric series with ratio $\sqrt2/4$. With $q^2=2^md^2\in(1/2,1]$,
the two parts are at most $a\,q/d$ and $b/(q^3d)$, where
$a=6+4\sqrt2<11.657$ and
$b=\tfrac{113}{100}(2+\sqrt2)\tfrac{x}{1-x}<2.12$ with $x=\sqrt2/4$. For
$q\in[7/10,1]$, the quartic $\tfrac{72}{5}q^3-11.657\,q^4-2.12$ is
nonnegative: it equals a nonnegative chord plus
$(q-\tfrac7{10})(1-q)$ times a quadratic that is positive there. So the call
second moment is at most $\tfrac{72}{5}\min(\sqrt{2^L},1/d)$, in place of
$23$.

**The rest of the chain.** [`Moments.lean`](../../lean/ThresholdHC/UpperMoment/Moments.lean),
[`Batch.lean`](../../lean/ThresholdHC/UpperMoment/Batch.lean) and
[`Full.lean`](../../lean/ThresholdHC/UpperMoment/Full.lean) repeat the
steps of `UpperWork` with the second moment $72/5$ and its padded call cost
$273/25$. The batch mean-square error is at most
$1+\tfrac{72}{5}\cdot\tfrac{273}{25}=\tfrac{19781}{125}$ times
$\omega_\mu(N^{-1/2})^2$. The level RMS is at most
$\tfrac{63}{5}\,\omega_\mu(N^{-1/2})$, since $19781/125\le(63/5)^2$. The
budget factor $17/6$ then gives $\tfrac{63}{5}\cdot\tfrac{17}{6}=\tfrac{357}{10}<36$.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_upper_moment.py --replay --jobs 3` | 10 exact statements and 21 transitive axiom reports over 6 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 6 modules replayed through the independent kernel checker. | [upper-moment-audit.log](upper-moment-audit.log) |
| `python tools/verify_project_axioms.py` | PROJECT_SUMMARY | [project-audit.log](project-audit.log) |
| `python -m unittest discover -s tools -p 'test_upper_moment.py'` | 10 guard tests pass. | |
| `python tools/verify_lean_sources.py` | SOURCES_SUMMARY | |

The whole-project audit was first run with `--add-definitions`. It added
the two statement definitions to `tools/definition_lock.json`. No existing
entry changed. The run recorded here is the later one without that flag.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The frozen
[`BlindUpper`](../../lean/ThresholdHC/BlindUpper/Specification.lean) targets
with $512$, and the targets of
[`UpperConstant`](../../lean/ThresholdHC/UpperConstant/Specification.lean)
with $119$ and [`UpperWork`](../../lean/ThresholdHC/UpperWork/Specification.lean)
with $45$, are unchanged. The v6 paper still states $512$.

The [numerical study](../../research/2026-11-18-upper-constant/README.md)
puts the actual worst ratio of this estimator near $7.6$. The remaining
slack is in the per-level bounds themselves. The exact disagreement
probability is at most $0.25$ and at most $0.115/x^2$, against
$\min\{1,1.13/x^2\}$. The exact expected flips are at most $1.26$ times the
work envelope, against the bound $\tfrac{49}{10}\,d^{-2}(1+\log(Nd^2))$.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
