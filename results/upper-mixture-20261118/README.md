# RMS upper constant 27: library audit

The [previous record](../upper-moment-20261118/README.md) gave the constant
$36$ for the RMS law's upper bound with the distribution-blind estimator of
`BlindUpper`. That estimator runs a single dyadic level and can leave up to
half the budget unused. Mixing two consecutive levels so that the whole
budget is used gives $27$. The audit runs below were made when the proof was
added, at commit
[`3cd4f1d87fef58b38df0f44f63f3d21393ed61c7`](https://github.com/davidiach/adaptive-threshold-estimation/commit/3cd4f1d87fef58b38df0f44f63f3d21393ed61c7).

## Statements

[`lean/ThresholdHC/UpperMixture/Specification.lean`](../../lean/ThresholdHC/UpperMixture/Specification.lean)
states two targets against the original experiment, budget, risk and
modulus definitions, with $\omega_\mu(h)=\int\min(1,h/d)\,\mu(dd)$:

| Target | Statement |
|---|---|
| `blind_upper_27` | One budget-indexed family, chosen before the gap law, keeps the uniform expected-work budget $B$ and has RMS risk at most $27\,\omega_\mu(B^{-1/2})$ for every gap law and every $B\ge1$. |
| `minimax_upper_27` | $R_\mu(B)\le27\,\omega_\mu(B^{-1/2})$ for every gap law and every $B\ge1$. |

With the sharp lower constant $1/6$, the two sides of the RMS law are now a
factor $162$ apart, in place of $216$. The specification was written after
the proof; it is pinned by hash from this audit onward.

## Where 36 became 27

For a budget $B\ge4$, let $L$ be the level with $4\cdot2^L\le B<8\cdot2^L$.
The calibrated batch of `BlindUpper` at level $L$ costs at most $4\cdot2^L$
and, by the previous record, has mean-square error at most
$K\,\omega_\mu(2^{-L/2})^2$ with $K=19781/125$. The family of the previous
records runs that batch alone and pays for the unused budget with the factor
$17/6$.

**The mixture.** [`Mixture.lean`](../../lean/ThresholdHC/UpperMixture/Mixture.lean)
defines `mixEstimator p A₀ A₁`. Its random seed is a coin showing heads with
probability $p$ clipped to $[0,1]$, together with a seed of $A_0$. On heads it
runs $A_1$, on tails $A_0$. When the two estimators use the same seed law,
the simulation identities of the original experiment write the expected
work and the squared risk as integrals over the seed and the tapes, and the
coin splits each integral in two. So both are the same mixtures of the two
estimators' values (`mix_expectedWork`, `mix_squaredRisk`), for every gap
law and sign law. The calibrated batches of all levels share one seed law.

**The family.** [`Full.lean`](../../lean/ThresholdHC/UpperMixture/Full.lean)
defines `budgetMixture B`: for $B\ge4$ it mixes level $L$ and level $L+1$
with $p=B/(4\cdot2^L)-1\in[0,1]$; for $B<4$ it does no work. Its expected
work is at most $(1-p)\cdot4\cdot2^L+p\cdot8\cdot2^L=B$ under every sign law
(`budgetMixture_uniformBudget`). The modulus satisfies
$\omega_\mu(ch)\le c\,\omega_\mu(h)$ for $c\ge1$, so
$N\,\omega_\mu(N^{-1/2})^2\le B\,\omega_\mu(B^{-1/2})^2$ for $0<N\le B$
(`modulus_sq_scale`). With $B/2^L=4(1+p)$ and $B/2^{L+1}=2(1+p)$, the
mean-square error is at most

$$K\,\omega_\mu(B^{-1/2})^2\,\bigl(4(1+p)(1-p)+2(1+p)p\bigr)
=4(1+p)(1-p/2)\,K\,\omega_\mu(B^{-1/2})^2,$$

and $4(1+p)(1-p/2)\le9/2$, with equality at $p=1/2$. Since
$\tfrac92\cdot\tfrac{19781}{125}=\tfrac{178029}{250}\le27^2$, the RMS risk is
at most $27\,\omega_\mu(B^{-1/2})$. For $1\le B<4$ the estimator does no work,
its RMS risk is at most $1$, and $\omega_\mu(B^{-1/2})=1$
(`budgetMixture_maximalRMSRisk`).

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_upper_mixture.py --replay --jobs 3` | 8 exact statements and 26 transitive axiom reports over 3 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 3 modules replayed through the independent kernel checker. | [upper-mixture-audit.log](upper-mixture-audit.log) |
| `python tools/verify_project_axioms.py` | 15,769 constants (12,655 theorems) in 1,369 modules, same axioms. 142 exported instances. 2,980 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python -m unittest discover -s tools -p 'test_upper_mixture.py'` | 10 guard tests pass. | |
| `python tools/verify_lean_sources.py` | 1,370 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added
seven entries to `tools/definition_lock.json`: the two statement
definitions, `clip`, `coinLaw`, `mixEstimator`, `levelWeight` and
`budgetMixture`. No existing entry changed. The run recorded here is a
later one without that flag.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The frozen
[`BlindUpper`](../../lean/ThresholdHC/BlindUpper/Specification.lean) targets
with $512$, and the targets of
[`UpperConstant`](../../lean/ThresholdHC/UpperConstant/Specification.lean)
with $119$, [`UpperWork`](../../lean/ThresholdHC/UpperWork/Specification.lean)
with $45$ and [`UpperMoment`](../../lean/ThresholdHC/UpperMoment/Specification.lean)
with $36$, are unchanged. The v6 paper still states $512$.

The family here differs from the single-level estimator of the earlier
records only in the coin that picks the level. The
[numerical study](../../research/2026-11-18-upper-constant/README.md) puts
the actual worst ratio of the single-level estimator near $7.6$; it does not
compute the mixture. The per-level bounds behind $K$ are those of the
previous record, and they hold most of the remaining slack.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
