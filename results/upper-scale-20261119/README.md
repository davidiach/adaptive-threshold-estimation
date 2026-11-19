# RMS upper constant 12: library audit

The [previous record](../upper-quarter-20261119/README.md) gave the constant
$13$ for the RMS law's upper bound with a distribution-blind mixture of two
budget levels. A sharper bound on the padded call cost, and a calibration at
the scale $B/4$ in place of the mixture, give $12$. The audit runs below were
made at commit
[`2cf3ec0d01f0c713c2e56a7b75ad84a357a2335d`](https://github.com/davidiach/adaptive-threshold-estimation/commit/2cf3ec0d01f0c713c2e56a7b75ad84a357a2335d),
which adds the audit tool to the Lean commit
[`eb9f1a19f59d7afe6145fa91b150321f49a2a1ef`](https://github.com/davidiach/adaptive-threshold-estimation/commit/eb9f1a19f59d7afe6145fa91b150321f49a2a1ef).

## Statements

[`lean/ThresholdHC/UpperScale/Specification.lean`](../../lean/ThresholdHC/UpperScale/Specification.lean)
states two targets against the original experiment, budget, risk and
modulus definitions, with $\omega_\mu(h)=\int\min(1,h/d)\,\mu(dd)$:

| Target | Statement |
|---|---|
| `blind_upper_12` | One budget-indexed family, chosen before the gap law, keeps the uniform expected-work budget $B$ and has RMS risk at most $12\,\omega_\mu(B^{-1/2})$ for every gap law and every $B\ge1$. |
| `minimax_upper_12` | $R_\mu(B)\le12\,\omega_\mu(B^{-1/2})$ for every gap law and every $B\ge1$. |

With the sharp lower constant $1/6$, the two sides of the RMS law are now a
factor $72$ apart, in place of $78$. The specification was written after the
proof; it is pinned by hash from this audit onward. The v6 paper still states
$15$, in Appendix AB.

## Where 13 became 12

**Call cost.** The padded call cost of `UpperCost` is a level sum of survival
probabilities. Grouped by the difference $j+1$ of the level and the check,
each group follows one dyadic grid with threshold scale
$v_j=1+(j+1)\log2$ and is at most $\sqrt{v_j}$ times an offset bound $C_j$.
`UpperCost` takes $C_0=89/20$, $C_j=17/4$ for $j\ge1$ and
$\sqrt v\le(v+4)/4$, which gives $11/2$. The offset sum decreases as $v$
grows: [`UpperCallCost/Offset.lean`](../../lean/ThresholdHC/UpperCallCost/Offset.lean)
bounds it by $399/100$ for $v\ge307/100$, which covers $j\ge2$
(`offset_le_far`, 29 pieces chosen and checked in exact rational arithmetic by
a script and emitted as one Lean lemma each).
[`LevelSum.lean`](../../lean/ThresholdHC/UpperCallCost/LevelSum.lean) bounds
$\sqrt{v_j}$ one by one for $j<8$ and by $(v_j+9)/6$ beyond, so the weighted
sum of the offsets is at most $26/5$ (`callCost_constant_le`; the rational
bound in the proof is about $5.185$). The
padded call cost is then at most $\tfrac{26}{5}\min(\sqrt N,1/d)$, and at most
$\tfrac{26}{5}\min(\sqrt N,1/d)-\tfrac{21}{5}\sqrt N$ when $Nd^2\le1$
(`padded_regime_le`, `paddedCutoff_work_upper`).

**Calibration scale.** The batch machine of
[`BlindUpper`](../../lean/ThresholdHC/BlindUpper/BatchMachine.lean) at level
$L$ marks a call of padded cost $C$ when its uniform seed mark $u$ satisfies
$u<C/2^L$; the calibration then has scale $2^L$, and the machine uses
$4\cdot2^L$ flips less the mean cost. Run on a seed whose marks are multiplied
by $t\ge1$, the same machine marks the call when $u<C/(t\,2^L)$
(`callMark_scale`). With the identities of `BlindUpper.ActualBatch` for the
scaled seed and the law of the seed,
[`UpperScale/Seed.lean`](../../lean/ThresholdHC/UpperScale/Seed.lean) shows
that the machine realizes the calibration at scale $t\,2^L$: it keeps the
budget $4t\,2^L$ (`scaled_uniformBudget`), and its squared risk is the
calibrated mean-square error at that scale (`scaled_squaredRisk_eq`).

**Batch.** Let $A$ be the average call scale and $G$ the average regime
term over the gap law. With the second moment $\tfrac{13}{2}A+\tfrac{129}{25}G$ of
`UpperQuarter` and the cost $\tfrac{26}{5}A-\tfrac{21}{5}G$, the variance
times the cost is at most $\tfrac{169}{5}A^2$, because
$\tfrac{129}{25}\cdot\tfrac{26}{5}\le\tfrac{13}{2}\cdot\tfrac{21}{5}$
(`call_variance_cost_le`). So the mean-square error at scale $t\,2^L$ is at
most $(1+\tfrac{169}{5t})\,\omega(2^{-L/2})^2$
([`Batch.lean`](../../lean/ThresholdHC/UpperScale/Batch.lean),
`scaledBatch_mse`).

**Family.** For $B\ge4$, [`Full.lean`](../../lean/ThresholdHC/UpperScale/Full.lean)
runs the level $L$ with $4\cdot2^L\le B<8\cdot2^L$ at scale $B/4$, so
$t=B/(4\cdot2^L)\in[1,2)$ and the family uses the whole budget without the
two-level mixture. Since $2^L\omega(2^{-L/2})^2\le B\,\omega(B^{-1/2})^2$, the
mean-square error is at most
$4(t+\tfrac{169}{5})\,\omega(B^{-1/2})^2\le\tfrac{716}{5}\,\omega(B^{-1/2})^2$,
and $716/5\le12^2$ (`scaledFamily_maximalRMSRisk`). Below $B=4$ the family is
the idle estimator of `BlindUpper`. The two-level mixture with the same bounds
would give $\sqrt{(9/2)\cdot174/5}\approx12.5$.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_upper_scale.py --replay --jobs 3` | 14 exact statements and 90 transitive axiom reports over 8 registered modules in `UpperCallCost` and `UpperScale`, all within `propext`, `Classical.choice` and `Quot.sound`. All 8 modules replayed through the independent kernel checker. | [upper-scale-audit.log](upper-scale-audit.log) |
| `python tools/verify_project_axioms.py` | 16,368 constants (13,212 theorems) in 1,416 modules, same axioms. 142 exported instances. 3,020 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python -m unittest discover -s tools -p 'test_upper_scale.py'` | 11 guard tests pass. | |
| `python tools/verify_lean_sources.py` | 1,417 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added
thirteen entries to `tools/definition_lock.json`: the two statement
definitions and `scaleRatio`, `calScale`, `scaledMark`, `scaleMarks`,
`scaleState`, `scaleSeed`, `scaledEstimator`, `scaledBatchOutput`,
`scaledBatchWork`, `budgetRatio` and `scaledFamily`. No existing entry
changed. The run recorded here is a later one without that flag.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The frozen
[`BlindUpper`](../../lean/ThresholdHC/BlindUpper/Specification.lean) targets
with $512$, and the targets of the earlier stages ($119$, $45$, $36$, $27$,
$19$, $17$, $15$ and $13$), are unchanged. The batch machine of `BlindUpper`
is used as it is; only its seed law is scaled. The v6 paper states $15$.

The [numerical study](../../research/2026-11-18-upper-constant/README.md)
puts the actual worst ratio of the single-level estimator near $7.6$. It does
not compute the family above. Its route table gives sharp per-gap constants
of about $2.9$ for the call second moment and about $2.8$ to $3.6$ for the
call cost, against $13/2$ and $26/5$ here. The calibration at scale $B/4$
costs the factor $4$, and the bias of the dyadic level $L$ is at most $t\le2$
times the squared modulus at that scale.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
