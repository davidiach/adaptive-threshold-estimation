# RMS upper constant 119: library audit

The RMS law's upper bound held with the constant $512$. The same
distribution-blind estimator, with the same analysis kept sharper, gives
$119$. The audit runs below were made when the proof was added, at commit
[`eaa11e98367b97a8c4f74611ca8fc59a8e1fa401`](https://github.com/davidiach/adaptive-threshold-estimation/commit/eaa11e98367b97a8c4f74611ca8fc59a8e1fa401).

## Statements

[`lean/ThresholdHC/UpperConstant/Specification.lean`](../../lean/ThresholdHC/UpperConstant/Specification.lean)
states two targets against the original experiment, budget, risk and
modulus definitions, with $\omega_\mu(h)=\int\min(1,h/d)\,\mu(dd)$:

| Target | Statement |
|---|---|
| `blind_upper_119` | One budget-indexed family, chosen before the gap law, keeps the uniform expected-work budget $B$ and has RMS risk at most $119\,\omega_\mu(B^{-1/2})$ for every gap law and every $B\ge1$. |
| `minimax_upper_119` | $R_\mu(B)\le119\,\omega_\mu(B^{-1/2})$ for every gap law and every $B\ge1$. |

With the sharp lower constant $1/6$, the two sides of the RMS law are now a
factor $714$ apart, in place of $3072$. The specification was written after
the proof; it is pinned by hash from this audit onward.

## Where 512 became 119

The family is `budgetEstimator` of
[`BlindUpper`](../../lean/ThresholdHC/BlindUpper/Full.lean), unchanged. Its
proof bounds the second moment and the expected cost of one call by
$85\,A$ and $149\,A$, with $A=\mathbb E_\mu\min\{N^{1/2},D^{-1}\}$, and then
the calibrated batch's mean-square error by
$1+85\cdot150=12751$ times $\omega_\mu(N^{-1/2})^2$. Its final step compares
$\omega_\mu(N^{-1/2})$ with $\omega_\mu(B^{-1/2})$ by the factor $4$ and
rounds $\sqrt{12751}$ up to $128$.

The library already proved the two level sums with smaller constants:
$23$ for the second moment and $(17/7)\cdot31=527/7$ for the cost
(`sum_secondMomentEnvelope_lt` and `sum_weightedWorkEnvelope_lt` in
[`Uniform713/Series.lean`](../../lean/ThresholdHC/Uniform713/Series.lean)).
The proofs of the frozen Tier 2 targets weaken them to $85$ and $149$.
[`Moments.lean`](../../lean/ThresholdHC/UpperConstant/Moments.lean) keeps
the sharper constants. [`Batch.lean`](../../lean/ThresholdHC/UpperConstant/Batch.lean)
carries them through the population, call and padded-cost bounds to a
mean-square error of $1+23\cdot534/7=12289/7$ times
$\omega_\mu(N^{-1/2})^2$. [`Full.lean`](../../lean/ThresholdHC/UpperConstant/Full.lean)
takes the square root, $\sqrt{12289/7}<42$, and compares the moduli with
the factor $17/6$: the dyadic level satisfies $B<8\cdot2^L$, and
$(17/6)^2\ge8$. Then $42\cdot17/6=119$.

No new probabilistic estimate is involved. The per-level bounds on the
classifiers are the existing ones.

## Runs

| Command | Outcome | Log |
|---|---|---|
| `python tools/verify_upper_constant.py --replay --jobs 3` | 7 exact statements and 22 transitive axiom reports over 4 registered modules, all within `propext`, `Classical.choice` and `Quot.sound`. All 4 modules replayed through the independent kernel checker. | [upper-constant-audit.log](upper-constant-audit.log) |
| `python tools/verify_project_axioms.py` | 15,592 constants (12,491 theorems) in 1,353 modules, same axioms. 141 exported instances. 2,967 locked definition fingerprints. | [project-audit.log](project-audit.log) |
| `python -m unittest discover -s tools -p 'test_upper_constant.py'` | 10 guard tests pass. | |
| `python tools/verify_lean_sources.py` | 1,354 Lean sources, no proof escapes. | |

The whole-project audit was first run with `--add-definitions`. It added
the two statement definitions to `tools/definition_lock.json`. No existing
entry changed. The run recorded here is the later one without that flag.

## Scope

These audits check that the stated types are proved and which axioms the
proofs use. The frozen
[`BlindUpper`](../../lean/ThresholdHC/BlindUpper/Specification.lean) targets
with $512$ are unchanged, and the v6 paper still states $512$.

The [numerical study](../../research/2026-11-18-upper-constant/README.md)
puts the actual worst ratio of this estimator near $7.6$. The remaining
slack is in the per-level bounds: the probability that two consecutive
classifiers disagree is bounded by $\min\{1,3/x^2\}$, where it is at most
$0.25$ and at most $0.115/x^2$ in the exact computation. The expected flips
are bounded by $17$ times the work envelope, where they are at most $1.26$
times it.

[SHA256SUMS](SHA256SUMS) identifies the files of this record.
