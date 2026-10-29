# Tier 2: frozen targets and scorer v2

**Status: all 13 Tier 2 targets proved. Complete checkpoint: 121/121 on Windows and Linux.**
Proposed by Opus from the open items in [REPORT.md](REPORT.md); reviewed and integrated by Codex.
The approval and final verification record are in [FREEZE_LOG.md](../../FREEZE_LOG.md).

Checkpoint 001 proved I1–I4, I7, K3, and R1. Checkpoint 002 completes I5–I6
and K1–K2/K4–K5: 61/61 Tier 2 points and all 60/60 Tier 1 points. Full build
and both independent 46-target audits pass locally with the frozen statements
unchanged and only the three standard axioms. The independent
[Linux replay of `e6cbd9c`](https://github.com/davidiach/adaptive-threshold-estimation/actions/runs/40417194219)
also passes all 46 targets, 7 scalar lemmas, the complete 130-root 713 audit,
and the numerical and validation checks.

Tier 1 is complete (60/60, checkpoint `a485ad6`). Tier 2 adds 13 targets worth 61
points, covering results that were paper-only when the extension was approved:

- the stopped-transcript information bound behind the lower bound;
- Lemmas 6–7 as probability statements, not scalar inequalities;
- the rare-event optimizer.

It also folds the audit-exit guard into the frozen scorer.

The 713 constant is **not** a Tier 2 target. Astra's separate `Uniform713`
development (completed in commit `852690a`) already proves the stronger untruncated,
arbitrary-law theorem. See "The 713 track" below for its strengthened definition lock.

## What changes

| File | Frozen? | Change |
|---|---|---|
| `lean/ThresholdHC/Statements2.lean` | new, frozen | 13 target statements plus supporting definitions |
| `lean/ThresholdHC/Proofs/Tier2/*.lean` | no | three proof groups and supporting modules; all targets proved |
| `lean/ThresholdHC.lean` | frozen | imports Statements2 and the Tier 2 proof modules |
| `tools/targets.json` | frozen | `tier` field on every entry; 13 Tier 2 entries |
| `tools/score.py` | frozen | v2 validity rule and per-tier points; Statements2 exempt from the token scan |
| `tools/freeze.py` | frozen | Tier 2 and the 713 definition/guard locks added to the frozen list (21 files) |
| `tools/check_targets_numeric.py` | frozen | checks only `tier == 1`, so unknown Tier 2 names no longer fail it |
| `tools/check_targets2_numeric.py` | new, frozen | numeric truth checks for all 13 Tier 2 targets |
| `tools/verify_lean_checkpoint.py` | no | reads build modules from `targets.json` instead of a hard-coded list |
| `tools/verify_uniform713.py`, `tools/uniform713_targets.json` | newly frozen | checks the specification and all five local dependency files, including during the audit |
| `Uniform713/{Specification,Common,Concentration,Classifier,Estimator}.lean` | newly frozen | locks existing source bytes; `Statements.lean` was already frozen |
| `tools/test_validation.py` | no | failure-path regression tests for both validation fixes and the 713 lock |
| `.github/workflows/checks.yml` | no | runs the Tier 2 numeric checks and validation regression tests |

### Scorer v2

A run is **valid** only if all of the following hold:

1. frozen hashes match;
2. no forbidden constructs;
3. `lake build` succeeds;
4. **the audit process exits 0**;
5. **every target reports `proven` or `sorry`**.

Items 4 and 5 are new. They make the frozen scorer enforce what
`verify_lean_checkpoint.py` previously checked separately; the guard stays as a
second line. The output adds `audit_exit_code`, `audit_complete`, and `points_by_tier`.
Lean output and scorer logs use UTF-8 explicitly, including on Windows with a
cp1252 default; a regression test covers Unicode diagnostics without `PYTHONUTF8`.

Tested against simulated Lean output:

| Scenario | Result |
|---|---|
| all proven | valid, 121/121 |
| Tier 2 `sorry` | valid, tier1=60/60, tier2=0/61 |
| audit exits 1 | **invalid** (v1 accepted it) |
| one report missing | **invalid** (v1 accepted it) |
| elaboration error | invalid |
| non-standard axiom | invalid |
| non-standard axiom together with `sorryAx` | invalid (inherited parser bug fixed) |
| `--accept` against current `results/lean_best.json` | ACCEPT 60 → 121 |

The guard builds all 11 modules from `targets.json`. It passes when Tier 2 is
`sorry`, and fails on a bad audit exit.

## The 13 targets

All target statements use finite sums. The classifier proofs use measure theory
internally to derive these finite sums from independent Bernoulli observations.
Each target was checked numerically by
`tools/check_targets2_numeric.py` (about 10 s); all pass.
Every target must have positive recorded coverage. I6 includes a deterministic
one-coin case with `d = h = 1/2`, `eta = 1/8`, and both test errors `delta = 3/8`;
there is no synthetic passing fallback when no qualifying sample is tested.

### Group I: information and testing (27 points, `Proofs/Tier2/Information.lean`)

| Id | Name | Pts | Statement |
|---|---|---:|---|
| I1 | `kl_data_processing_finite` | 3 | Two-cell data processing: `kl(P(A), Q(A)) ≤ KL(P‖Q)` on a finite type |
| I2 | `pinsker_finite` | 4 | `TV ≤ √(KL/2)` on a finite type, strictly positive weights |
| I3 | `two_point_rms_lower` | 2 | If both RMS errors are ≤ R, then `(b−a)²(1−TV) ≤ 8R²` |
| I4 | `transcript_law_total` | 3 | The law of a stopped adaptive transcript is a probability distribution |
| I5 | `stopped_transcript_kl` | 10 | Hard pair `q± = 1/2 ± η`: `KL ≤ (128/225)h² · E₊[work]` |
| I6 | `stopped_transcript_testing` | 3 | A test with both errors ≤ δ forces `kl(1−δ, δ) ≤ (128/225)h² E₊[work]` |
| I7 | `bounded_ratio_log` | 2 | Scalar core of the bounded-ratio decomposition |

The experiment model is a deterministic adaptive policy over `m` coins with revealed
magnitudes, run for at most `n` steps. A transcript is `Fin n → Option Bool`, where
`none` means stopped. A randomized policy is a mixture of these. An unbounded
horizon follows by a limit that is not formalized here.

### Group K: Lemmas 6–7 as probability statements, (k1, k2) = (1, 1) (30 points, `Proofs/Tier2/ClassifierProb.lean`)

| Id | Name | Pts | Statement |
|---|---|---:|---|
| K1 | `lemma6_error` | 8 | Cap-2^L classifier: `P(error) ≤ min{1, (2^L d²)^{-2}}` |
| K2 | `lemma6_work` | 8 | `E[work] ≤ 17 m_N(d)` |
| K3 | `lemma7_telescoping` | 2 | `Σ_l E[Δ_l] = P(Z_{2^L} = 1)`, for any thresholds |
| K4 | `lemma7_second_moment` | 6 | `E[Y_L²] ≤ 85 min{√2^L, 1/d}` |
| K5 | `lemma7_work` | 6 | `E[W_L] ≤ 149 min{√2^L, 1/d}` |

Expectations are explicit sums over `Fin (2^L) → Bool`, the shared stream. The
estimator is truncated at level L. The nonnegative second-moment and work
series admit monotone limits; unbiasedness also needs an integrability or
absolute-summability argument. These extensions are not formalized here.

Observed slack:

- K1: worst ratio is 0.75, at L = 1, where the bound is 1.
- K4 and K5: the true constants are far below 85 and 149; observed maxima are about 3.4 and 3.

### Group R: rare event (4 points, `Proofs/Tier2/RareEvent.lean`)

| Id | Name | Pts | Statement |
|---|---|---:|---|
| R1 | `psi_optimizer_atomic` | 4 | Atomic law: `w*(d) = min{1, t²/d²}` maximizes `Σ w_j min{v_j, h√v_j/d_j}` subject to `0 ≤ v ≤ 1` and `Σ w v ≤ ρ` |

R1 assumes a cutoff `t` satisfying the mass constraint and restricts `0 < h < t`.
It does not establish cutoff existence/uniqueness, the `h >= t` saturation case,
or the arbitrary-law optimizer. Its proposed mathematical statement is unchanged.
These extensions are now proved separately in
[Tier 3's optimizer](../../lean/ThresholdHC/Tier3/Optimizer.lean).

## Approval and re-freeze

David approved integration and re-freezing on 27 October 2026:

> Go ahead and fix the two validation issues, harden the 713 guard, and integrate Tier 2. I approve re-freezing once all checks pass.

The integration retained all 13 proposed target statements unchanged. Before
re-freezing, both numeric suites, validation regressions, the complete Lean
build and target audit, the full 713 audit, and the remaining local CI checks
passed. The baseline audit had 33 proven targets and 13 `sorry` targets.
[FREEZE_LOG.md](../../FREEZE_LOG.md) records the checks and the approved 21-file freeze. The valid
60/121 integration baseline is preserved in `results/lean_tier2_baseline.json`;
`results/lean_best.json` now records the complete 121/121 proof checkpoint.

Subsequent proof checkpoints use `tools/score.py --accept results/lean_best.json`
and the independent checkpoint guard before committing. This integration is an
approved target-set extension, not a claimed proof-score improvement.

## Proof hints

Suggested order is cheapest first: I7, I4, K3, I1, I3, I2, R1, then I5 and I6,
K1 and K2, K4 and K5.

**I7.** Put `y = √x`. Then the left side is `f(y) = y² − 1 − 2 log y`, with
`f(1) = f'(1) = 0` and `f'' = 2 + 2/y²`. So `C = 1 + 1/(1−κ)` works, by Taylor
with remainder or by a direct monotonicity argument.

**I4.** Fix the sign vector `s` and prove `Σ_ω pathProb = 1` by induction on `n`:

- Split `Fin (n+1) → Option Bool` with `Fin.snoc`.
- Prove `histBefore (Fin.snoc ω o) (Fin.castSucc t) = histBefore ω t`.
- The last factor sums to 1 over `{none, some true, some false}` for any history.

Nonnegativity follows from `0 ≤ p ≤ 1`, which holds because `d ≤ 1/2`.

**K3.** This is a pure telescoping sum. `deltaK 0` is the cap-1 classifier
itself; induct with `Finset.sum_range_succ`. It holds for any `k1` and `k2`.

**I1.** This is the log-sum inequality on A and on Aᶜ: Jensen for the convex
function `x log x` with weights `Q a / Q(A)`. Mathlib has the convexity, for
example `Real.strictConvexOn_mul_log`; names may differ in the pinned version.
The hypothesis `Q a = 0 → P a = 0` handles the `log 0 = 0` convention.

**I3.** Use the midpoint test. Markov gives
`P(|θ−a| ≥ (b−a)/2) ≤ 4R²/(b−a)²`, and the same for Q. The two test errors
sum to at least `1 − TV`.

**I2.** Two routes:

- Prove the two-point Pinsker inequality `2(u−v)² ≤ kl(u,v)` by calculus, then
  apply I1 with A = {P > Q}.
- If the pinned Mathlib has Pinsker, transfer it.

**R1.** Use a Lagrangian with `λ = h/(2t)`. Each `g_j(v) = min{v, h√v/d_j}` is
concave. At `v* = t²/d_j² < 1`, its derivative is `h/(2t)`. At saturated atoms
(`d_j ≤ t`), the left derivative at 1 is at least `h/(2t)`. So
`g_j(v) ≤ g_j(v*_j) + λ(v − v*_j)` for every `v ∈ [0,1]`. Multiply by `w_j`, sum,
and use `Σ w v ≤ ρ = Σ w v*`.

**I5.** This is the main one. Use the chain rule with the same `Fin.snoc`
decomposition as I4:

- `KL_{n+1} = KL_n + E₊[conditional kl at step n]`.
- When the policy picks coin i, signs are independent across coins. So under
  each hypothesis, the conditional success probability is
  `pred d_i (rhoPlus η_i Λ)` or `pred d_i (rhoMinus η_i Λ)`, where Λ is coin i's
  likelihood ratio from its earlier observations.
- **Tier 1 B2 (`lemmaA_forward`, already proved) bounds this per step by
  `32 d²η²/(1−4η²)²`, uniformly in Λ.**
- Then `η ≤ 1/8` and `dη ≤ h/8` give `128h²/225`.
- Edge case `d_i = 1/2`: after one observation Λ is 0 or ∞, both posteriors
  coincide, and later steps on that coin contribute 0. B2 needs `0 < Λ`, so
  treat this case separately.

Numerically, the worst ratio of KL to the bound is 0.898, at d = 1/2, n = 1. Half
the checker's trials sit exactly on the `η = min{1/8, h/(8d)}` boundary.

**I6.** Combine three facts:

- I1 with the test set A; mutual absolute continuity holds because `1/2 ± η ≥ 3/8 > 0`.
- `kl(u, v)` increases in u and decreases in v on `u ≥ 1−δ > 1/2 > δ ≥ v`.
- I5.

**K1 and K2.** Follow v4's Lemma 6 proof:

- Use a Chernoff/Hoeffding bound at each dyadic checkpoint, then a union bound.
- On `Fin M → Bool`, sums of `streamProb` against `exp(λ·succCount)` factorize
  (`Finset.prod_univ_sum` / `Fintype.prod_sum`), so Hoeffding's lemma
  `p e^{λ(1−p)} + (1−p) e^{−λp} ≤ e^{λ²/8}` gives the bound without measure theory.
- Prove the prefix lemma once and reuse it.

**K4 and K5.** Follow v4's Lemma 7:

- `E[Δ_l²] ≤ P(Z_l ≠ Z_{l−1}) ≤ err_l + err_{l−1}` from K1. Then sum the
  geometric series with `p_l = (1−r) r^l`.
- For work, K2 bounds each level by the max of two classifiers.

The `Uniform713` development already has Hoeffding tails and geometric-series
lemmas, but for measure-space observations and `(k1, k2) = (1/4, 1)`. Group K
is the v4 paper's `(1, 1)` on finite streams. Reuse the arithmetic where it
transfers; the probability layer is different.

## The 713 track

`FullBound713Statement` in `lean/ThresholdHC/Uniform713/Specification.lean` is
already proved by `full_bound_713` (commit `852690a`). It is untruncated, allows
arbitrary magnitude/sign laws and `[0,1]` observations, and assumes nothing
about classifier error or work bounds.

The guard now checks the original specification hash plus whole-file hashes
for its complete local import closure:

| File | Meaning protected |
|---|---|
| `Statements.lean` | `rLevel` and the original shared definitions |
| `Uniform713/Common.lean` | `threshold`, `cap`, `levelProb`, `increment` |
| `Uniform713/Concentration.lean` | `prefixMean`, `dyadicMean` |
| `Uniform713/Classifier.lean` | `firstStop`, `firstDecision`, `stopLevel`, `decision`, `work` |
| `Uniform713/Estimator.lean` | `levelMeasure`, `samplingMeasure`, `sampled`, `estimator` |

The guard rejects absent or incomplete dependency locks and checks that these
sources remain unchanged during the build and audit. The manifest, guard,
specification, and four newly protected dependency modules join the frozen
file set; `Statements.lean` and the dependency/toolchain pins were already
frozen. Regression tests cover every protected file and the local import closure.

Whole-file locks retain the completed Lean development byte-for-byte. Proofs
inside those files are consequently frozen too; future edits need approval.
Other 713 proof modules remain editable. The theorem remains outside the scored
Tier 1/2 target set; adding it to the scorer would be a separate scope change.

## Proof entry points

| Targets | Checked proof module |
|---|---|
| I1–I3, I7 | [InformationCore.lean](../../lean/ThresholdHC/Proofs/Tier2/InformationCore.lean) |
| I4 | [TranscriptBase.lean](../../lean/ThresholdHC/Proofs/Tier2/TranscriptBase.lean) |
| I5–I6 | [Transcript.lean](../../lean/ThresholdHC/Proofs/Tier2/Transcript.lean) |
| K1–K2, K4–K5 | [ClassifierProb.lean](../../lean/ThresholdHC/Proofs/Tier2/ClassifierProb.lean) |
| K3 | [ClassifierTelescoping.lean](../../lean/ThresholdHC/Proofs/Tier2/ClassifierTelescoping.lean) |
| R1 | [RareEvent.lean](../../lean/ThresholdHC/Proofs/Tier2/RareEvent.lean) |

The public declarations retain the exact frozen `ThresholdHC.Targets` types.
The stopped-transcript proof is supported by likelihood factorization and
posterior KL modules. The classifier proof is supported by explicit finite
marginals, a stopping-rule identity, concentration bounds, and finite series.

## What Tier 2 does not cover

- Randomized policies and unbounded horizons remain outside Tier 2's score.
  They are now covered by the separate [Tier 3 landmark](../../lean/ThresholdHC/Tier3/Full.lean)
  for stopping and terminal testing, with finite expected work.
- Untruncated estimators in Group K. The statements bound truncation level L
  uniformly; second-moment and work series have monotone limits. The untruncated 713 theorem is on the
  `Uniform713` track.
- The minimax lower and upper theorems as wholes, and the power-margin rates.
  Both minimax theorems are now proved separately, in
  [Tier 6](../../lean/ThresholdHC/Tier6/Full.lean) and
  [BlindUpper](../../lean/ThresholdHC/BlindUpper/Full.lean). The critical and
  [alpha > 2](../../lean/ThresholdHC/RareAboveTwo/Full.lean) power-margin rates are
  Lean-checked; the alpha < 2 rates remain paper proofs.
- Any optimality claim for 713. The lower bound remains 1/16.
