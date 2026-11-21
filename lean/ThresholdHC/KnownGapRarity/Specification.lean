import ThresholdHC.FixedPlan.Specification
import ThresholdHC.ClippedOutput.Clip
import ThresholdHC.Confidence.Model

/-! Target statements for the known-gap, rarity-free estimator.

Source: `research/2026-10-27-minimax-audit/adaptation.tex`, section
`A qualified guarantee when rarity is unknown` (input by `RESEARCH_NOTE.tex` of
the same package; the file has no LaTeX labels):
* Proposition `Known fixed gap, unknown rarity` with its proof (lines 6-38).
  Let `mu = delta_d`, `0 < d < 1/2`, be known. For a budget `B >= 1` let `m` be
  the least positive odd integer at least `log(2B)/(2d^2)`. If `B >= 2m`, one
  estimator independent of the rarity has `E T <= B` and mean squared error at
  most `8 m theta/B + 4 m/B^2` for every `0 <= theta <= 1`, with a deterministic
  work cap; for `B < 2m` the constant zero has error `theta`. The proof queries
  `n = floor(B/m)` fresh coins `m` times each, takes the strict-majority
  decisions `Z_i`, sets `f = P(Bin(m,1/2-d) > m/2)` and returns
  `(Zbar - f)/(1-2f)` clipped to `[0,1]`.
* The paragraph on the computable confidence interval (lines 47-56): for
  `B >= 2m` the interval `[raw - r, raw + r]` intersected with `[0,1]`, where
  `r = sqrt(log(2/delta)/(2n))/(1-2f)`, covers `theta` with probability at least
  `1 - delta`; for smaller budgets the interval is `[0,1]`.
The claim is row `A7` of `research/2026-10-27-minimax-audit/CLAIMS.tsv`.

Formalization choices.
* The experiment is the original adaptive experiment `Tier6.experimentLaw` at the
  gap law `Measure.dirac d`. Every sign law `q` is allowed, and the target is
  `theta = signMean (Measure.dirac d) q.val`, which equals `q.val d` and ranges
  over `[0,1]`. Neither the estimator nor the budget depends on `q`.
* The odd flip count is `m = flipCount d B = 2 * flipIndex d B + 1`, given in
  closed form; `FlipCountStatement` certifies that it is the source's `m`.
* `missRate d B` is the exact binomial tail `FixedPlan.majorityMiss` of the
  majority of `m` flips at success rate `1/2 - d`, which is the source's `f`.
  Its computability and any floating-point evaluation are not formalized.
* The plan is the audited fixed plan `FixedPlan.majorityEstimator` with
  `coinCount d B = floor(B/m)` coins; `debiased` keeps its seed law and policy
  and changes only the output to `(Zbar - f)/(1-2f)`. For `B < 2m` the raw
  estimator is the empty plan with no coins, which has output `0` and no work.
  `knownGapEstimator` clips the raw output to `[0,1]` (`ClippedOutput.unitClip`).
* The mean squared error bound is stated for every `B >= 1`, also for `B < 2m`,
  where it follows from the zero output because `theta^2 <= 8 m theta/B` there.
  The deterministic work cap is `HardBudget.PathwiseCap` at `floor B`, and
  `E T <= B` is `UniformBudget`.
* The interval is centred at the unclipped raw output as in the source, with
  radius `knownGapRadius d B delta` (`1` for small budgets). Its coverage is
  stated in the interval form and as `Confidence.UniformConfidence`; the last
  conjunct adds that the interval centred at the clipped output also covers.
* The hypothesis `d < 1/2` is kept to match the source.
Not stated: the unbiasedness of the raw estimate as a separate claim (it is used
inside the risk proof), the order-of-magnitude discussion after the proof, the
endpoint remark at `d = 1/2`, and the shared-regression example of
`theorem/critical.tex` (claim `D4`). -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace ThresholdHC.KnownGapRarity
open ThresholdHC.Tier6 ThresholdHC.FixedPlan ThresholdHC.HardBudget

/-- `k` with `m = 2k+1` the least positive odd integer at least `log(2B)/(2d^2)`. -/
def flipIndex (d : Gap) (B : ℝ) : ℕ := ⌈(Real.log (2*B) / (2*(d:ℝ)^2) - 1) / 2⌉₊

/-- The source's odd flip count `m`. -/
def flipCount (d : Gap) (B : ℝ) : ℕ := 2 * flipIndex d B + 1

/-- `f = P(Bin(m, 1/2-d) > m/2)`: the exact binomial tail, a finite sum in `d` and `m` (its computability is not formalized). -/
def missRate (d : Gap) (B : ℝ) : ℝ := majorityMiss (flipIndex d B) d

/-- The number of coins `n = floor(B/m)`. -/
def coinCount (d : Gap) (B : ℝ) : ℕ := ⌊B / (flipCount d B : ℝ)⌋₊

/-- The fixed plan's majority share, debiased: output `(Zbar - f)/(1-2f)`.
Same seed law and policy as `majorityEstimator k n`. -/
def debiased (k n : ℕ) (f : ℝ) : AdaptiveEstimator Unit :=
  { majorityEstimator k n with
    output := fun z => ((majorityEstimator k n).output z - f) / (1 - 2*f)
    output_measurable := ((majorityEstimator k n).output_measurable.sub_const f).div_const _ }

/-- If `B >= 2m`: `n` fresh coins with `m` flips each, debiased. Otherwise stop at
once with output `0` (the empty plan). The rarity does not occur. -/
def rawEstimator (d : Gap) (B : ℝ) : AdaptiveEstimator Unit :=
  if 2 * (flipCount d B : ℝ) ≤ B then debiased (flipIndex d B) (coinCount d B) (missRate d B)
  else majorityEstimator (flipIndex d B) 0

/-- The source's estimator: the raw estimate clipped to `[0,1]`. -/
def knownGapEstimator (d : Gap) (B : ℝ) : AdaptiveEstimator Unit :=
  ClippedOutput.unitClip (rawEstimator d B)

/-- Half-width of the computable interval (`1` for small budgets). -/
def knownGapRadius (d : Gap) (B δ : ℝ) : ℝ :=
  if 2 * (flipCount d B : ℝ) ≤ B then
    Real.sqrt (Real.log (2/δ) / (2 * (coinCount d B : ℝ))) / (1 - 2 * missRate d B)
  else 1

/-- `flipCount` is the source's `m`: the least positive odd integer at least
`log(2B)/(2d^2)`. -/
def FlipCountStatement : Prop :=
  ∀ (d : Gap) (B : ℝ), 1 ≤ B →
    Odd (flipCount d B) ∧ Real.log (2*B) / (2*(d:ℝ)^2) ≤ flipCount d B ∧
    ∀ m : ℕ, Odd m → Real.log (2*B) / (2*(d:ℝ)^2) ≤ m → flipCount d B ≤ m

/-- Proposition (known fixed gap, unknown rarity): one rarity-free estimator per
budget, a deterministic cap of `floor B` flips on every path, expected work at most
`B` for every sign law (`UniformBudget`), zero output for `B < 2m` with squared
error exactly `theta^2` there, and mean squared error at most
`8 m theta/B + 4 m/B^2` for every sign law (`theta = q.val d` ranges over
`[0,1]`). -/
def KnownGapRarityFreeStatement : Prop :=
  ∀ (d : Gap), (d : ℝ) < 1/2 → ∀ B : ℝ, 1 ≤ B →
    PathwiseCap (knownGapEstimator d B) ⌊B⌋₊ ∧
    UniformBudget (Measure.dirac d) (knownGapEstimator d B) B ∧
    (B < 2 * (flipCount d B : ℝ) → ∀ z, (knownGapEstimator d B).output z = 0) ∧
    (B < 2 * (flipCount d B : ℝ) → ∀ q : SignLaw,
      squaredRisk (experimentLaw (Measure.dirac d) (knownGapEstimator d B) q)
          (populationOutput (knownGapEstimator d B)) (signMean (Measure.dirac d) q.val) =
        ENNReal.ofReal (signMean (Measure.dirac d) q.val ^ 2)) ∧
    ∀ q : SignLaw,
      squaredRisk (experimentLaw (Measure.dirac d) (knownGapEstimator d B) q)
          (populationOutput (knownGapEstimator d B)) (signMean (Measure.dirac d) q.val) ≤
        ENNReal.ofReal (8 * (flipCount d B : ℝ) * signMean (Measure.dirac d) q.val / B
          + 4 * (flipCount d B : ℝ) / B^2)

/-- The computable conservative interval `[raw - r, raw + r]` intersected with
`[0,1]` covers `theta` with probability at least `1 - delta`, in the same experiment
(`knownGapEstimator` has the same seed law and policy as `rawEstimator`). The
second conjunct is the standard form; the third centres the interval at the
clipped output instead. -/
def KnownGapConfidenceStatement : Prop :=
  ∀ (d : Gap), (d : ℝ) < 1/2 → ∀ B : ℝ, 1 ≤ B → ∀ δ : ℝ, 0 < δ → δ < 1 →
    (∀ q : SignLaw, experimentLaw (Measure.dirac d) (rawEstimator d B) q
      {z | signMean (Measure.dirac d) q.val ∉
        Set.Icc (populationOutput (rawEstimator d B) z - knownGapRadius d B δ)
                (populationOutput (rawEstimator d B) z + knownGapRadius d B δ) ∩ Set.Icc 0 1}
        ≤ ENNReal.ofReal δ) ∧
    Confidence.UniformConfidence (Measure.dirac d) (rawEstimator d B) (knownGapRadius d B δ) δ ∧
    Confidence.UniformConfidence (Measure.dirac d) (knownGapEstimator d B) (knownGapRadius d B δ) δ

end ThresholdHC.KnownGapRarity
