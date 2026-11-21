import ThresholdHC.KnownGapRarity.Specification

/-! Basic facts about the known-gap estimator: the debiased plan shares the
experiment of the fixed plan, the empty plan outputs `0`, the flip count is the
least odd integer above `log(2B)/(2d^2)`, and the coin count satisfies
`n m <= B` and, when `2m <= B`, `n >= B/(2m) >= 1`. -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace ThresholdHC.KnownGapRarity
open ThresholdHC.Tier6 ThresholdHC.FixedPlan ThresholdHC.HardBudget
open ThresholdHC.EntropyTailExecution

theorem debiased_experimentLaw (μ : Measure Gap) [IsProbabilityMeasure μ] (k n : ℕ) (f : ℝ)
    (q : SignLaw) :
    experimentLaw μ (debiased k n f) q = experimentLaw μ (majorityEstimator k n) q := rfl

theorem debiased_expectedWork (μ : Measure Gap) [IsProbabilityMeasure μ] (k n : ℕ) (f : ℝ)
    (q : SignLaw) :
    expectedWork μ (debiased k n f) q = expectedWork μ (majorityEstimator k n) q := rfl

theorem debiased_policy (k n : ℕ) (f : ℝ) :
    (debiased k n f).policy = (majorityEstimator k n).policy := rfl

theorem debiased_populationOutput (k n : ℕ) (f : ℝ) (z : PopulationSeed Unit × Tier3.ProcessTape) :
    populationOutput (debiased k n f) z =
      (populationOutput (majorityEstimator k n) z - f) / (1 - 2*f) := rfl

/-- The empty plan outputs `0` on every outcome. -/
theorem majorityEstimator_zero_output (k : ℕ) (z : Unit × Tier3.ProcessTape) :
    (majorityEstimator k 0).output z = 0 := by
  show finitePlanOutput (fun _ => majorityCall k 0) (fun _ => List.range 0) z = 0
  unfold finitePlanOutput
  rw [planRun_absorbs _ _ rfl]
  rfl

theorem rawEstimator_of_le {d : Gap} {B : ℝ} (h : 2 * (flipCount d B : ℝ) ≤ B) :
    rawEstimator d B = debiased (flipIndex d B) (coinCount d B) (missRate d B) := ite_eq_left h

theorem rawEstimator_of_lt {d : Gap} {B : ℝ} (h : B < 2 * (flipCount d B : ℝ)) :
    rawEstimator d B = majorityEstimator (flipIndex d B) 0 := ite_eq_right (not_le.mpr h)

theorem knownGapRadius_of_le {d : Gap} {B : ℝ} (δ : ℝ) (h : 2 * (flipCount d B : ℝ) ≤ B) :
    knownGapRadius d B δ =
      Real.sqrt (Real.log (2/δ) / (2 * (coinCount d B : ℝ))) / (1 - 2 * missRate d B) := ite_eq_left h

theorem knownGapRadius_of_lt {d : Gap} {B : ℝ} (δ : ℝ) (h : B < 2 * (flipCount d B : ℝ)) :
    knownGapRadius d B δ = 1 := ite_eq_right (not_le.mpr h)

theorem knownGapEstimator_output (d : Gap) (B : ℝ) (z : Unit × Tier3.ProcessTape) :
    (knownGapEstimator d B).output z = max 0 (min 1 ((rawEstimator d B).output z)) := rfl

/-- For `B < 2m` the clipped estimator outputs `0` on every outcome. -/
theorem knownGapEstimator_output_of_lt {d : Gap} {B : ℝ} (h : B < 2 * (flipCount d B : ℝ))
    (z : Unit × Tier3.ProcessTape) : (knownGapEstimator d B).output z = 0 := by
  rw [knownGapEstimator_output, rawEstimator_of_lt h, majorityEstimator_zero_output]
  norm_num

theorem rawEstimator_output_of_lt {d : Gap} {B : ℝ} (h : B < 2 * (flipCount d B : ℝ))
    (z : Unit × Tier3.ProcessTape) : (rawEstimator d B).output z = 0 := by
  rw [rawEstimator_of_lt h, majorityEstimator_zero_output]

/-! The flip count. -/

theorem flipCount_odd (d : Gap) (B : ℝ) : Odd (flipCount d B) := ⟨flipIndex d B, rfl⟩

theorem flipCount_pos (d : Gap) (B : ℝ) : 0 < flipCount d B := by
  unfold flipCount; omega

theorem flipCount_cast_pos (d : Gap) (B : ℝ) : (0 : ℝ) < flipCount d B := by
  exact_mod_cast flipCount_pos d B

theorem flipCount_ge (d : Gap) (B : ℝ) :
    Real.log (2*B) / (2*(d:ℝ)^2) ≤ flipCount d B := by
  have h := Nat.le_ceil ((Real.log (2*B) / (2*(d:ℝ)^2) - 1) / 2)
  unfold flipCount flipIndex
  push_cast
  linarith

theorem flipCount_least (d : Gap) (B : ℝ) (m : ℕ) (hm : Odd m)
    (h : Real.log (2*B) / (2*(d:ℝ)^2) ≤ m) : flipCount d B ≤ m := by
  obtain ⟨j, rfl⟩ := hm
  have hj : flipIndex d B ≤ j := by
    apply Nat.ceil_le.mpr
    push_cast at h
    linarith
  unfold flipCount
  omega

theorem flipCount_eq (d : Gap) (B : ℝ) : flipCount d B = 2 * flipIndex d B + 1 := rfl

/-! The coin count. -/

theorem coinCount_mul_le (d : Gap) {B : ℝ} (hB : 0 ≤ B) :
    (coinCount d B : ℝ) * flipCount d B ≤ B := by
  have hm := flipCount_cast_pos d B
  have h := Nat.floor_le (div_nonneg hB hm.le)
  unfold coinCount
  calc (⌊B / (flipCount d B : ℝ)⌋₊ : ℝ) * flipCount d B ≤ B / (flipCount d B : ℝ) * flipCount d B :=
        mul_le_mul_of_nonneg_right h hm.le
    _ = B := div_mul_cancel₀ B hm.ne'

theorem work_le_floor (d : Gap) {B : ℝ} (hB : 0 ≤ B) :
    coinCount d B * (2 * flipIndex d B + 1) ≤ ⌊B⌋₊ := by
  apply Nat.le_floor
  have h := coinCount_mul_le d hB
  push_cast
  unfold flipCount at h
  push_cast at h
  exact h

theorem coinCount_ge {d : Gap} {B : ℝ} (h : 2 * (flipCount d B : ℝ) ≤ B) :
    B / (2 * flipCount d B) ≤ coinCount d B := by
  have hm := flipCount_cast_pos d B
  have h1 := Nat.lt_floor_add_one (B / (flipCount d B : ℝ))
  have h2 : 2 ≤ B / (flipCount d B : ℝ) := by rw [le_div_iff₀ hm]; linarith
  have h3 : B / (2 * flipCount d B) = (B / (flipCount d B : ℝ)) / 2 := by
    rw [div_div, mul_comm]
  unfold coinCount
  rw [h3]
  linarith

theorem coinCount_one_le {d : Gap} {B : ℝ} (h : 2 * (flipCount d B : ℝ) ≤ B) :
    (1 : ℝ) ≤ coinCount d B := by
  have hm := flipCount_cast_pos d B
  have h1 := coinCount_ge h
  have h2 : 1 ≤ B / (2 * flipCount d B) := by rw [le_div_iff₀ (by positivity)]; linarith
  linarith

theorem coinCount_pos {d : Gap} {B : ℝ} (h : 2 * (flipCount d B : ℝ) ≤ B) :
    0 < coinCount d B := by
  have h1 := coinCount_one_le h
  exact_mod_cast (show (0 : ℝ) < coinCount d B by linarith)

end ThresholdHC.KnownGapRarity
