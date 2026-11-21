import ThresholdHC.RestrictedRMS.Specification
import ThresholdHC.SharpRMS.Full

/-! Restricted settings from the all-protocol theorem. Restricting the class
of protocols can only raise the minimax risk, and restricting the budgets only
removes constraints, so the coefficient one sixth of
`SharpRMS.sharp_coefficient` stays valid. The four-fresh-flip estimator
`SharpRMS.fourFlips` has budget four and maximal RMS risk at most one sixth at
the gap one half, where the modulus is one. It lies in the class by hypothesis
in `restricted_coefficient_iff` and by `fresh_policy_count` in the three-flip
class, so no larger coefficient is valid. For the oracles, the upper direction
is `SharpRMS.oracle_endpoint_eq`. The note's class-specific lower-bound
arguments are not used. -/
noncomputable section
namespace ThresholdHC.RestrictedRMS
open MeasureTheory
open scoped ENNReal
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.Tier6 ThresholdHC.OracleLower

/-- At the gap one half and budget four the modulus is one. -/
theorem endpoint_modulus_one :
    modulus (Measure.dirac SharpRMS.endpointGap) (1 / Real.sqrt 4) = 1 := by
  norm_num [modulus, clippedGap, SharpRMS.endpointGap, Real.sqrt_eq_iff_mul_self_eq]

/-- The four-fresh-flip estimator has maximal RMS risk at most one sixth at the
gap one half. -/
theorem four_flips_rms_le :
    maximalRMSRisk (Measure.dirac SharpRMS.endpointGap) SharpRMS.fourFlips ≤
      ENNReal.ofReal (1/6 : ℝ) := by
  apply iSup_le
  intro q
  apply HardBudget.rms_from_square _ _ _ _ (by norm_num)
  rw [SharpRMS.four_flips_squared_risk]
  norm_num

/-- A coefficient at most one sixth gives at most one sixth of the modulus. -/
theorem coefficient_scale (μ : Measure Gap) [IsProbabilityMeasure μ] {B c : ℝ}
    (hb : 1 ≤ B) (hc : c ≤ 1/6) :
    ENNReal.ofReal (modulus μ (1 / Real.sqrt B) * c) ≤
      ENNReal.ofReal (modulus μ (1 / Real.sqrt B) / 6) := by
  apply ENNReal.ofReal_le_ofReal
  have hp : 0 < 1 / Real.sqrt B := by positivity
  simpa only [div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_left hc (modulus_pos μ hp).le

/-- A class containing every four-fresh-flip protocol and a set of budgets at
least one containing four have restricted coefficient exactly one sixth. -/
theorem restricted_coefficient_iff
    (C : ∀ (R : Type) [MeasurableSpace R], AdaptiveEstimator R → Prop) (S : Set ℝ)
    (hC : ∀ (R : Type) [MeasurableSpace R] (A : AdaptiveEstimator R),
      (∀ s, A.policy s = freshPolicy 3) → C R A)
    (hS : ∀ B ∈ S, 1 ≤ B) (h4 : (4 : ℝ) ∈ S) (c : ℝ) :
    (∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), B ∈ S →
      ENNReal.ofReal (modulus μ (1 / Real.sqrt B) * c) ≤
        sInf {r | ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R),
          C R A ∧ UniformBudget μ A B ∧ r = maximalRMSRisk μ A}) ↔ c ≤ 1/6 := by
  constructor
  · intro h
    have e := h (Measure.dirac SharpRMS.endpointGap) 4 h4
    rw [endpoint_modulus_one, one_mul] at e
    refine (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp (e.trans ?_)
    refine le_trans (sInf_le ?_) four_flips_rms_le
    exact ⟨Unit, inferInstance, SharpRMS.fourFlips,
      hC Unit SharpRMS.fourFlips (fun _ => rfl), SharpRMS.four_flips_budget _, rfl⟩
  · intro hc μ _ B hB
    refine ((SharpRMS.sharp_coefficient c).mpr hc μ B (hS B hB)).trans ?_
    unfold minimaxRisk
    apply sInf_le_sInf
    rintro _ ⟨R, mR, A, -, hb, rfl⟩
    exact ⟨R, mR, A, hb, rfl⟩

/-- The budget restriction `1 ≤ B ≤ 4`, as the instance of the general statement
with every protocol and `S = [1, 4]`. -/
theorem small_budget_coefficient_iff (c : ℝ) :
    (∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 1 ≤ B → B ≤ 4 →
      ENNReal.ofReal (modulus μ (1 / Real.sqrt B) * c) ≤ minimaxRisk μ B) ↔ c ≤ 1/6 := by
  have key := restricted_coefficient_iff
    (fun (R : Type) [MeasurableSpace R] (_ : AdaptiveEstimator R) => True) (Set.Icc 1 4)
    (by intros; trivial) (fun _ hB => hB.1) ⟨by norm_num, le_rfl⟩ c
  have hset (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ) :
      sInf {r | ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R),
        True ∧ UniformBudget μ A B ∧ r = maximalRMSRisk μ A} = minimaxRisk μ B := by
    unfold minimaxRisk
    simp only [true_and]
  rw [← key]
  constructor
  · intro h μ _ B hB
    rw [hset]
    exact h μ B hB.1 hB.2
  · intro h μ _ B h1 h4
    rw [← hset]
    exact h μ B ⟨h1, h4⟩

/-- The same budget restriction under both magnitude oracles. -/
theorem oracle_small_budget_coefficient_iff (c : ℝ) :
    ((∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 1 ≤ B → B ≤ 4 →
      ENNReal.ofReal (modulus μ (1 / Real.sqrt B) * c) ≤ revealedMinimaxRisk μ B) ↔ c ≤ 1/6) ∧
    ((∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 1 ≤ B → B ≤ 4 →
      ENNReal.ofReal (modulus μ (1 / Real.sqrt B) * c) ≤ selectedMinimaxRisk μ B) ↔ c ≤ 1/6) := by
  obtain ⟨hr, hs⟩ := SharpRMS.oracle_endpoint_eq
  constructor
  · constructor
    · intro h
      have e := h (Measure.dirac SharpRMS.endpointGap) 4 (by norm_num) le_rfl
      rw [endpoint_modulus_one, one_mul, hr] at e
      exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp e
    · intro hc μ _ B hb _
      exact (coefficient_scale μ hb hc).trans (SharpRMS.oracle_sharp_lower μ B hb).1
  · constructor
    · intro h
      have e := h (Measure.dirac SharpRMS.endpointGap) 4 (by norm_num) le_rfl
      rw [endpoint_modulus_one, one_mul, hs] at e
      exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp e
    · intro hc μ _ B hb _
      exact (coefficient_scale μ hb hc).trans (SharpRMS.oracle_sharp_lower μ B hb).2

/-- The fresh policy never revisits a coin: the coin requested after `xs` is
the new label `xs.length`, which no earlier flip used. -/
theorem fresh_policy_count (xs : List Bool) (j : ℕ) (h : freshPolicy 3 xs = some j) :
    (List.range xs.length).countP (fun i => decide (freshPolicy 3 (xs.take i) = some j)) < 3 := by
  unfold freshPolicy at h
  split_ifs at h
  have hj : xs.length = j := Option.some.inj h
  rw [List.countP_eq_zero.mpr]
  · norm_num
  · intro i hi
    rw [List.mem_range] at hi
    simp only [freshPolicy, List.length_take, min_eq_left hi.le, decide_eq_true_eq]
    split_ifs <;> simp
    omega

/-- At most three flips per coin, as the instance of the general statement with
the three-flip class and every budget `B ≥ 1`. -/
theorem three_flip_coefficient_iff (c : ℝ) :
    (∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ), 1 ≤ B →
      ENNReal.ofReal (modulus μ (1 / Real.sqrt B) * c) ≤
        sInf {r | ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R),
          (∀ (s : R) (xs : List Bool) (j : ℕ), A.policy s xs = some j →
            (List.range xs.length).countP
              (fun i => decide (A.policy s (xs.take i) = some j)) < 3) ∧
          UniformBudget μ A B ∧ r = maximalRMSRisk μ A}) ↔ c ≤ 1/6 :=
  restricted_coefficient_iff
    (fun (R : Type) [MeasurableSpace R] (A : AdaptiveEstimator R) =>
      ∀ (s : R) (xs : List Bool) (j : ℕ), A.policy s xs = some j →
        (List.range xs.length).countP (fun i => decide (A.policy s (xs.take i) = some j)) < 3)
    (Set.Ici 1)
    (by
      intro R _ A hA s xs j h
      rw [hA s] at h ⊢
      exact fresh_policy_count xs j h)
    (fun _ hB => hB) (by norm_num) c

end ThresholdHC.RestrictedRMS
