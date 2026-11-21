import ThresholdHC.OracleUpper.Upper
import ThresholdHC.OracleSharpness.Full

/-! The upper bound of both magnitude-oracle minimax risks by one half of the
modulus, its floor form, and the optimality of the coefficient one half,
stated against the specification. The lower half of the coefficient
statement is the audited sharpness theorem
ThresholdHC.OracleSharpness.oracle_upper_sharpness, used at budget one. -/
noncomputable section
namespace ThresholdHC.OracleUpper
open MeasureTheory
open scoped ENNReal
open ThresholdHC ThresholdHC.Tier6 ThresholdHC.OracleLower

theorem oracle_upper : OracleUpperStatement := oracle_modulus_upper_bound

theorem oracle_floor_upper : OracleFloorUpperStatement := oracle_floor_upper_bound

private theorem half_le_coefficient {c : ℝ}
    (h : ∀ g : Gap, ENNReal.ofReal (modulus (Measure.dirac g) (1 / Real.sqrt 1) * c) <
      revealedMinimaxRisk (Measure.dirac g) 1 ∧
      ENNReal.ofReal (modulus (Measure.dirac g) (1 / Real.sqrt 1) * c) <
      selectedMinimaxRisk (Measure.dirac g) 1 → False) : 1/2 ≤ c := by
  by_contra hc
  obtain ⟨g₀, hg₀, hg⟩ :=
    ThresholdHC.OracleSharpness.oracle_upper_sharpness 1 c le_rfl (lt_of_not_ge hc)
  exact h ⟨min g₀ (1/2), lt_min hg₀ (by norm_num), min_le_right _ _⟩ (hg _ (min_le_left _ _))

private theorem half_mul_le (μ : Measure Gap) (B c : ℝ) (hc : 1/2 ≤ c) :
    ENNReal.ofReal (modulus μ (1 / Real.sqrt B) / 2) ≤
      ENNReal.ofReal (modulus μ (1 / Real.sqrt B) * c) := by
  apply ENNReal.ofReal_le_ofReal
  have h := modulus_nonneg μ (one_div_nonneg.mpr (Real.sqrt_nonneg B))
  nlinarith

theorem oracle_upper_coefficient : OracleUpperCoefficientStatement := by
  intro c
  constructor
  · constructor
    · intro h
      exact half_le_coefficient fun g hg => absurd (hg.1.trans_le (h (Measure.dirac g) 1 le_rfl))
        (lt_irrefl _)
    · intro hc μ _ B hB
      exact (oracle_upper μ B hB).1.trans (half_mul_le μ B c hc)
  · constructor
    · intro h
      exact half_le_coefficient fun g hg => absurd (hg.2.trans_le (h (Measure.dirac g) 1 le_rfl))
        (lt_irrefl _)
    · intro hc μ _ B hB
      exact (oracle_upper μ B hB).2.trans (half_mul_le μ B c hc)

end ThresholdHC.OracleUpper
