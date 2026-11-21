import ThresholdHC.UnknownRarity.Transfer
import ThresholdHC.UnknownRarity.Risk

/-! The obstruction to completely uniform adaptation to unknown rarity.

For one estimator and one budget: the bound at `θ = 0` for every `ρ` makes the
output zero almost surely under the all-negative prior. The stopped-transcript
null-set transfer at the interior gap `d < 1/2` carries this to the constant
prior `1/4`, where zero output has RMS error `1/4`. The bound at
`ρ = θ = 1/4` is below `1/4` once `B > 4C²/d²`. The family statement picks such
a budget, and the expected-work statement first derives almost-sure stopping. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.UnknownRarity
open ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.Tier6
open ThresholdHC.StoppingProgram (constantPrior)

theorem fixed_budget_obstruction_proof : FixedBudgetObstructionStatement := by
  intro d hd C B hB R _ A hstop H
  have hd0 : (0 : ℝ) < d := d.property.1
  have h00 : (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 1 := ⟨le_rfl, zero_le_one⟩
  have h14 : (0 : ℝ) ≤ 1/4 ∧ (1/4 : ℝ) ≤ 1 := by norm_num
  -- Under `θ = 0` the bound holds for every `ρ`, so the output vanishes.
  have hrms0 : rootMeanRisk (experimentLaw (Measure.dirac d) A (constantPrior 0 h00))
      (populationOutput A) 0 = 0 := by
    apply eq_zero_of_le_linear _ (max C 0) (le_max_right _ _)
    intro ρ hρ hρ1
    exact (H ρ hρ hρ1 0 h00 hρ.le).trans
      (ENNReal.ofReal_le_ofReal (bound_le_linear C ρ d B hρ.le hd0))
  have h0 := output_zero_of_rms_zero _ _ (measurable_populationOutput A) hrms0
  -- Transfer the null event of nonzero output to the constant prior `1/4`.
  have hS : MeasurableSet {x : R × ProcessTape | A.output x ≠ 0} :=
    A.output_measurable (measurableSet_singleton 0).compl
  have hq : ∀ᵐ z ∂experimentLaw (Measure.dirac d) A (constantPrior 0 h00),
      (z.1.1, z.2) ∉ {x : R × ProcessTape | A.output x ≠ 0} := by
    filter_upwards [h0] with z hz
    simp only [not_not]
    exact hz
  have hv := dirac_null_transfer d hd A (constantPrior 0 h00) (constantPrior (1/4) h14)
    hstop _ hS hq
  have h1 : ∀ᵐ z ∂experimentLaw (Measure.dirac d) A (constantPrior (1/4) h14),
      populationOutput A z = 0 := by
    filter_upwards [hv] with z hz
    simp only [not_not] at hz
    exact hz
  -- Zero output has RMS error `1/4` at `θ = 1/4`, above the bound at `ρ = 1/4`.
  have hrms1 := rms_of_output_zero _ _ h1 (1/4) (by norm_num)
  have hb := H (1/4) (by norm_num) le_rfl (1/4) h14 le_rfl
  rw [hrms1] at hb
  exact bound_quarter_lt d C B hd0 hB hb

theorem unknown_rarity_obstruction_proof : UnknownRarityObstructionStatement := by
  intro d hd C R _ A hstop H
  have hB1 : (1 : ℝ) ≤ max 1 (4 * C^2 / (d : ℝ)^2 + 1) := le_max_left _ _
  have hB : 4 * C^2 / (d : ℝ)^2 < max 1 (4 * C^2 / (d : ℝ)^2 + 1) :=
    lt_of_lt_of_le (lt_add_one _) (le_max_right _ _)
  exact fixed_budget_obstruction_proof d hd C _ hB _ (A _)
    (hstop _ hB1 (1/4) (by norm_num) le_rfl)
    (fun ρ hρ hρ1 θ hθ hθρ => H _ hB1 ρ hρ hρ1 θ hθ hθρ)

theorem expected_work_obstruction_proof : ExpectedWorkObstructionStatement := by
  intro d hd C R _ A hwork
  exact unknown_rarity_obstruction_proof d hd C R A
    (fun B hB θ hθ hθ4 => stops_of_expectedWork _ _ _ (hwork B hB θ hθ hθ4))

end ThresholdHC.UnknownRarity
