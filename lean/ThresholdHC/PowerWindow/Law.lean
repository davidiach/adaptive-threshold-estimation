import ThresholdHC.PowerWindow.Specification
import ThresholdHC.RareAboveTwo.PowerLaw
import ThresholdHC.SubcriticalPower.Layers

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThresholdHC.PowerWindow
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.CriticalEntropy
open ThresholdHC.EntropyTailQuantile

/-- Positive-gap finite measures are determined by their real CDF values. -/
theorem gap_measure_ext (μ ν : Measure Gap) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ x : ℝ, 0 < x → μ.real {d | (d : ℝ) ≤ x} = ν.real {d | (d : ℝ) ≤ x}) : μ = ν := by
  have := μ.isFiniteMeasure_map (Subtype.val : Gap → ℝ)
  have := ν.isFiniteMeasure_map (Subtype.val : Gap → ℝ)
  apply (MeasurableEmbedding.subtype_coe (measurableSet_Ioc :
    MeasurableSet (Ioc (0 : ℝ) (1/2)))).map_injective
  change μ.map (Subtype.val : Gap → ℝ) = ν.map (Subtype.val : Gap → ℝ)
  apply Measure.ext_of_Iic
  intro x
  rw [Measure.map_apply measurable_subtype_coe measurableSet_Iic,
    Measure.map_apply measurable_subtype_coe measurableSet_Iic]
  change μ {d | (d : ℝ) ≤ x} = ν {d | (d : ℝ) ≤ x}
  by_cases hx : 0 < x
  · rw [← ofReal_measureReal, ← ofReal_measureReal, h x hx]
  · have he : {d : Gap | (d : ℝ) ≤ x} = ∅ := by
      ext d
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      exact not_le_of_gt ((not_lt.1 hx).trans_lt d.2.1)
    simp [he]

theorem exact_power_law_eq (μ : Measure Gap) [IsProbabilityMeasure μ]
    {α a : ℝ} (hα : 0 < α) (ha : 0 < a) (ha2 : a ≤ 1/2)
    (hm : ExactPowerLaw μ α a) : μ = powerGapLaw α a hα ha ha2 := by
  apply gap_measure_ext
  intro x hx
  rw [hm x hx, powerGapLaw_cdf α a hα ha ha2 x hx]

def partialPowerLaw (α a ρ : ℝ) (hα : 0 < α) (ha : 0 < a) (ha2 : a ≤ 1/2) : Measure Gap :=
  (uniformUnitMeasure.restrict (Iic ρ)).map (powerQuantile α a hα ha ha2)

theorem partialPowerLaw_finite (α a ρ : ℝ) (hα : 0 < α) (ha : 0 < a) (ha2 : a ≤ 1/2) :
    IsFiniteMeasure (partialPowerLaw α a ρ hα ha ha2) := by
  unfold partialPowerLaw
  infer_instance

theorem partialPowerLaw_cdf {α a ρ : ℝ} (hα : 0 < α) (ha : 0 < a) (ha2 : a ≤ 1/2)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (x : ℝ) (hx : 0 < x) :
    (partialPowerLaw α a ρ hα ha ha2).real {d | (d : ℝ) ≤ x} = min ρ ((x/a)^α) := by
  have hm : MeasurableSet {d : Gap | (d : ℝ) ≤ x} :=
    measurableSet_le measurable_subtype_coe measurable_const
  have hf := measurable_powerQuantile α a hα ha ha2
  rw [measureReal_def, partialPowerLaw, Measure.map_apply hf hm,
    Measure.restrict_apply (hf hm)]
  have he : (powerQuantile α a hα ha ha2 ⁻¹' {d | (d : ℝ) ≤ x}) ∩ Iic ρ
      =ᵐ[uniformUnitMeasure] Ioc 0 (min ρ ((x/a)^α)) := by
    filter_upwards [uniformUnit_ae_positive] with u hu
    apply propext
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, mem_Iic,
      powerQuantile_le_iff α a hα ha ha2 u x hu hx, mem_Ioc, le_min_iff]
    tauto
  rw [measure_congr he, uniformUnitMeasure, Measure.restrict_apply measurableSet_Ioc]
  have hi : Ioc 0 (min ρ ((x/a)^α)) ∩ Icc (0 : ℝ) 1 = Ioc 0 (min ρ ((x/a)^α)) :=
    inter_eq_left.2 fun u hu => ⟨hu.1.le, hu.2.trans ((min_le_left _ _).trans hρ1)⟩
  rw [hi, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal]
  exact le_min hρ.le (Real.rpow_nonneg (div_pos hx ha).le _)

theorem power_quantile_tail (μ : Measure Gap) [IsProbabilityMeasure μ]
    {α a ρ : ℝ} (hα : 0 < α) (ha : 0 < a) (ha2 : a ≤ 1/2)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hm : ExactPowerLaw μ α a) :
    quantileTail μ ρ = partialPowerLaw α a ρ hα ha ha2 := by
  have : IsFiniteMeasure (quantileTail μ ρ) := isFiniteMeasure_of_le μ (quantileTail_le μ hρ hρ1)
  have := partialPowerLaw_finite α a ρ hα ha ha2
  apply gap_measure_ext
  intro x hx
  rw [ThresholdHC.SubcriticalPower.quantile_cdf μ hρ hρ1, hm x hx,
    partialPowerLaw_cdf hα ha ha2 hρ hρ1 x hx, ← min_assoc, min_eq_left hρ1]

/-- The complementary upper quantile is the same power quantile map applied
to the uniform variable restricted to `(ρ,1]`. -/
theorem power_quantile_core (μ : Measure Gap) [IsProbabilityMeasure μ]
    {α a ρ : ℝ} (hα : 0 < α) (ha : 0 < a) (ha2 : a ≤ 1/2)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hm : ExactPowerLaw μ α a) :
    quantileCore μ ρ = (volume.restrict (Ioc ρ 1)).map (powerQuantile α a hα ha ha2) := by
  have hvol : uniformUnitMeasure.restrict (Ioi ρ) = volume.restrict (Ioc ρ 1) := by
    rw [uniformUnitMeasure, Measure.restrict_restrict measurableSet_Ioi]
    congr 1
    ext u
    simp only [mem_inter_iff, mem_Ioi, mem_Icc, mem_Ioc]
    constructor
    · rintro ⟨hu, _, hu1⟩
      exact ⟨hu, hu1⟩
    · rintro ⟨hu, hu1⟩
      exact ⟨hu, (hρ.trans hu).le, hu1⟩
  have hsplit : partialPowerLaw α a ρ hα ha ha2 +
      (uniformUnitMeasure.restrict (Ioi ρ)).map (powerQuantile α a hα ha ha2) =
        powerGapLaw α a hα ha ha2 := by
    rw [partialPowerLaw, ← Measure.map_add, ← compl_Iic,
      Measure.restrict_add_restrict_compl measurableSet_Iic]
    · rfl
    · exact measurable_powerQuantile α a hα ha ha2
  have := partialPowerLaw_finite α a ρ hα ha ha2
  rw [quantileCore, power_quantile_tail μ hα ha ha2 hρ hρ1 hm,
    exact_power_law_eq μ hα ha ha2 hm, ← hsplit, add_comm, Measure.add_sub_cancel, hvol]

end ThresholdHC.PowerWindow
