import ThresholdHC.EntropyTail.Model
import ThresholdHC.EntropyTail.QuantileThreshold

/-! The quantile cut for an arbitrary gap law, including boundary atoms. -/

noncomputable section
open MeasureTheory Set Real ProbabilityTheory
open scoped ENNReal Topology

namespace ThresholdHC.EntropyTail
open ThresholdHC.Tier6

def gapCDF (μ : Measure Gap) : StieltjesFunction ℝ := cdf (μ.map Subtype.val)

theorem gapCDF_eq (μ : Measure Gap) [IsProbabilityMeasure μ] (t : ℝ) :
    gapCDF μ t = μ.real {d : Gap | (d:ℝ) ≤ t} := by
  rw [gapCDF, cdf_eq_real,
    map_measureReal_apply measurable_subtype_coe measurableSet_Iic]
  rfl

theorem gapCDF_zero (μ : Measure Gap) [IsProbabilityMeasure μ] : gapCDF μ 0 = 0 := by
  rw [gapCDF_eq]
  have he : {d : Gap | (d:ℝ) ≤ 0} = ∅ := by
    ext d
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
    exact not_le_of_gt d.property.1
  simp [he]

theorem gapCDF_half (μ : Measure Gap) [IsProbabilityMeasure μ] : gapCDF μ (1/2) = 1 := by
  rw [gapCDF_eq]
  have he : {d : Gap | (d:ℝ) ≤ 1/2} = univ := by
    ext d
    simp only [mem_ofPred_eq, mem_univ, iff_true]
    exact d.property.2
  rw [he]
  simp

theorem quantileThreshold_eq_levelThreshold (μ : Measure Gap) [IsProbabilityMeasure μ]
    (ρ : ℝ) : quantileThreshold μ ρ = levelThreshold (gapCDF μ) ρ := by
  simp only [quantileThreshold, levelThreshold, gapCDF_eq]

theorem quantileThreshold_properties (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    0 < quantileThreshold μ ρ ∧ quantileThreshold μ ρ ≤ 1/2 ∧
    ρ ≤ μ.real {d : Gap | (d:ℝ) ≤ quantileThreshold μ ρ} ∧
    ∀ r < quantileThreshold μ ρ, μ.real {d : Gap | (d:ℝ) ≤ r} < ρ := by
  simpa only [← quantileThreshold_eq_levelThreshold, gapCDF_eq] using
    stieltjes_threshold_properties (gapCDF μ) hρ (gapCDF_zero μ)
      (by simpa only [gapCDF_half] using hρ1)

theorem quantileThreshold_mass_below (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    μ.real {d : Gap | (d:ℝ) < quantileThreshold μ ρ} ≤ ρ := by
  let f := gapCDF μ
  let t := quantileThreshold μ ρ
  have hleft : Function.leftLim f t ≤ ρ := by
    rw [f.mono.leftLim_eq_sSup]
    apply csSup_le (nonempty_Iio.image f)
    rintro _ ⟨r, hr, rfl⟩
    simpa only [f, gapCDF_eq] using
      ((quantileThreshold_properties μ hρ hρ1).2.2.2 r hr).le
  have hm : μ {d : Gap | (d:ℝ) < t} = ENNReal.ofReal (Function.leftLim f t) := by
    have he := (cdf (μ.map Subtype.val)).measure_Iio
      (tendsto_cdf_atBot (μ.map Subtype.val)) t
    rw [measure_cdf, Measure.map_apply measurable_subtype_coe measurableSet_Iio] at he
    simpa only [sub_zero, f, gapCDF, preimage, mem_Iio] using he
  rw [measureReal_def, hm]
  calc
    _ ≤ (ENNReal.ofReal ρ).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top (ENNReal.ofReal_le_ofReal hleft)
    _ = ρ := ENNReal.toReal_ofReal hρ.le

theorem gap_mass_le_eq (μ : Measure Gap) [IsFiniteMeasure μ] (t : ℝ) :
    μ.real {d : Gap | (d:ℝ) ≤ t} =
      μ.real {d : Gap | (d:ℝ) < t} + μ.real {d : Gap | (d:ℝ) = t} := by
  have hu : {d : Gap | (d:ℝ) ≤ t} =
      {d : Gap | (d:ℝ) < t} ∪ {d : Gap | (d:ℝ) = t} := by
    ext d
    exact (le_iff_lt_or_eq : (d:ℝ) ≤ t ↔ (d:ℝ) < t ∨ (d:ℝ) = t)
  rw [hu]
  exact measureReal_union (by
    rw [Set.disjoint_left]
    intro d hlt heq
    exact (ne_of_lt hlt) heq)
    (measurableSet_eq_fun measurable_subtype_coe measurable_const)

theorem quantileBoundaryFraction_properties (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    0 ≤ quantileBoundaryFraction μ ρ ∧ quantileBoundaryFraction μ ρ ≤ 1 ∧
      quantileBoundaryFraction μ ρ * μ.real {d : Gap | (d:ℝ) = quantileThreshold μ ρ} =
        ρ - μ.real {d : Gap | (d:ℝ) < quantileThreshold μ ρ} := by
  have hlo := quantileThreshold_mass_below μ hρ hρ1
  have hhi := (quantileThreshold_properties μ hρ hρ1).2.2.1
  rw [gap_mass_le_eq] at hhi
  unfold quantileBoundaryFraction
  have hn : 0 ≤ ρ - μ.real {d : Gap | (d:ℝ) < quantileThreshold μ ρ} := sub_nonneg.2 hlo
  have hb : 0 ≤ μ.real {d : Gap | (d:ℝ) = quantileThreshold μ ρ} := measureReal_nonneg
  rcases hb.eq_or_lt with hz | hp
  · have hnz : ρ - μ.real {d : Gap | (d:ℝ) < quantileThreshold μ ρ} = 0 := by
      linarith
    simp [← hz, hnz]
  · exact ⟨div_nonneg hn hp.le, (div_le_one hp).2 (by linarith),
      div_mul_cancel₀ _ hp.ne'⟩

theorem quantileTail_le (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) : quantileTail μ ρ ≤ μ := by
  let t := quantileThreshold μ ρ
  have hr : ENNReal.ofReal (quantileBoundaryFraction μ ρ) ≤ 1 := by
    exact ENNReal.ofReal_le_one.mpr (quantileBoundaryFraction_properties μ hρ hρ1).2.1
  have hu : {d : Gap | (d:ℝ) < t} ∪ {d : Gap | (d:ℝ) = t} =
      {d : Gap | (d:ℝ) ≤ t} := by
    ext d
    exact (le_iff_lt_or_eq : (d:ℝ) ≤ t ↔ (d:ℝ) < t ∨ (d:ℝ) = t).symm
  calc
    quantileTail μ ρ ≤ μ.restrict {d : Gap | (d:ℝ) < t} +
        μ.restrict {d : Gap | (d:ℝ) = t} := by
      unfold quantileTail
      apply add_le_add le_rfl
      calc
        _ ≤ (1 : ℝ≥0∞) • μ.restrict {d : Gap | (d:ℝ) = t} := by
          intro s
          simp only [Measure.smul_apply, smul_eq_mul]
          gcongr
        _ = _ := one_smul _ _
    _ = μ.restrict {d : Gap | (d:ℝ) ≤ t} := by
      rw [← Measure.restrict_union, hu]
      · rw [Set.disjoint_left]
        intro d hlt heq
        exact (ne_of_lt hlt) heq
      · exact measurableSet_eq_fun measurable_subtype_coe measurable_const
    _ ≤ μ := Measure.restrict_le_self

theorem quantileTail_mass (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) : (quantileTail μ ρ) univ = ENNReal.ofReal ρ := by
  have hp := quantileBoundaryFraction_properties μ hρ hρ1
  unfold quantileTail
  rw [Measure.add_apply, Measure.smul_apply, Measure.restrict_apply_univ,
    Measure.restrict_apply_univ, smul_eq_mul]
  rw [← ofReal_measureReal, ← ofReal_measureReal,
    ← ENNReal.ofReal_mul hp.1, hp.2.2, ← ENNReal.ofReal_add measureReal_nonneg]
  · congr 1
    ring
  · exact sub_nonneg.2 (quantileThreshold_mass_below μ hρ hρ1)

theorem quantileTail_add_core (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) : quantileTail μ ρ + quantileCore μ ρ = μ := by
  have : IsFiniteMeasure (quantileTail μ ρ) :=
    isFiniteMeasure_of_le μ (quantileTail_le μ hρ hρ1)
  rw [quantileCore, add_comm, Measure.sub_add_cancel_of_le (quantileTail_le μ hρ hρ1)]

theorem quantileTail_support (μ : Measure Gap) (ρ : ℝ) :
    ∀ᵐ d : Gap ∂quantileTail μ ρ, (d:ℝ) ≤ quantileThreshold μ ρ := by
  rw [quantileTail, ae_add_measure_iff]
  constructor
  · exact (ae_restrict_mem (measurableSet_lt measurable_subtype_coe measurable_const)).mono
      (fun _ hd => hd.le)
  · apply Measure.ae_smul_measure
    exact (ae_restrict_mem (measurableSet_eq_fun measurable_subtype_coe measurable_const)).mono
      (fun _ hd => hd.le)

theorem quantileCore_support (μ : Measure Gap) (ρ : ℝ) :
    ∀ᵐ d : Gap ∂quantileCore μ ρ, quantileThreshold μ ρ ≤ (d:ℝ) := by
  rw [ae_iff]
  simp only [not_le]
  apply Measure.sub_apply_eq_zero_of_restrict_le_restrict
  · unfold quantileTail
    rw [Measure.restrict_add, Measure.restrict_restrict]
    · simp only [inter_self]
      exact le_add_of_nonneg_right bot_le
    · exact measurableSet_lt measurable_subtype_coe measurable_const
  · exact measurableSet_lt measurable_subtype_coe measurable_const

end ThresholdHC.EntropyTail
