import ThresholdHC.ArbitraryLawAdaptation.IncreasingSelection

/-! The entropy--tail functional on laws that may have unresolved mass at
zero. Positive mass selected at zero has infinite entropy; its tail cost is one. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThresholdHC.ArbitraryLawAdaptation
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTail

def positivePart (μ : Measure ℝ) : Measure Gap := μ.comap Subtype.val

theorem gapEmbedding : MeasurableEmbedding (Subtype.val : Gap → ℝ) :=
  MeasurableEmbedding.subtype_coe measurableSet_Ioc

theorem positivePart_map (σ : Measure Gap) : positivePart (σ.map Subtype.val) = σ :=
  gapEmbedding.comap_map σ

theorem map_positivePart (μ : Measure ℝ) :
    (positivePart μ).map Subtype.val = μ.restrict (Ioc 0 (1/2)) := by
  rw [positivePart, gapEmbedding.map_comap]
  congr 1
  ext x
  constructor
  · rintro ⟨d, rfl⟩; exact d.property
  · intro hx; exact ⟨⟨x, hx⟩, rfl⟩

def zeroGamma (σ : Measure ℝ) : ℝ≥0∞ :=
  if σ {0} = 0 then gamma (positivePart σ) else ∞

def zeroTailWeight (h d : ℝ) : ℝ≥0∞ :=
  if d ≤ 0 then 1 else ENNReal.ofReal (min 1 (h/d))

def zeroTailCost (μ : Measure ℝ) (h : ℝ) : ℝ≥0∞ := ∫⁻ d, zeroTailWeight h d ∂μ

def zeroObjective (μ : Measure ℝ) (ρ B : ℝ) (σ : Measure ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (1/Real.sqrt B)*(ENNReal.ofReal ρ*zeroGamma σ)^(1/2 : ℝ) +
    zeroTailCost (μ-σ) (1/Real.sqrt B)

def zeroSelection (μ : Measure ℝ) (ρ B : ℝ) : ℝ≥0∞ :=
  min (ENNReal.ofReal ρ) (⨅ (σ : Measure ℝ) (_ : σ ≤ μ), zeroObjective μ ρ B σ)

theorem zeroGamma_of_atom {σ : Measure ℝ} (hz : σ {0} ≠ 0) : zeroGamma σ = ∞ := by
  simp [zeroGamma, hz]

theorem zeroTailWeight_zero (h : ℝ) : zeroTailWeight h 0 = 1 := by simp [zeroTailWeight]

theorem measurable_zeroTailWeight (h : ℝ) : Measurable (zeroTailWeight h) :=
  Measurable.ite measurableSet_Iic measurable_const
    ((measurable_const.min (measurable_const.div measurable_id)).ennreal_ofReal)

theorem zeroTailWeight_antitone {h : ℝ} (hh : 0 ≤ h) : Antitone (zeroTailWeight h) := by
  intro x y hxy
  by_cases hy : y ≤ 0
  · simp [zeroTailWeight, hy, hxy.trans hy]
  · by_cases hx : x ≤ 0
    · simp only [zeroTailWeight, hx, hy, ite_true, ite_false]
      exact (ENNReal.ofReal_le_ofReal (min_le_left _ _)).trans_eq ENNReal.ofReal_one
    · simp only [zeroTailWeight, hx, hy, ite_false]
      exact ENNReal.ofReal_le_ofReal
        (min_le_min_left _ (div_le_div_of_nonneg_left hh (lt_of_not_ge hx) hxy))

theorem mappedGap_zero_atom (σ : Measure Gap) : σ.map Subtype.val {0} = 0 := by
  rw [gapEmbedding.map_apply]
  have he : (Subtype.val : Gap → ℝ) ⁻¹' {0} = ∅ := by
    ext d
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    exact ne_of_gt d.property.1
  rw [he, measure_empty]

theorem zeroGamma_map (σ : Measure Gap) : zeroGamma (σ.map Subtype.val) = gamma σ := by
  rw [zeroGamma, ite_eq_left (mappedGap_zero_atom σ), positivePart_map]

theorem zeroTailCost_map (σ : Measure Gap) (h : ℝ) :
    zeroTailCost (σ.map Subtype.val) h = tailCost σ h := by
  rw [zeroTailCost, lintegral_map (measurable_zeroTailWeight h) measurable_subtype_coe]
  apply lintegral_congr
  intro d
  simp only [zeroTailWeight, not_le.mpr d.property.1, ite_false]

theorem zeroObjective_map (μ : Measure Gap) [IsFiniteMeasure μ] {σ : Measure Gap}
    (hσ : σ ≤ μ) (ρ B : ℝ) :
    zeroObjective (μ.map Subtype.val) ρ B (σ.map Subtype.val) = selectionObjective μ ρ B σ := by
  have : IsFiniteMeasure σ := isFiniteMeasure_of_le μ hσ
  rw [zeroObjective, zeroGamma_map, ← map_sub_of_le hσ measurable_subtype_coe, zeroTailCost_map]
  rfl

theorem comap_mono_embedding {A E : Type*} [MeasurableSpace A] [MeasurableSpace E]
    {f : A → E} (hf : MeasurableEmbedding f) {μ ν : Measure E} (h : μ ≤ ν) :
    μ.comap f ≤ ν.comap f := by
  intro s
  rw [hf.comap_apply, hf.comap_apply]
  exact h _

theorem zeroSelection_map (μ : Measure Gap) [IsFiniteMeasure μ] (ρ B : ℝ) :
    zeroSelection (μ.map Subtype.val) ρ B = selection μ ρ B := by
  apply le_antisymm
  · apply le_min (min_le_left _ _)
    apply le_iInf₂
    intro σ hσ
    have hsmap : σ.map Subtype.val ≤ μ.map Subtype.val := Measure.map_mono hσ measurable_subtype_coe
    have hle : zeroSelection (μ.map Subtype.val) ρ B ≤
        zeroObjective (μ.map Subtype.val) ρ B (σ.map Subtype.val) :=
      (min_le_right (ENNReal.ofReal ρ) _).trans
      (iInf₂_le (σ.map Subtype.val) hsmap)
    exact hle.trans_eq (zeroObjective_map μ hσ ρ B)
  · apply le_min (selection_le_rho _ _ _)
    apply le_iInf₂
    intro σ hσ
    have hp : positivePart σ ≤ μ := by
      have h := comap_mono_embedding gapEmbedding hσ
      rw [gapEmbedding.comap_map] at h
      exact h
    have hs : (positivePart σ).map Subtype.val = σ := by
      rw [positivePart, gapEmbedding.map_comap]
      apply Measure.restrict_eq_self_of_ae_mem
      apply (Measure.absolutelyContinuous_of_le hσ).ae_le
      exact ae_map_mem_range gapEmbedding.measurableSet_range measurable_subtype_coe.aemeasurable
    have he := zeroObjective_map μ hp ρ B
    rw [hs] at he
    exact (selection_le_objective hp ρ B).trans_eq he.symm

end ThresholdHC.ArbitraryLawAdaptation
