import ThresholdHC.ObservedState.Labels
import ThresholdHC.ObservedState.FiniteLower

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThresholdHC.ObservedState
open ThresholdHC.Tier6

def cellWeight {N : ℕ} (cell : unitInterval → Fin N) (i : Fin N) : ℝ :=
  volume.real {u | cell u = i}

def cellDelta {N : ℕ} (cap : Fin N → Gap) (cell : unitInterval → Fin N) (h : Gap) : ℝ :=
  (1 / 4) * ∑ i, cellWeight cell i * clippedGap h (cap i)

/-- A finite measurable cell partition with an exact underlying gap law.
The caps support the constant-magnitude family and the noise simulation. -/
structure CellDesign (μ : Measure Gap) (h : Gap) (δ : ℝ) where
  count : ℕ
  cap : Fin count → Gap
  gap : unitInterval → Gap
  cell : unitInterval → Fin count
  gap_measurable : Measurable gap
  cell_measurable : Measurable cell
  gap_law : volume.map gap = μ
  cap_bound : ∀ u, gap u ≤ cap (cell u)
  clipped_bound : ∀ u, clippedGap h (gap u) ≤ 2 * clippedGap h (cap (cell u))
  concentration : (∑ i, (cellWeight cell i) ^ 2) ≤ δ * (cellDelta cap cell h) ^ 2 / 16

theorem cell_moment {N : ℕ} (cell : unitInterval → Fin N) (hc : Measurable cell) (F : Fin N → ℝ) :
    (∫ u : unitInterval, F (cell u)) = ∑ i, cellWeight cell i * F i := by
  have : IsProbabilityMeasure (volume.map cell) :=
    (Measure.isProbabilityMeasure_map_iff hc.aemeasurable).mpr inferInstance
  rw [← integral_map (φ := cell) (f := F) hc.aemeasurable
    (measurable_of_countable F).aestronglyMeasurable,integral_fintype (Integrable.of_finite)]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_measureReal_apply hc (measurableSet_singleton i)]
  rfl

theorem cellWeight_sum {N : ℕ} (cell : unitInterval → Fin N) (hc : Measurable cell) :
    ∑ i, cellWeight cell i = 1 := by
  simpa only [integral_const,probReal_univ,smul_eq_mul,mul_one] using
    (cell_moment cell hc (fun _ => (1 : ℝ))).symm

theorem design_separation (μ : Measure Gap) [IsProbabilityMeasure μ] (h : Gap) (δ : ℝ)
    (D : CellDesign μ h δ) :
    modulus μ h / 8 ≤ cellDelta D.cap D.cell h := by
  have hg : Integrable (fun u => clippedGap h (D.gap u)) (volume : Measure unitInterval) := by
    apply (integrable_const (1 : ℝ)).mono'
      ((measurable_clippedGap h).comp D.gap_measurable).aestronglyMeasurable
    exact ae_of_all _ (fun u => by
      dsimp only [Function.comp_apply]
      rw [Real.norm_of_nonneg (clippedGap_nonneg h.property.1.le _)]
      exact clippedGap_le_one h _)
  have hc : Integrable (fun u => clippedGap h (D.cap (D.cell u))) (volume : Measure unitInterval) := by
    have hi : Integrable (fun i => clippedGap h (D.cap i)) (volume.map D.cell) := Integrable.of_finite
    exact (integrable_map_measure (measurable_of_countable (fun i => clippedGap h (D.cap i))).aestronglyMeasurable
      D.cell_measurable.aemeasurable).mp hi
  have hb := integral_mono hg (hc.const_mul 2) D.clipped_bound
  rw [integral_const_mul,cell_moment D.cell D.cell_measurable (fun i => clippedGap h (D.cap i))] at hb
  have he : (∫ u : unitInterval, clippedGap h (D.gap u)) = modulus μ h := by
    rw [← integral_map D.gap_measurable.aemeasurable (measurable_clippedGap h).aestronglyMeasurable,D.gap_law]
    rfl
  rw [he] at hb
  unfold cellDelta
  linarith

theorem design_delta_pos (μ : Measure Gap) [IsProbabilityMeasure μ] (h : Gap) (δ : ℝ)
    (D : CellDesign μ h δ) : 0 < cellDelta D.cap D.cell h :=
  (div_pos (modulus_pos μ h.property.1) (by norm_num)).trans_le (design_separation μ h δ D)

theorem design_cdf (μ : Measure Gap) (h : Gap) (δ : ℝ) (D : CellDesign μ h δ) (x : ℝ) :
    volume {u : unitInterval | (D.cap (D.cell u) : ℝ) ≤ x} ≤ μ {d : Gap | (d : ℝ) ≤ x} := by
  calc
    _ ≤ volume {u : unitInterval | (D.gap u : ℝ) ≤ x} :=
      measure_mono (fun u hu => (show (D.gap u : ℝ) ≤ (D.cap (D.cell u) : ℝ) from D.cap_bound u).trans hu)
    _ = (volume.map D.gap) {d : Gap | (d : ℝ) ≤ x} :=
      (Measure.map_apply D.gap_measurable (measurableSet_le measurable_subtype_coe measurable_const)).symm
    _ = _ := congrArg (fun ν : Measure Gap => ν {d : Gap | (d : ℝ) ≤ x}) D.gap_law

end ThresholdHC.ObservedState
