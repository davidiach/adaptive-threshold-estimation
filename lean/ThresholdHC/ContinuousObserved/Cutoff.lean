import ThresholdHC.ObservedState.Construction

noncomputable section
open MeasureTheory
namespace ThresholdHC.ContinuousObserved
open ThresholdHC.Tier6 ThresholdHC.ObservedState

def capGap (a d : Gap) : Gap :=
  ⟨min (d : ℝ) a,lt_min d.property.1 a.property.1,(min_le_left _ _).trans d.property.2⟩

theorem capGap_le (a d : Gap) : capGap a d ≤ a := min_le_right _ _

theorem capGap_le_self (a d : Gap) : capGap a d ≤ d := min_le_left _ _

theorem capGap_of_le (a d : Gap) (hd : d ≤ a) : capGap a d = d := by
  apply Subtype.ext
  exact min_eq_left hd

theorem capGap_of_ge (a d : Gap) (hd : a ≤ d) : capGap a d = a := by
  apply Subtype.ext
  exact min_eq_right hd

theorem measurable_capGap (a : Gap) : Measurable (capGap a) :=
  (measurable_subtype_coe.min measurable_const).subtype_mk

theorem clippedGap_antitone (h : Gap) {d b : Gap} (hd : d ≤ b) :
    clippedGap h b ≤ clippedGap h d :=
  min_le_min_left _ (div_le_div_of_nonneg_left h.property.1.le d.property.1 hd)

theorem capGap_clipped_bound (a h d b : Gap) (hd : d ≤ b)
    (hc : clippedGap h d ≤ 2 * clippedGap h b) :
    clippedGap h (capGap a d) ≤ 2 * clippedGap h (capGap a b) := by
  by_cases ha : d ≤ a
  · rw [capGap_of_le a d ha]
    exact hc.trans (mul_le_mul_of_nonneg_left (clippedGap_antitone h (capGap_le_self a b)) (by norm_num))
  · have ha' : a ≤ d := le_of_lt (lt_of_not_ge ha)
    rw [capGap_of_ge a d ha',capGap_of_ge a b (ha'.trans hd)]
    have hn := clippedGap_nonneg h.property.1.le a
    linarith

theorem capGap_law (μ : Measure Gap) (a : Gap)
    (hs : ∀ᵐ d ∂μ, d ≤ a) : μ.map (capGap a) = μ := by
  have he : capGap a =ᵐ[μ] id := hs.mono (fun d hd => capGap_of_le a d hd)
  rw [Measure.map_congr he,Measure.map_id]

theorem capped_delta_ge {N : ℕ} (cap : Fin N → Gap) (cell : unitInterval → Fin N) (a h : Gap) :
    cellDelta cap cell h ≤ cellDelta (fun i => capGap a (cap i)) cell h := by
  unfold cellDelta
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (clippedGap_antitone h (capGap_le_self a (cap i))) (measureReal_nonneg)

def cappedDesign (μ : Measure Gap) (a h : Gap) {δ : ℝ} (hδ : 0 ≤ δ)
    (hs : ∀ᵐ d ∂μ, d ≤ a) (D : CellDesign μ h δ) : CellDesign μ h δ where
  count := D.count
  cap := fun i => capGap a (D.cap i)
  gap := fun u => capGap a (D.gap u)
  cell := D.cell
  gap_measurable := (measurable_capGap a).comp D.gap_measurable
  cell_measurable := D.cell_measurable
  gap_law := by
    change volume.map (capGap a ∘ D.gap) = μ
    rw [← Measure.map_map (measurable_capGap a) D.gap_measurable,D.gap_law,capGap_law μ a hs]
  cap_bound := fun u => min_le_min (D.cap_bound u) le_rfl
  clipped_bound := fun u => capGap_clipped_bound a h (D.gap u) (D.cap (D.cell u))
    (D.cap_bound u) (D.clipped_bound u)
  concentration := by
    have hb := capped_delta_ge D.cap D.cell a h
    have hn : 0 ≤ cellDelta D.cap D.cell h := by
      unfold cellDelta
      apply mul_nonneg (by norm_num)
      exact Finset.sum_nonneg (fun i _ => mul_nonneg measureReal_nonneg (clippedGap_nonneg h.property.1.le _))
    exact D.concentration.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (sq_le_sq₀ hn (hn.trans hb) |>.mpr hb) hδ) (by norm_num))

end ThresholdHC.ContinuousObserved
