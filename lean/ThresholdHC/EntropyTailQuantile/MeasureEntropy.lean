import ThresholdHC.EntropyTailQuantile.Model
import ThresholdHC.EntropyTailQuantile.CostEntropySeries

/-! Band integrability and countable cost entropy for finite gap measures. -/

noncomputable section
open MeasureTheory Set Real
open scoped ENNReal BigOperators

namespace ThresholdHC.EntropyTailQuantile
open ThresholdHC.Tier6

theorem bandEdge_pos (j : ℕ) : 0 < bandEdge j := by
  unfold bandEdge
  positivity

theorem bandEdge_antitone : Antitone bandEdge := by
  intro i j hij
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.add_le_add_right hij 1)

theorem measurableSet_band (j : ℕ) : MeasurableSet (band j) :=
  (measurableSet_lt measurable_const measurable_subtype_coe).inter
    (measurableSet_le measurable_subtype_coe measurable_const)

theorem band_inverseSquare_integrable (σ : Measure Gap) [IsFiniteMeasure σ] (j : ℕ) :
    IntegrableOn (fun d : Gap => (d:ℝ)⁻¹ ^ 2) (band j) σ := by
  apply Measure.integrableOn_of_bounded (measure_ne_top _ _)
    (by fun_prop : AEStronglyMeasurable (fun d : Gap => (d:ℝ)⁻¹ ^ 2) σ)
    (M := (bandEdge j / 2)⁻¹ ^ 2)
  filter_upwards [ae_restrict_mem (measurableSet_band j)] with d hd
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  apply pow_le_pow_left₀ (inv_nonneg.mpr d.property.1.le)
  exact inv_anti₀ (by positivity [bandEdge_pos j]) hd.1.le

theorem bandCost_nonneg (σ : Measure Gap) (j : ℕ) : 0 ≤ bandCost σ j :=
  integral_nonneg (fun _ => sq_nonneg _)

theorem bandCost_mono {σ τ : Measure Gap} [IsFiniteMeasure τ] (h : σ ≤ τ) (j : ℕ) :
    bandCost σ j ≤ bandCost τ j := by
  apply integral_mono_measure (Measure.restrict_mono le_rfl h)
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
    (band_inverseSquare_integrable τ j)

theorem measureCostEntropy_mono {σ τ : Measure Gap} [IsFiniteMeasure τ] (h : σ ≤ τ) :
    measureCostEntropy σ ≤ measureCostEntropy τ := by
  apply iSup_mono
  intro n
  exact ENNReal.ofReal_le_ofReal (costEntropy_mono
    (fun i : Fin n => bandCost_nonneg σ i) (fun i => bandCost_mono h i))

theorem measureCostEntropy_lt_top_of_support (σ : Measure Gap) {t : ℝ}
    (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) : measureCostEntropy σ < ⊤ := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one ht (by norm_num : (2:ℝ)⁻¹ < 1)
  have hbN : bandEdge N < t := (pow_le_pow_of_le_one (by norm_num) (by norm_num)
    (Nat.le_succ N)).trans_lt hN
  have hzero (j : ℕ) (hj : N ≤ j) : bandCost σ j = 0 := by
    have hm : σ (band j) = 0 := by
      apply measure_mono_null (t := {d : Gap | (d:ℝ) < t})
      · intro d hd
        exact hd.2.trans_lt ((bandEdge_antitone hj).trans_lt hbN)
      · simpa only [ae_iff, not_le] using hs
    simp only [bandCost, Measure.restrict_eq_zero.mpr hm, integral_zero_measure]
  apply lt_of_le_of_lt (b := ENNReal.ofReal
    (costEntropy (fun i : Fin N => bandCost σ i)))
  · apply iSup_le
    intro n
    exact ENNReal.ofReal_le_ofReal
      (costEntropy_prefix_le_of_eventually_zero (bandCost_nonneg σ) hzero n)
  · exact ENNReal.ofReal_lt_top

end ThresholdHC.EntropyTailQuantile
