import ThresholdHC.ConfidenceProgram.MedianController
import ThresholdHC.HardBudget.Application

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThresholdHC.ConfidenceProgram
open ThresholdHC.Tier6 ThresholdHC.HardBudget ThresholdHC.ObservableSimulation

private theorem timeout_one_eighth {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (A : AdaptiveEstimator R) (N : ℕ) (M : ℝ) (hw : expectedWork μ A q ≤ ENNReal.ofReal (((N:ℝ)+1)/8)) :
    (originalSimulationLaw μ A q) {z | (outcome A N M z).1 = true} ≤ 1/8 := by
  let P := originalSimulationLaw μ A q
  let T := {z | (outcome A N M z).1 = true}
  have hm : MeasurableSet T := measurableSet_eq_fun (measurable_outcome A N M).fst measurable_const
  have he : (fun z => timedOut (outcome A N M z)) = T.indicator (fun _ => (1:ℝ≥0∞)) := by
    funext z; cases hp : (outcome A N M z).1 <;> simp [T,timedOut,hp]
  have h := (timeout_work μ q A M N).trans hw
  rw [he,lintegral_indicator hm,lintegral_const,Measure.restrict_apply_univ,one_mul] at h
  have h0 : (N:ℝ≥0∞)+1 ≠ 0 := by positivity
  apply (ENNReal.mul_le_mul_iff_left h0 (by finiteness : (N:ℝ≥0∞)+1 ≠ ⊤)).mp
  rw [mul_comm _ ((N:ℝ≥0∞)+1),mul_comm (1/8) _]
  refine h.trans_eq ?_
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<8),
    ENNReal.ofReal_add (Nat.cast_nonneg N) zero_le_one,ENNReal.ofReal_natCast]
  norm_num [div_eq_mul_inv]

private theorem deviation_one_eighth {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (f : Ω → ℝ) (hm : Measurable f) (θ r : ℝ) (hr : 0 ≤ r)
    (h : (∫⁻ z, loss θ (f z) ∂P) ≤ ENNReal.ofReal (r^2)) :
    P {z | Real.sqrt 8*r < |f z-θ|} ≤ 1/8 := by
  have hm' := (measurable_loss θ).comp hm
  by_cases hz : r = 0
  · subst r
    have hzero : (∫⁻ z, loss θ (f z) ∂P) = 0 := by simpa using h
    have he := (lintegral_eq_zero_iff hm').mp hzero
    have hz' : ∀ᵐ z ∂P, ¬ (Real.sqrt 8*0 < |f z-θ|) := by
      filter_upwards [he] with z hv
      change ENNReal.ofReal ((f z-θ)^2) = 0 at hv
      have hsq := ENNReal.ofReal_eq_zero.mp hv
      have hh : f z-θ=0 := by nlinarith [sq_nonneg (f z-θ)]
      simp [hh]
    have hnull : P {z | Real.sqrt 8*0 < |f z-θ|} = 0 := by simpa only [not_not] using ae_iff.mp hz'
    rw [hnull]
    exact bot_le
  have hr' := lt_of_le_of_ne hr (Ne.symm hz)
  have hr8 : 0 < 8*r^2 := by positivity
  have ht := meas_ge_le_lintegral_div (μ := P) hm'.aemeasurable (ENNReal.ofReal_pos.mpr hr8).ne' ENNReal.ofReal_ne_top
  apply (measure_mono (t := {z | ENNReal.ofReal (8*r^2) ≤ loss θ (f z)}) ?_).trans
    (ht.trans ((ENNReal.div_le_div_right h _).trans_eq ?_))
  · intro z hz
    have hs := pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg _) hr) hz.le 2
    rw [mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 8),sq_abs] at hs
    exact ENNReal.ofReal_le_ofReal hs
  · rw [← ENNReal.ofReal_div_of_pos hr8,show r^2/(8*r^2) = 1/8 by field_simp]
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<8)]
    norm_num

/-- Each capped trial fails with probability at most 1/4. Its timeout and
estimation error may be arbitrarily dependent. -/
theorem single_capped_failure {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (A : AdaptiveEstimator R) (N : ℕ) (M θ r : ℝ) (hθ : 0 ≤ θ ∧ θ ≤ M)
    (hr : 0 ≤ r) (hw : expectedWork μ A q ≤ ENNReal.ofReal (((N:ℝ)+1)/8))
    (hR : squaredRisk (experimentLaw μ A q) (populationOutput A) θ ≤ ENNReal.ofReal (r^2)) :
    (originalSimulationLaw μ A q) {z | Real.sqrt 8*r < |localValue M (outcome A N M z)-θ|} ≤ 1/4 := by
  let P := originalSimulationLaw μ A q
  let X := outcome A N M
  let T := {z | (X z).1 = true}
  let E := {z | Real.sqrt 8*r < |(X z).2-θ|}
  have ht := timeout_one_eighth μ q A N M hw
  have he := deviation_one_eighth P (fun z => (X z).2) (measurable_outcome A N M).snd θ r hr
    ((stage_loss_le μ q A M θ hθ N).trans hR)
  have hsub : {z | Real.sqrt 8*r < |localValue M (X z)-θ|} ⊆ T ∪ E := by
    intro z hz
    cases h : (X z).1 with
    | true => exact Or.inl h
    | false => exact Or.inr (by simpa [E,localValue,h] using hz)
  refine (measure_mono hsub).trans ((measure_union_le T E).trans ((add_le_add ht he).trans_eq ?_))
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  norm_num

end ThresholdHC.ConfidenceProgram
