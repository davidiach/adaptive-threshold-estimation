import ThresholdHC.StoppingProgram.FlowPoisson
import ThresholdHC.RareAboveTwo.Nonvacuity

/-! Every feasible stopping certificate is realized by an actual observable
estimator with the original uniform expected-work and squared-risk bounds. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo

theorem squared_bias_bound {x b : ℝ} (hb : 0 ≤ b) (h : |x| ≤ b) : x^2 ≤ b^2 := by
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg x) hb).mpr h

theorem certificate_realization {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (ρ B : ℝ) (C : Certificate N) (hC : Feasible μ ρ B C) (hN : 0 < N) :
    ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R),
      RareBudget μ A ρ B ∧ ∀ q : SignLaw, RarePrior μ ρ q →
        squaredRisk (experimentLaw μ A q) (populationOutput A) (signMean μ q.val) ≤ certificateSquared C := by
  by_cases hzero : intensity C.flow = 0
  · refine ⟨Unit,inferInstance,constantEstimator C.offset,constant_rare_budget μ ρ B C.offset,?_⟩
    intro q hq
    have hout : C.flow.outputWeight = fun _ => 0 := funext (fun s => (flow_zero_intensity C.flow hC.cone hzero s).2.2)
    have hm : countMean μ q C.flow.outputWeight = 0 := by simp [hout,countMean]
    have hb := hC.bias_bound q hq
    rw [hm,add_zero] at hb
    have he : squaredRisk (experimentLaw μ (constantEstimator C.offset) q)
        (populationOutput (constantEstimator C.offset)) (signMean μ q.val) =
        ENNReal.ofReal ((C.offset-signMean μ q.val)^2) := by
      simp [squaredRisk,populationOutput,constantEstimator]
    rw [he,certificateSquared]
    apply ENNReal.ofReal_le_ofReal
    have hsq := squared_bias_bound hC.bias_nonneg hb
    linarith [hC.variance_nonneg]
  · have hr : 0 < intensity C.flow := lt_of_le_of_ne (hC.cone.continue_nonneg (rootState N)) (Ne.symm hzero)
    obtain ⟨J,⟨e⟩⟩ := positiveTable_enumeration C.flow hC.cone hr
    let A := shiftEstimator (flowPoissonEstimator hN C.flow hC.cone e) C.offset
    refine ⟨Fin (J+1) → ℕ,inferInstance,A,?_,?_⟩
    · intro q hq
      change expectedWork μ (shiftEstimator _ _) q ≤ _
      rw [shiftEstimator_work,flowPoisson_work]
      exact ENNReal.ofReal_le_ofReal (hC.work_bound q hq)
    · intro q hq
      change squaredRisk (experimentLaw μ (shiftEstimator _ _) q) (populationOutput (shiftEstimator _ _)) _ ≤ _
      rw [shiftEstimator_squaredRisk]
      apply (flowPoisson_squaredRisk μ q hN C.flow hC.cone e _).trans
      apply ENNReal.ofReal_le_ofReal
      have hb := squared_bias_bound hC.bias_nonneg (hC.bias_bound q hq)
      have he : countMean μ q C.flow.outputWeight-(signMean μ q.val-C.offset) =
          C.offset+countMean μ q C.flow.outputWeight-signMean μ q.val := by ring
      rw [he]
      exact add_le_add (hC.variance_bound q hq) hb |>.trans_eq (add_comm _ _)

end ThresholdHC.StoppingProgram
