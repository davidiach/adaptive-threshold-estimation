import ThresholdHC.StoppingProgram.PrimalAttainment
import ThresholdHC.StoppingProgram.StrongDuality
import ThresholdHC.StoppingProgram.Specification

/-! The full unchanged attained four-prior dual target, with both primal
and dual optimizers, positive value and finite optimal information ratio. -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace ThresholdHC.StoppingProgram

theorem attained_four_prior_dual : AttainedDualStatement := by
  intro μ hμ ρ B N hρ hρquarter hB hN
  have hρhalf : ρ ≤ 1/2 := by linarith
  obtain ⟨hvalue,Q,hQ,hdual,hpos,hfinite⟩ := strong_four_prior_duality N μ hρ hρhalf hB
  obtain ⟨C,hC,hprimal⟩ := programSquared_attained N μ hρ hρhalf hB.le
  exact ⟨hvalue,C,Q,hC,hQ,hprimal,hdual,hpos,hfinite⟩

end ThresholdHC.StoppingProgram
