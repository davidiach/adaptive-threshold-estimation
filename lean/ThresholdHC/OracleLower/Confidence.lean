import ThresholdHC.OracleLower.Information
import ThresholdHC.Confidence.Lower

noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal
namespace ThresholdHC.OracleLower
open ThresholdHC.Tier6 ThresholdHC.Confidence

def confidenceClipFactor : ℝ := 15/(32*Real.sqrt 2)

theorem confidenceClipFactor_bounds : 0 < confidenceClipFactor ∧ confidenceClipFactor ≤ 1 := by
  have hs : 0 < Real.sqrt (2 : ℝ) := by positivity
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  constructor
  · unfold confidenceClipFactor; positivity
  · unfold confidenceClipFactor
    apply (div_le_iff₀ (by positivity : 0 < 32*Real.sqrt (2:ℝ))).mpr
    nlinarith

theorem confidenceClipFactor_square : confidenceClipFactor^2 = (225/2048 : ℝ) := by
  unfold confidenceClipFactor
  rw [div_pow,mul_pow,Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem confidenceClipFactor_eighth : confidenceClipFactor/8 = 15/(256*Real.sqrt 2) := by
  unfold confidenceClipFactor
  field_simp
  norm_num

/-- The paper's confidence coefficient, valid even for the general magnitude
oracle. The target law need not be the oracle's magnitude sampling law. -/
theorem oracle_confidence_lower : OracleConfidenceLowerStatement := by
  intro R _ μ _ A B δ r hB hδ hδle hr hbudget hconfidence
  have hB0 : 0 < B := by linarith
  have hs0 := confidenceScale_pos hB0 hδ hδle
  let h := confidenceClipFactor*confidenceScale B δ
  have hh : 0 < h := mul_pos confidenceClipFactor_bounds.1 hs0
  let hv := hard_pair_validity h hh
  let qp : SignLaw := ⟨hardPlus h,hv.2.1,fun d => (hv.2.2.2 d).2.2.1⟩
  let qm : SignLaw := ⟨hardMinus h,hv.2.2.1,fun d => (hv.2.2.2 d).2.2.2⟩
  let a := signMean μ qp.val
  let b := signMean μ qm.val
  have hsep : a-b = (1/4:ℝ)*modulus μ h := hard_pair_separation μ h hh
  have hscale := modulus_scaling μ confidenceClipFactor (confidenceScale B δ)
    confidenceClipFactor_bounds.1.le confidenceClipFactor_bounds.2 hs0.le
  have hsq : (confidenceScale B δ)^2*B = Real.log (1/δ) := by
    rw [confidenceScale,Real.sq_sqrt (div_nonneg (confidence_log_pos hδ hδle).le hB0.le)]
    exact div_mul_cancel₀ _ (ne_of_gt hB0)
  have hcost : (128/225:ℝ)*h^2*B = Real.log (1/δ)/16 := by
    calc
      _ = (128/225:ℝ)*confidenceClipFactor^2*((confidenceScale B δ)^2*B) := by dsimp [h]; ring
      _ = _ := by rw [confidenceClipFactor_square,hsq]; ring
  have hkl := oracle_hard_pair_information A B h hh hbudget
  change klDiv (oracleLaw A qp) (oracleLaw A qm) ≤ _ at hkl
  have hkl' : klDiv (oracleLaw A qp) (oracleLaw A qm) < ENNReal.ofReal (Real.log (1/δ)/4) := by
    apply lt_of_le_of_lt hkl
    apply (ENNReal.ofReal_lt_ofReal_iff (div_pos (confidence_log_pos hδ hδle) (by norm_num))).mpr
    rw [hcost]
    linarith [confidence_log_pos hδ hδle]
  by_contra hn
  have hsmall : 2*r < a-b := by
    have hn' := lt_of_not_ge hn
    rw [← confidenceClipFactor_eighth] at hn'
    change confidenceClipFactor*modulus μ (confidenceScale B δ) ≤ modulus μ h at hscale
    nlinarith
  have htest := confidence_testing_bound (oracleLaw A qp) (oracleLaw A qm)
    A.output A.output_measurable a b r δ hδ hδle hsmall (hconfidence qp) (hconfidence qm)
  exact (not_le_of_gt hkl') htest

theorem hidden_confidence_lower {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (B δ r : ℝ)
    (hB : 1 ≤ B) (hδ : 0 < δ) (hδle : δ ≤ 1/4) (hr : 0 ≤ r)
    (hb : UniformBudget μ A B) (hc : UniformConfidence μ A r δ) :
    (15/(256*Real.sqrt 2))*modulus μ (confidenceScale B δ) ≤ r :=
  oracle_confidence_lower (PopulationSeed R) μ (hiddenOracle μ A) B δ r hB hδ hδle hr hb hc

end ThresholdHC.OracleLower
