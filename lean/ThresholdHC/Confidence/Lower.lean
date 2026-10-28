import ThresholdHC.Confidence.Specification
import ThresholdHC.Confidence.Information
import ThresholdHC.Confidence.Testing

noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal
namespace ThresholdHC.Confidence
open ThresholdHC.Tier6

theorem confidence_log_pos {δ : ℝ} (hδ : 0 < δ) (hδle : δ ≤ 1/4) :
    0 < Real.log (1/δ) :=
  Real.log_pos ((one_lt_div hδ).mpr (by linarith))

theorem confidenceScale_pos {B δ : ℝ} (hB : 0 < B) (hδ : 0 < δ) (hδle : δ ≤ 1/4) :
    0 < confidenceScale B δ :=
  Real.sqrt_pos.mpr (div_pos (confidence_log_pos hδ hδle) hB)

/-- A radius smaller than half a two-point separation gives a test with
both error probabilities at most the asserted confidence failure level. -/
theorem confidence_testing_bound {Ω : Type} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (f : Ω → ℝ) (hf : Measurable f) (a b r δ : ℝ)
    (hδ : 0 < δ) (hδle : δ ≤ 1/4) (hr : 2*r < a-b)
    (hP : P {z | r < |f z-a|} ≤ ENNReal.ofReal δ)
    (hQ : Q {z | r < |f z-b|} ≤ ENNReal.ofReal δ) :
    ENNReal.ofReal (Real.log (1/δ)/4) ≤ klDiv P Q := by
  let s : Set Ω := {z | (a+b)/2 < f z}
  have hs : MeasurableSet s := measurableSet_lt measurable_const hf
  have hPc : P sᶜ ≤ ENNReal.ofReal δ := by
    apply le_trans (measure_mono ?_) hP
    intro z hz
    have hz' : f z ≤ (a+b)/2 := not_lt.mp hz
    change r < |f z-a|
    have ha := neg_le_abs (f z-a)
    linarith
  have hQs : Q s ≤ ENNReal.ofReal δ := by
    apply le_trans (measure_mono ?_) hQ
    intro z hz
    change r < |f z-b|
    have hb := le_abs_self (f z-b)
    change (a+b)/2 < f z at hz
    linarith
  apply klDiv_confidence_separation P Q s hs δ hδ hδle
  · have hc := ENNReal.toReal_le_of_le_ofReal hδ.le hPc
    change P.real sᶜ ≤ δ at hc
    rw [probReal_compl_eq_one_sub hs] at hc
    linarith
  · exact ENNReal.toReal_le_of_le_ofReal hδ.le hQs

theorem confidence_algorithm_lower : ConfidenceAlgorithmLowerStatement := by
  intro R _ μ _ A B δ r hB hδ hδle hr hbudget hconfidence
  have hB0 : 0 < B := by linarith
  have hs0 := confidenceScale_pos hB0 hδ hδle
  let h := confidenceScale B δ / 8
  have hh : 0 < h := by dsimp [h]; positivity
  let hv := hard_pair_validity h hh
  let qp : SignLaw := ⟨hardPlus h, hv.2.1, fun d => (hv.2.2.2 d).2.2.1⟩
  let qm : SignLaw := ⟨hardMinus h, hv.2.2.1, fun d => (hv.2.2.2 d).2.2.2⟩
  let a := signMean μ qp.val
  let b := signMean μ qm.val
  have hsep : a-b = (1/4:ℝ)*modulus μ h := hard_pair_separation μ h hh
  have hscale := modulus_scaling μ (1/8) (confidenceScale B δ)
    (by norm_num) (by norm_num) hs0.le
  have hscale' : modulus μ (confidenceScale B δ)/8 ≤ modulus μ h := by
    have he : (1/8 : ℝ)*confidenceScale B δ = h := by dsimp [h]; ring
    rw [he] at hscale
    linarith
  have hsq : (confidenceScale B δ)^2 * B = Real.log (1/δ) := by
    rw [confidenceScale, Real.sq_sqrt (div_nonneg (confidence_log_pos hδ hδle).le hB0.le)]
    exact div_mul_cancel₀ _ (ne_of_gt hB0)
  have hkl := hard_pair_information μ A B h hh hbudget
  change klDiv (experimentLaw μ A qp) (experimentLaw μ A qm) ≤ _ at hkl
  have hkl' : klDiv (experimentLaw μ A qp) (experimentLaw μ A qm) <
      ENNReal.ofReal (Real.log (1/δ)/4) := by
    apply lt_of_le_of_lt hkl
    apply (ENNReal.ofReal_lt_ofReal_iff
      (div_pos (confidence_log_pos hδ hδle) (by norm_num))).mpr
    dsimp [h]
    nlinarith [confidence_log_pos hδ hδle]
  by_contra hn
  have hsmall : 2*r < a-b := by
    have hn' := lt_of_not_ge hn
    linarith
  have htest := confidence_testing_bound (experimentLaw μ A qp) (experimentLaw μ A qm)
    (populationOutput A) (measurable_populationOutput A) a b r δ hδ hδle hsmall
    (hconfidence qp) (hconfidence qm)
  exact (not_le_of_gt hkl') htest

theorem minimax_confidence_lower (μ : Measure Gap) [IsProbabilityMeasure μ]
    (B δ : ℝ) (hB : 1 ≤ B) (hδ : 0 < δ) (hδle : δ ≤ 1/4) :
    ENNReal.ofReal (modulus μ (confidenceScale B δ)/64) ≤ minimaxConfidenceRadius μ B δ := by
  apply le_sInf
  rintro t ⟨R, mR, A, r, hr, hb, hc, rfl⟩
  exact ENNReal.ofReal_le_ofReal (confidence_algorithm_lower R μ A B δ r hB hδ hδle hr hb hc)

end ThresholdHC.Confidence
