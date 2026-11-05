import ThresholdHC.LawAdaptation.Identification
import ThresholdHC.LawAdaptation.Concentration

noncomputable section
open MeasureTheory ProbabilityTheory Real
open scoped BigOperators ENNReal Classical
namespace ThresholdHC.LawAdaptation

/-- The actual signature rule has exponentially small error under independent
bounded observations with the true candidate's coordinate means. -/
theorem pilot_error {Ω ι : Type*} [MeasurableSpace Ω] [Nonempty ι]
    (P : Measure Ω) [IsProbabilityMeasure P] {m n : ℕ} (hn : 0 < n)
    (signature : ι → Fin m → ℝ) (truth : ι) (X : Fin m → Fin n → Ω → ℝ)
    {η : ℝ} (hη : 0 < η)
    (hdist : ∀ i j, i ≠ j → ∃ k, η ≤ |signature i k-signature j k|)
    (hm : ∀ k t, AEMeasurable (X k t) P)
    (hb : ∀ k t, ∀ᵐ ω ∂P, X k t ω ∈ Set.Icc (-1:ℝ) 1)
    (hi : ∀ k, iIndepFun (X k) P)
    (hmean : ∀ k t, ∫ ω, X k t ω ∂P = signature truth k) :
    P {ω | identify signature (fun k => (∑ t, X k t ω)/(n:ℝ)) (η/4) ≠ truth} ≤
      ENNReal.ofReal (2*(m:ℝ)*exp (-(n:ℝ)*η^2/32)) := by
  have hc (k : Fin m) :
      P {ω | η/4 < |(∑ t, X k t ω)/(n:ℝ)-signature truth k|} ≤
        ENNReal.ofReal (2*exp (-(n:ℝ)*η^2/32)) := by
    have h := bounded_average_tail P hn (X k) (hm k) (hb k) (hi k)
      (hmean k) (by positivity : 0 ≤ η/4)
    have he : -(n:ℝ)*(η/4)^2/2 = -(n:ℝ)*η^2/32 := by ring
    rw [he] at h
    have hh := ENNReal.ofReal_le_ofReal h
    simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using hh
  have h := identify_error_bound P signature
    (fun ω k => (∑ t, X k t ω)/(n:ℝ)) truth
    (by linarith : 2*(η/4) < η) hdist
    (fun _ => ENNReal.ofReal (2*exp (-(n:ℝ)*η^2/32))) hc
  convert h using 1
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg m)]
  congr 1
  ring

/-- Natural-log sample calibration for any positive failure allowance. -/
theorem pilot_calibration {m n : ℕ} (hm : 0 < m) {η δ : ℝ} (hd : 0 < δ)
    (hsize : log (2*(m:ℝ)/δ) ≤ (n:ℝ)*η^2/32) :
    2*(m:ℝ)*exp (-(n:ℝ)*η^2/32) ≤ δ := by
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have he := exp_le_exp.mpr (neg_le_neg hsize)
  have hp : 0 < 2*(m:ℝ)/δ := by positivity
  rw [exp_neg (log (2*(m:ℝ)/δ)), exp_log hp] at he
  have h := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 2*(m:ℝ))
  have hc : 2*(m:ℝ)*(2*(m:ℝ)/δ)⁻¹ = δ := by field_simp
  simpa only [neg_div, neg_mul, hc] using h

end ThresholdHC.LawAdaptation

