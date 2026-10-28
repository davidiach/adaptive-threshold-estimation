import ThresholdHC.BlindUpper.CalibrationBundle
import ThresholdHC.BlindUpper.PaddedCall
import ThresholdHC.BlindUpper.CutoffModulus

noncomputable section
namespace ThresholdHC.BlindUpper
open MeasureTheory ProbabilityTheory ThresholdHC.Tier6
open scoped ENNReal

def paddedRealCost (L : ℕ) (z : ℕ × (ℕ → Bool)) : ℝ := paddedCutoffCost L z

theorem measurable_paddedRealCost (L : ℕ) : Measurable (paddedRealCost L) :=
  (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp (measurable_paddedCutoffCost L)

theorem paddedRealCost_bounds (L : ℕ) (z : ℕ × (ℕ → Bool)) :
    0 ≤ paddedRealCost L z ∧ paddedRealCost L z ≤ (2 : ℝ)^L :=
  ⟨Nat.cast_nonneg _,by
    change (paddedCutoffCost L z : ℝ) ≤ (2 : ℝ)^L
    exact_mod_cast (paddedCutoffCost_bounds L z).2⟩

def paddedMark (L : ℕ) : (ℕ × (ℕ → Bool)) → unitInterval :=
  costParameter ((2 : ℝ)^L) (by positivity) (paddedRealCost L) (paddedRealCost_bounds L)

def cutoffBatchOutput (L : ℕ) : CalibrationState (ℕ × (ℕ → Bool)) → ℝ :=
  calibrationOutput (paddedMark L) (cutoffValue L)

def cutoffBatchWork (L : ℕ) : CalibrationState (ℕ × (ℕ → Bool)) → ℝ≥0∞ :=
  calibrationWork (paddedMark L) (paddedRealCost L)

theorem cutoffBatch_budget (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    (∫⁻ z, cutoffBatchWork L z ∂calibrationLaw (callMeasure μ q)) ≤ ENNReal.ofReal (4*(2 : ℝ)^L) :=
  calibration_cost_budget (callMeasure μ q) ((2 : ℝ)^L) (by positivity) (paddedRealCost L)
    (paddedRealCost_bounds L) (measurable_paddedRealCost L)
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (paddedCutoff_work_lower L μ q))

/-- Statistical call-array bound. Realization by an observable population
policy is a separate requirement. Padding changes the scalar factor to12751. -/
theorem cutoffBatch_mse (L : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    (∫⁻ z, ENNReal.ofReal ((cutoffBatchOutput L z-signMean μ q.val)^2)
      ∂calibrationLaw (callMeasure μ q)) ≤
      ENNReal.ofReal (12751*(modulus μ (1/Real.sqrt ((2 : ℝ)^L)))^2) := by
  let ν := callMeasure μ q
  let A : ℝ := ∫ d, callScale L d ∂μ
  let w : ℝ := modulus μ (1/Real.sqrt ((2 : ℝ)^L))
  let c : ℝ := ∫ z, paddedRealCost L z ∂ν
  let v : ℝ := variance (cutoffValue L) ν
  let b : ℝ := (∫ z, cutoffValue L z ∂ν)-signMean μ q.val
  have hZ : MemLp (cutoffValue L) 2 ν :=
    (memLp_two_iff_integrable_sq (measurable_cutoffValue L).aestronglyMeasurable).mpr
      (cutoff_call_sq_integrable L μ q)
  have hc : 0 < c := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (paddedCutoff_work_lower L μ q)
  have he : (∫⁻ z, ENNReal.ofReal ((cutoffBatchOutput L z-signMean μ q.val)^2) ∂calibrationLaw ν) =
      ENNReal.ofReal (v*c/(2 : ℝ)^L+b^2) :=
    calibration_cost_mse ν ((2 : ℝ)^L) (by positivity) (paddedRealCost L) (paddedRealCost_bounds L)
      (measurable_paddedRealCost L) hc (cutoffValue L) (measurable_cutoffValue L) hZ (signMean μ q.val)
  rw [he]
  apply ENNReal.ofReal_le_ofReal
  have hv : v ≤ 85*A := (variance_le_expectation_sq (measurable_cutoffValue L).aestronglyMeasurable).trans
    (cutoff_call_second_real_le L μ q)
  have hcu : c ≤ 150*A := paddedCutoff_work_upper L μ q
  have hA₀ : 0 ≤ A := (by norm_num : (0 : ℝ) ≤ 1).trans (callScale_integral_one_le L μ)
  have hw : 0 ≤ w := modulus_nonneg μ (by positivity)
  have hb : |b| ≤ w := (cutoff_call_bias_le L μ q).trans (callBiasScale_integral_le_modulus L μ)
  have hb₂ : b^2 ≤ w^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg b) hw).mpr hb
  have hprod : v*c/(2 : ℝ)^L ≤ (85*A)*(150*A)/(2 : ℝ)^L :=
    div_le_div_of_nonneg_right (mul_le_mul hv hcu hc.le (by positivity)) (by positivity)
  have hA : A = Real.sqrt ((2 : ℝ)^L)*w := callScale_integral_eq_modulus L μ
  have hscale : (85*A)*(150*A)/(2 : ℝ)^L = 12750*w^2 := by
    rw [hA]
    calc
      _ = 12750*(Real.sqrt ((2 : ℝ)^L))^2*w^2/(2 : ℝ)^L := by ring
      _ = _ := by rw [Real.sq_sqrt (by positivity)]; field_simp
  rw [hscale] at hprod
  change v*c/(2 : ℝ)^L+b^2 ≤ 12751*w^2
  linarith

end ThresholdHC.BlindUpper
