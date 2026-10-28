import ThresholdHC.BlindUpper.PilotCost
import ThresholdHC.BlindUpper.PilotCount
import ThresholdHC.BlindUpper.MixedProduction

noncomputable section
namespace ThresholdHC.BlindUpper
open MeasureTheory ProbabilityTheory ThresholdHC.CriticalEntropy
open scoped ENNReal

abbrev CalibrationState (X : Type) := ((ℕ → X × ℝ) × (ℕ → X × ℝ)) × (ℕ → X)

def calibrationLaw {X : Type} [MeasurableSpace X] (ν : Measure X) : Measure (CalibrationState X) :=
  ((markedSequenceLaw ν).prod (markedSequenceLaw ν)).prod (Measure.infinitePi (fun _ : ℕ => ν))

instance calibrationLaw_probability {X : Type} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] : IsProbabilityMeasure (calibrationLaw ν) := by
  unfold calibrationLaw; infer_instance

def calibrationCountInput {X : Type} (P : X → unitInterval) (z : CalibrationState X) : ℕ × (ℕ → X) :=
  (twoPilotFailures P z.1,z.2)

theorem measurable_calibrationCountInput {X : Type} [MeasurableSpace X]
    (P : X → unitInterval) (hP : Measurable P) : Measurable (calibrationCountInput P) :=
  ((measurable_twoPilotFailures P hP).comp measurable_fst).prodMk measurable_snd

theorem calibrationCountInput_preserving {X : Type} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (P : X → unitInterval) (hP : Measurable P)
    (hp : meanParameter ν P hP ≠ 0) :
    MeasurePreserving (calibrationCountInput P) (calibrationLaw ν)
      ((doubleFailuresLaw (meanParameter ν P hP)).prod (Measure.infinitePi (fun _ : ℕ => ν))) := by
  refine ⟨measurable_calibrationCountInput P hP,?_⟩
  change (calibrationLaw ν).map (Prod.map (twoPilotFailures P) id) = _
  rw [calibrationLaw,← Measure.map_prod_map _ _ (measurable_twoPilotFailures P hP) measurable_id,
    Measure.map_id,twoPilotFailures_map ν P hP hp]

def calibrationOutput {X : Type} (P : X → unitInterval) (Z : X → ℝ) (z : CalibrationState X) : ℝ :=
  productionAverage Z (twoPilotFailures P z.1) z.2

def calibrationWork {X : Type} (P : X → unitInterval) (C : X → ℝ) (z : CalibrationState X) : ℝ≥0∞ :=
  twoPilotWork P (fun x => ENNReal.ofReal (C x)) z.1 +
    ENNReal.ofReal (productionCost C (twoPilotFailures P z.1) z.2)

theorem measurable_calibrationOutput {X : Type} [MeasurableSpace X]
    (P : X → unitInterval) (hP : Measurable P) (Z : X → ℝ) (hZ : Measurable Z) :
    Measurable (calibrationOutput P Z) :=
  (measurable_productionAverage_joint Z hZ).comp (measurable_calibrationCountInput P hP)

theorem measurable_twoPilotWork {X : Type} [MeasurableSpace X]
    (P : X → unitInterval) (hP : Measurable P) (C : X → ℝ≥0∞) (hC : Measurable C) :
    Measurable (twoPilotWork P C) :=
  ((measurable_firstPilotWork P hP C hC).comp measurable_fst).add
    ((measurable_firstPilotWork P hP C hC).comp measurable_snd)

theorem measurable_calibrationWork {X : Type} [MeasurableSpace X]
    (P : X → unitInterval) (hP : Measurable P) (C : X → ℝ) (hC : Measurable C) :
    Measurable (calibrationWork P C) :=
  ((measurable_twoPilotWork P hP (fun x => ENNReal.ofReal (C x))
    (ENNReal.measurable_ofReal.comp hC)).comp measurable_fst).add
    (ENNReal.measurable_ofReal.comp ((measurable_productionCost_joint C hC).comp
      (measurable_calibrationCountInput P hP)))

theorem calibration_mse {X : Type} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (P : X → unitInterval) (hP : Measurable P)
    (hp : 0 < (meanParameter ν P hP : ℝ)) (Z : X → ℝ) (hZm : Measurable Z)
    (hZ : MemLp Z 2 ν) (a : ℝ) :
    (∫⁻ z, ENNReal.ofReal ((calibrationOutput P Z z-a)^2) ∂calibrationLaw ν) =
      ENNReal.ofReal (variance Z ν*(meanParameter ν P hP : ℝ)+((∫ x, Z x ∂ν)-a)^2) := by
  have hp' : meanParameter ν P hP ≠ 0 := by intro h; simp [h] at hp
  have hm : Measurable (fun z : ℕ × (ℕ → X) => ENNReal.ofReal ((productionAverage Z z.1 z.2-a)^2)) :=
    ENNReal.measurable_ofReal.comp (((measurable_productionAverage_joint Z hZm).sub measurable_const).pow_const 2)
  exact ((calibrationCountInput_preserving ν P hP hp').lintegral_comp hm).trans
    (mixedProduction_mse ν Z hZm hZ _ hp a)

theorem calibration_cost_mse {X : Type} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (N : ℝ) (hN : 0 < N)
    (C : X → ℝ) (hC : ∀ x, 0 ≤ C x ∧ C x ≤ N) (hCm : Measurable C)
    (hc : 0 < ∫ x, C x ∂ν) (Z : X → ℝ) (hZm : Measurable Z) (hZ : MemLp Z 2 ν) (a : ℝ) :
    (∫⁻ z, ENNReal.ofReal ((calibrationOutput (costParameter N hN C hC) Z z-a)^2) ∂calibrationLaw ν) =
      ENNReal.ofReal (variance Z ν*(∫ x, C x ∂ν)/N+((∫ x, Z x ∂ν)-a)^2) := by
  have hp : 0 < (meanParameter ν (costParameter N hN C hC)
      (measurable_costParameter N hN C hC hCm) : ℝ) := by
    rw [mean_costParameter ν N hN C hC hCm]
    exact div_pos hc hN
  rw [calibration_mse ν _ (measurable_costParameter N hN C hC hCm) hp Z hZm hZ a,
    mean_costParameter ν N hN C hC hCm]
  congr 1
  ring

theorem calibration_cost_work {X : Type} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (N : ℝ) (hN : 0 < N)
    (C : X → ℝ) (hC : ∀ x, 0 ≤ C x ∧ C x ≤ N) (hCm : Measurable C)
    (hc : 0 < ∫ x, C x ∂ν) :
    (∫⁻ z, calibrationWork (costParameter N hN C hC) C z ∂calibrationLaw ν) =
      ENNReal.ofReal (4*N-∫ x, C x ∂ν) := by
  let P := costParameter N hN C hC
  have hP : Measurable P := measurable_costParameter N hN C hC hCm
  let p := meanParameter ν P hP
  have hp : 0 < (p : ℝ) := by
    rw [show (p : ℝ) = (∫ x, C x ∂ν)/N from mean_costParameter ν N hN C hC hCm]
    exact div_pos hc hN
  have hp' : p ≠ 0 := by intro h; simp [h] at hp
  have hi := boundedCost_integrable ν N C hC hCm
  have hcN : (∫ x, C x ∂ν) ≤ N := by
    have h := integral_mono hi (integrable_const N) (fun x => (hC x).2)
    simpa using h
  have hpilotm : Measurable (fun z : CalibrationState X =>
      twoPilotWork P (fun x => ENNReal.ofReal (C x)) z.1) :=
    (measurable_twoPilotWork P hP (fun x => ENNReal.ofReal (C x))
      (ENNReal.measurable_ofReal.comp hCm)).comp measurable_fst
  have hpilot : (∫⁻ z : CalibrationState X,
      twoPilotWork P (fun x => ENNReal.ofReal (C x)) z.1 ∂calibrationLaw ν) = ENNReal.ofReal (2*N) := by
    rw [calibrationLaw,lintegral_prod _ hpilotm.aemeasurable]
    simp only [lintegral_const,measure_univ,mul_one]
    exact twoPilotWork_cost_expectation ν N hN C hC hCm hc
  have hproductionm : Measurable (fun z : ℕ × (ℕ → X) => ENNReal.ofReal (productionCost C z.1 z.2)) :=
    ENNReal.measurable_ofReal.comp (measurable_productionCost_joint C hCm)
  have hproduction : (∫⁻ z : CalibrationState X,
      ENNReal.ofReal (productionCost C (twoPilotFailures P z.1) z.2) ∂calibrationLaw ν) =
      ENNReal.ofReal ((2/(p : ℝ)-1)*(∫ x, C x ∂ν)) :=
    ((calibrationCountInput_preserving ν P hP hp').lintegral_comp hproductionm).trans
      (mixedProduction_work ν C hCm hi (fun x => (hC x).1) p hp)
  have he : (2/(p : ℝ)-1)*(∫ x, C x ∂ν) = 2*N-(∫ x, C x ∂ν) := by
    rw [show (p : ℝ) = (∫ x, C x ∂ν)/N from mean_costParameter ν N hN C hC hCm]
    field_simp
  change (∫⁻ z : CalibrationState X,
    twoPilotWork P (fun x => ENNReal.ofReal (C x)) z.1+
      ENNReal.ofReal (productionCost C (twoPilotFailures P z.1) z.2) ∂calibrationLaw ν) = _
  rw [lintegral_add_left hpilotm,hpilot,hproduction,he,
    ← ENNReal.ofReal_add (by positivity : 0 ≤ 2*N) (by linarith : 0 ≤ 2*N-∫ x, C x ∂ν)]
  congr 1
  ring

theorem calibration_cost_budget {X : Type} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (N : ℝ) (hN : 0 < N)
    (C : X → ℝ) (hC : ∀ x, 0 ≤ C x ∧ C x ≤ N) (hCm : Measurable C)
    (hc : 0 < ∫ x, C x ∂ν) :
    (∫⁻ z, calibrationWork (costParameter N hN C hC) C z ∂calibrationLaw ν) ≤ ENNReal.ofReal (4*N) := by
  rw [calibration_cost_work ν N hN C hC hCm hc]
  exact ENNReal.ofReal_le_ofReal (sub_le_self _ hc.le)

end ThresholdHC.BlindUpper
