import ThresholdHC.CriticalEntropy.UniformCoin
import ThresholdHC.Proofs.Calibration

noncomputable section
namespace ThresholdHC.BlindUpper
open MeasureTheory ProbabilityTheory ThresholdHC.CriticalEntropy
open scoped ENNReal NNReal

theorem unitParameter_integrable {X : Type} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (P : X → unitInterval) (hP : Measurable P) :
    Integrable (fun x => (P x : ℝ)) ν := by
  apply Integrable.of_bound (measurable_subtype_coe.comp hP).aestronglyMeasurable 1
  exact ae_of_all _ (fun x => by
    change ‖(P x : ℝ)‖ ≤ 1
    rw [Real.norm_eq_abs,abs_of_nonneg (P x).property.1]; exact (P x).property.2)

def meanParameter {X : Type} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (P : X → unitInterval) (hP : Measurable P) : unitInterval :=
  ⟨∫ x, (P x : ℝ) ∂ν, integral_nonneg (fun x => (P x).property.1),by
    have h := integral_mono (unitParameter_integrable ν P hP) (integrable_const (1 : ℝ))
      (fun x => (P x).property.2)
    simpa using h⟩

def callMark {X : Type} (P : X → unitInterval) (z : X × ℝ) : Bool := uniformCoinFlip (P z.1) z.2

theorem measurable_callMark {X : Type} [MeasurableSpace X]
    (P : X → unitInterval) (hP : Measurable P) : Measurable (callMark P) :=
  measurable_uniformCoinFlip.comp ((hP.comp measurable_fst).prodMk measurable_snd)

theorem callMark_true {X : Type} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (P : X → unitInterval) (hP : Measurable P) :
    (ν.prod uniformUnitMeasure) {z | callMark P z = true} = ENNReal.ofReal (meanParameter ν P hP : ℝ) := by
  rw [Measure.prod_apply (measurableSet_eq_fun (measurable_callMark P hP) measurable_const)]
  have he (x : X) : uniformUnitMeasure (Prod.mk x ⁻¹' {z | callMark P z = true}) =
      ENNReal.ofReal (P x : ℝ) := uniformCoinFlip_true (P x)
  simp_rw [he]
  exact (ofReal_integral_eq_lintegral_ofReal (unitParameter_integrable ν P hP)
    (ae_of_all _ (fun x => (P x).property.1))).symm

theorem callMark_map {X : Type} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (P : X → unitInterval) (hP : Measurable P) :
    (ν.prod uniformUnitMeasure).map (callMark P) = bernoulliMeasure true false (meanParameter ν P hP) := by
  let p := meanParameter ν P hP
  have hm := measurable_callMark P hP
  let : IsProbabilityMeasure ((ν.prod uniformUnitMeasure).map (callMark P)) :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).2 inferInstance
  have ht : ((ν.prod uniformUnitMeasure).map (callMark P)) {true} =
      bernoulliMeasure true false p {true} := by
    rw [Measure.map_apply hm (measurableSet_singleton true)]
    change (ν.prod uniformUnitMeasure) {z | callMark P z = true} = _
    rw [callMark_true ν P hP]
    simp [bernoulliMeasure_def]
    change ENNReal.ofReal ((unitInterval.toNNReal p : ℝ≥0) : ℝ) =
      ((unitInterval.toNNReal p : ℝ≥0) : ℝ≥0∞)
    simp only [ENNReal.ofReal_coe_nnreal]
  apply Measure.ext_of_singleton
  intro b
  cases b with
  | true => exact ht
  | false =>
    have hc : ({false} : Set Bool) = {true}ᶜ := by ext b; cases b <;> simp
    rw [hc,prob_compl_eq_one_sub (measurableSet_singleton true),
      prob_compl_eq_one_sub (measurableSet_singleton true),ht]

/-- The entire sequence of randomized marks has the exact iid Bernoulli law.
The marking function depends only on the realized call and fresh randomness. -/
theorem callMarks_map {X : Type} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (P : X → unitInterval) (hP : Measurable P) :
    (Measure.infinitePi (fun _ : ℕ => ν.prod uniformUnitMeasure)).map
      (fun z n => callMark P (z n)) = Tier2.tapeMeasure (meanParameter ν P hP) := by
  rw [Measure.infinitePi_map_pi _ (fun _ => measurable_callMark P hP)]
  simp_rw [callMark_map ν P hP]
  rfl

def costParameter {X : Type} (N : ℝ) (hN : 0 < N) (C : X → ℝ)
    (hC : ∀ x, 0 ≤ C x ∧ C x ≤ N) (x : X) : unitInterval :=
  ⟨C x/N,div_nonneg (hC x).1 hN.le,(div_le_one hN).mpr (hC x).2⟩

theorem measurable_costParameter {X : Type} [MeasurableSpace X]
    (N : ℝ) (hN : 0 < N) (C : X → ℝ) (hC : ∀ x, 0 ≤ C x ∧ C x ≤ N)
    (hCm : Measurable C) : Measurable (costParameter N hN C hC) :=
  (hCm.div_const N).subtype_mk

theorem mean_costParameter {X : Type} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν]
    (N : ℝ) (hN : 0 < N) (C : X → ℝ) (hC : ∀ x, 0 ≤ C x ∧ C x ≤ N)
    (hCm : Measurable C) :
    (meanParameter ν (costParameter N hN C hC) (measurable_costParameter N hN C hC hCm) : ℝ) =
      (∫ x, C x ∂ν)/N := integral_div N C

end ThresholdHC.BlindUpper
