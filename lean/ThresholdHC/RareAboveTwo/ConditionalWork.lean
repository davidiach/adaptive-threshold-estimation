import ThresholdHC.RareAboveTwo.PopulationError
import ThresholdHC.RareAboveTwo.StageWork

/-! Work per sign and gap before integration over the unknown gap law. -/
noncomputable section
open MeasureTheory
namespace ThresholdHC.RareAboveTwo
open ThresholdHC.Tier6 ThresholdHC.Uniform713 ThresholdHC.ObservableSimulation

theorem threshold_envelopes (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (j k : ℕ) :
    negativeThreshold j k ≤ 5*((j : ℝ)+1)*((k : ℝ)+1) ∧
    positiveThreshold ρ j k ≤ (5*((j : ℝ)+1)*(1+Real.log (1/ρ)))*((k : ℝ)+1) := by
  have hJ : 1 ≤ (j : ℝ)+1 := by have := Nat.cast_nonneg (α := ℝ) j; linarith
  have hK : 1 ≤ (k : ℝ)+1 := by have := Nat.cast_nonneg (α := ℝ) k; linarith
  have hJK : 1 ≤ ((j : ℝ)+1)*((k : ℝ)+1) := one_le_mul_of_one_le_of_one_le hJ hK
  have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at hlog
  have hρlog := Real.log_nonneg ((one_le_div hρ).2 hρ1)
  have hneg : negativeThreshold j k ≤ 5*((j : ℝ)+1)*((k : ℝ)+1) := by
    unfold negativeThreshold
    have h := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 4*((j : ℝ)+1)+((k : ℝ)+1))
    have hj := mul_le_mul_of_nonneg_left hK (by positivity : 0 ≤ (j : ℝ)+1)
    have hk := mul_le_mul_of_nonneg_right hJ (by positivity : 0 ≤ (k : ℝ)+1)
    nlinarith only [h,hj,hk]
  refine ⟨hneg,?_⟩
  have hprod := mul_le_mul_of_nonneg_right hJK hρlog
  unfold positiveThreshold
  nlinarith only [hneg,hprod,hρlog]

theorem calibratedCost_integrable (μ : Measure (ℕ → Bool)) [IsProbabilityMeasure μ]
    (a ρ : ℝ) (j : ℕ) : Integrable (fun ω => (calibratedCost a ρ j ω : ℝ)) μ := by
  apply Integrable.of_bound
    ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp (measurable_calibratedCost a ρ j)).aestronglyMeasurable
    (cap (initialLevel a+terminalLevel ρ j))
  exact ae_of_all _ (fun ω => by
    change ‖(calibratedCost a ρ j ω : ℝ)‖ ≤ _
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
    have h := (Nat.cast_le (α := ℝ)).2 (bandCost_le (initialLevel a) (negativeThreshold j) (positiveThreshold ρ j) (terminalLevel ρ j) ω)
    simpa only [calibratedCost,cap,Nat.cast_pow,Nat.cast_ofNat] using h)

theorem calibratedCost_conditional_bound (a ρ p : ℝ) (ha : 0 < a) (ha' : a ≤ 1/2)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hp : 1 < p) (j : ℕ) (d : Gap) (b : Bool) :
    (∫ ω, (calibratedCost a ρ j ω : ℝ) ∂Tier2.tapeMeasure (gapParameter b d)) ≤
      cap (initialLevel a)*(1+workCoefficient p*(5*((j : ℝ)+1))^p*
        (if b then (1+Real.log (1/ρ))^p else 1)*(a/(d : ℝ))^(2*p)) := by
  let e := initialLevel a
  let L := terminalLevel ρ j
  let m := fun k => dyadicMean Tier2.observations (e+k)
  have hm (k : ℕ) : Measurable (m k) := measurable_prefixMean Tier2.measurable_observations _
  have ht := Tier2.tape_mean_tails (gapParameter b d)
  have hcost : (fun ω => (calibratedCost a ρ j ω : ℝ)) =
      fun ω => cap (e+bandStop e (negativeThreshold j) (positiveThreshold ρ j) (fun k => m k ω) L) := by
    funext ω
    simp [calibratedCost,bandCost,cap,e,L,m]
  rw [hcost]
  have hF : 1 ≤ 5*((j : ℝ)+1) := by have := Nat.cast_nonneg (α := ℝ) j; linarith
  have hℓ : 1 ≤ 1+Real.log (1/ρ) := by linarith [Real.log_nonneg ((one_le_div hρ).2 hρ1)]
  cases b with
  | false =>
    change HasMeanTails _ _ (1/2-(d : ℝ)) at ht
    have hb := band_work_power_bound (Tier2.tapeMeasure (gapParameter false d)) m hm e L
      (negativeThreshold j) (positiveThreshold ρ j) (negativeThreshold j)
      a (d : ℝ) p (5*((j : ℝ)+1)) ha d.property.1 hp hF
      (initialLevel_bounds a ha ha').1 (negativeThreshold_nonneg j)
      (fun k => (threshold_envelopes ρ hρ hρ1 j k).1)
      (fun k => band_survival_negative e (negativeThreshold j) (positiveThreshold ρ j)
        (negativeThreshold_nonneg j) L k d.property.1 ht)
    simpa only [Bool.false_eq_true,ite_false,mul_one] using hb
  | true =>
    change HasMeanTails _ _ (1/2+(d : ℝ)) at ht
    have hb := band_work_power_bound (Tier2.tapeMeasure (gapParameter true d)) m hm e L
      (negativeThreshold j) (positiveThreshold ρ j) (positiveThreshold ρ j)
      a (d : ℝ) p (5*((j : ℝ)+1)*(1+Real.log (1/ρ))) ha d.property.1 hp
      (one_le_mul_of_one_le_of_one_le hF hℓ) (initialLevel_bounds a ha ha').1
      (positiveThreshold_nonneg ρ hρ hρ1 j)
      (fun k => (threshold_envelopes ρ hρ hρ1 j k).2)
      (fun k => band_survival_positive e (negativeThreshold j) (positiveThreshold ρ j)
        (positiveThreshold_nonneg ρ hρ hρ1 j) L k d.property.1 ht)
    simp only [Real.mul_rpow (by positivity : 0 ≤ 5*((j : ℝ)+1)) (by linarith : 0 ≤ 1+Real.log (1/ρ))] at hb
    simpa only [ite_true,mul_assoc] using hb

end ThresholdHC.RareAboveTwo
