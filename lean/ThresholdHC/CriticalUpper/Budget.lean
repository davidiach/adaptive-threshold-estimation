import ThresholdHC.CriticalUpper.FixedBounds
import ThresholdHC.CriticalUpper.Specification
import ThresholdHC.Tier6.RiskReduction

/-! Budget-dependent sample count and the zero-work saturation regime. -/

noncomputable section
namespace ThresholdHC.CriticalUpper
open MeasureTheory ProbabilityTheory Set ThresholdHC.CriticalEntropy ThresholdHC.Uniform713
open ThresholdHC.Tier2 ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.Tier6
open ThresholdHC.ObservableSimulation ThresholdHC.BlindUpper
open scoped ENNReal

def criticalWorkScale (ρ : ℝ) : ℝ := 112000000*criticalLogFactor ρ

theorem criticalWorkScale_pos (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) : 0 < criticalWorkScale ρ :=
  mul_pos (by norm_num) (criticalLogFactor_pos ρ hρ hρ1)

def criticalBatchIndex (ρ B : ℝ) : ℕ := ⌊B/(2*criticalWorkScale ρ)⌋₊

theorem criticalBatchIndex_bounds (ρ B : ℝ) (hρ : 0 < ρ) (hρh : ρ ≤ 1/2)
    (hlarge : criticalWorkScale ρ/ρ ≤ B) :
    ((criticalBatchIndex ρ B : ℝ)+1)*criticalWorkScale ρ ≤ B ∧
      B/(2*criticalWorkScale ρ) ≤ (criticalBatchIndex ρ B : ℝ)+1 := by
  have hW := criticalWorkScale_pos ρ hρ (by linarith)
  have hB : 0 < B := (div_pos hW hρ).trans_le hlarge
  have hWB : 2*criticalWorkScale ρ ≤ B := by
    have h := (div_le_iff₀ hρ).mp hlarge
    have hb := mul_le_mul_of_nonneg_left hρh hB.le
    nlinarith
  have hfloor := Nat.floor_le (by positivity : 0 ≤ B/(2*criticalWorkScale ρ))
  have hfloor' := Nat.lt_floor_add_one (B/(2*criticalWorkScale ρ))
  change (criticalBatchIndex ρ B : ℝ) ≤ B/(2*criticalWorkScale ρ) at hfloor
  change B/(2*criticalWorkScale ρ) < (criticalBatchIndex ρ B : ℝ)+1 at hfloor'
  constructor
  · have h := mul_le_mul_of_nonneg_right hfloor hW.le
    have he : B/(2*criticalWorkScale ρ)*criticalWorkScale ρ = B/2 := by field_simp
    rw [he] at h
    nlinarith
  · exact hfloor'.le

theorem critical_largeBudget_square_bound (ρ B : ℝ) (hρ : 0 < ρ) (hρh : ρ ≤ 1/2)
    (hlarge : criticalWorkScale ρ/ρ ≤ B) :
    28*ρ/((criticalBatchIndex ρ B : ℝ)+1) ≤
      (100000*Real.sqrt (ρ*criticalLogFactor ρ/B))^2 := by
  have hW := criticalWorkScale_pos ρ hρ (by linarith)
  have hF := criticalLogFactor_pos ρ hρ (by linarith)
  have hB : 0 < B := (div_pos hW hρ).trans_le hlarge
  have hx : 0 ≤ ρ*criticalLogFactor ρ/B := by positivity
  have hn := (criticalBatchIndex_bounds ρ B hρ hρh hlarge).2
  calc
    _ ≤ 28*ρ/(B/(2*criticalWorkScale ρ)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hn
    _ = 6272000000*(ρ*criticalLogFactor ρ/B) := by unfold criticalWorkScale; field_simp; ring
    _ ≤ _ := by nlinarith [Real.sq_sqrt hx]

theorem critical_largeBudget_sqrt_le (ρ B : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hlarge : criticalWorkScale ρ/ρ ≤ B) : Real.sqrt (ρ*criticalLogFactor ρ/B) ≤ ρ := by
  have hF := criticalLogFactor_pos ρ hρ hρ1
  have hW := criticalWorkScale_pos ρ hρ hρ1
  have hB : 0 < B := (div_pos hW hρ).trans_le hlarge
  have hx : 0 ≤ ρ*criticalLogFactor ρ/B := by positivity
  have hb := (div_le_iff₀ hρ).mp hlarge
  have hsmall : ρ*criticalLogFactor ρ/B ≤ ρ^2 := by
    apply (div_le_iff₀ hB).mpr
    unfold criticalWorkScale at hb
    have hf : criticalLogFactor ρ ≤ B*ρ := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hf hρ.le]
  nlinarith [Real.sq_sqrt hx,Real.sqrt_nonneg (ρ*criticalLogFactor ρ/B)]

theorem critical_smallBudget_bound (ρ B : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hB : 0 < B)
    (hsmall : B < criticalWorkScale ρ/ρ) :
    ρ ≤ 100000*min ρ (Real.sqrt (ρ*criticalLogFactor ρ/B)) := by
  have hF := criticalLogFactor_pos ρ hρ hρ1
  have hx : 0 ≤ ρ*criticalLogFactor ρ/B := by positivity
  have hb := (lt_div_iff₀ hρ).mp hsmall
  unfold criticalWorkScale at hb
  have hsq : ρ^2 ≤ 112000000*(ρ*criticalLogFactor ρ/B) := by
    have hm := mul_le_mul_of_nonneg_left hb.le hρ.le
    calc
      ρ^2 ≤ (112000000*(ρ*criticalLogFactor ρ))/B := (le_div_iff₀ hB).mpr (by nlinarith)
      _ = _ := by ring
  rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 100000)]
  apply le_min
  · nlinarith
  · nlinarith [Real.sq_sqrt hx,Real.sqrt_nonneg (ρ*criticalLogFactor ρ/B)]

def idleCriticalEstimator : AdaptiveEstimator CriticalSeed where
  randomLaw := criticalSeedLaw
  probability := criticalSeedLaw_probability
  policy := fun _ _ => none
  policy_measurable := fun _ _ => measurableSet_eq_fun measurable_const measurable_const
  output := fun _ => 0
  output_measurable := measurable_const

theorem idleCritical_work (q : ℝ → unitInterval) (hq : Measurable q) :
    criticalExpectedWork idleCriticalEstimator q hq = 0 := by
  rw [critical_expectedWork_simulation]
  have hz (z : CriticalSeed × (ℕ → ℕ → Bool)) :
      totalProcessWork (populationPath (idleCriticalEstimator.policy z.1) z.2) = 0 := by
    rw [populationPath_none _ _ rfl]
    simp [totalProcessWork,ThresholdHC.workOf,processPrefix]
  simp_rw [hz]
  simp

theorem idleCritical_risk (ρ : ℝ) : criticalMaximalRMSRisk idleCriticalEstimator ρ ≤ ENNReal.ofReal ρ := by
  apply iSup_le
  intro q
  apply iSup_le
  intro hq
  apply iSup_le
  intro hmass
  let a := ∫ d, (q d : ℝ) ∂criticalGapLaw
  have ha : 0 ≤ a := integral_nonneg (fun d => (q d).property.1)
  have heq : squaredRisk (criticalExperimentLaw idleCriticalEstimator q hq)
      (fun z => idleCriticalEstimator.output (z.1.1,z.2)) a = ENNReal.ofReal (a^2) := by
    simp [squaredRisk,idleCriticalEstimator]
  unfold rootMeanRisk
  change squaredRisk _ _ a ^ (1/2 : ℝ) ≤ _
  rw [heq,ofReal_square_rpow_half a ha]
  exact ENNReal.ofReal_le_ofReal hmass

def criticalBudgetEstimator (ρ B : ℝ) : AdaptiveEstimator CriticalSeed :=
  if criticalWorkScale ρ/ρ ≤ B then fixedEstimator ρ (criticalBatchIndex ρ B) else idleCriticalEstimator

end ThresholdHC.CriticalUpper
