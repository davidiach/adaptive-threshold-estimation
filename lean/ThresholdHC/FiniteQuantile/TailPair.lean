import ThresholdHC.EntropyTailQuantile.QuantileTailBound
import ThresholdHC.StoppingProgram.RaritySupport

/-! The paper's two endpoint priors share the fractional quantile atom.
The hard parameters do not depend on the algorithm or the truncation cap. -/
noncomputable section
open MeasureTheory Set Real
open scoped ENNReal
namespace ThresholdHC.FiniteQuantile
open ThresholdHC.Tier6 ThresholdHC.EntropyTailQuantile ThresholdHC.RareAboveTwo

def cutWeight (t r : ℝ) (d : Gap) : ℝ :=
  if (d : ℝ) < t then 1 else if (d : ℝ) = t then r else 0

theorem cutWeight_range {t r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) (d : Gap) :
    cutWeight t r d ∈ Icc (0 : ℝ) 1 := by
  unfold cutWeight
  split_ifs <;> first | exact hr | norm_num

theorem measurable_cutWeight (t r : ℝ) : Measurable (cutWeight t r) :=
  Measurable.ite (measurableSet_lt measurable_subtype_coe measurable_const) measurable_const
    (Measurable.ite (measurableSet_eq_fun measurable_subtype_coe measurable_const)
      measurable_const measurable_const)

theorem integral_cutWeight (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (f : Gap → ℝ) (hf : Integrable f μ) :
    (∫ d, cutWeight (quantileThreshold μ ρ) (quantileBoundaryFraction μ ρ) d * f d ∂μ) =
      ∫ d, f d ∂quantileTail μ ρ := by
  classical
  let t := quantileThreshold μ ρ
  let r := quantileBoundaryFraction μ ρ
  let L := {d : Gap | (d:ℝ) < t}
  let E := {d : Gap | (d:ℝ) = t}
  have hL : MeasurableSet L := measurableSet_lt measurable_subtype_coe measurable_const
  have hE : MeasurableSet E := measurableSet_eq_fun measurable_subtype_coe measurable_const
  have he : (fun d => cutWeight t r d * f d) =
      fun d => L.indicator f d + r * E.indicator f d := by
    funext d
    by_cases hl : (d:ℝ) < t
    · simp [cutWeight, L, E, hl, ne_of_lt hl]
    · by_cases heq : (d:ℝ) = t <;> simp [cutWeight, L, E, hl, heq]
  change (∫ d, cutWeight t r d * f d ∂μ) = ∫ d, f d ∂(μ.restrict L + ENNReal.ofReal r • μ.restrict E)
  rw [he, integral_add (hf.indicator hL) ((hf.indicator hE).const_mul r),
    integral_const_mul, integral_indicator hL, integral_indicator hE,
    integral_add_measure hf.integrableOn (hf.integrableOn.smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, ENNReal.toReal_ofReal (quantileBoundaryFraction_properties μ hρ hρ1).1]
  rfl

def tailEpsilon (h : ℝ) (d : Gap) : ℝ := min 1 (h/(d:ℝ)) / 16

theorem tailEpsilon_bounds {h : ℝ} (hh : 0 ≤ h) (d : Gap) :
    0 ≤ tailEpsilon h d ∧ tailEpsilon h d ≤ 1/16 ∧ tailEpsilon h d * (d:ℝ) ≤ h/16 := by
  have hlo := tailKernel_nonneg hh d
  have hhi := min_le_left (1:ℝ) (h/(d:ℝ))
  have hprod := (le_div_iff₀ d.property.1).mp (min_le_right (1:ℝ) (h/(d:ℝ)))
  unfold tailEpsilon
  exact ⟨by positivity, by linarith, by linarith⟩

def tailEndpoint (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ h : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hh : 0 ≤ h) (plus : Bool) : SignLaw := by
  let w := cutWeight (quantileThreshold μ ρ) (quantileBoundaryFraction μ ρ)
  let e := tailEpsilon h
  refine ⟨fun d => w d * (1/2 + if plus then e d else -e d), ?_, ?_⟩
  · have he : Measurable e := by unfold e tailEpsilon; fun_prop
    cases plus <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;>
      exact (measurable_cutWeight _ _).mul (by fun_prop)
  · intro d
    have hw := cutWeight_range (t := quantileThreshold μ ρ)
      (show quantileBoundaryFraction μ ρ ∈ Icc (0:ℝ) 1 from
        ⟨(quantileBoundaryFraction_properties μ hρ hρ1).1,
         (quantileBoundaryFraction_properties μ hρ hρ1).2.1⟩) d
    have he := tailEpsilon_bounds hh d
    have hp : 0 ≤ (1/2 : ℝ) + (if plus then e d else -e d) ∧
        (1/2 : ℝ) + (if plus then e d else -e d) ≤ 1 := by
      dsimp only [e]; cases plus <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;>
        constructor <;> linarith [he.1, he.2.1]
    exact ⟨mul_nonneg hw.1 hp.1, (mul_le_mul_of_nonneg_left hp.2 hw.1).trans (by simpa using hw.2)⟩

theorem tailEndpoint_mean (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ h : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hh : 0 ≤ h) (plus : Bool) :
    signMean μ (tailEndpoint μ hρ hρ1 hh plus).val =
      ρ/2 + (if plus then tailModulus (quantileTail μ ρ) h else -tailModulus (quantileTail μ ρ) h)/16 := by
  let ν := quantileTail μ ρ
  let : IsFiniteMeasure ν := isFiniteMeasure_of_le μ (quantileTail_le μ hρ hρ1)
  have he (ξ : Measure Gap) [IsFiniteMeasure ξ] : Integrable (tailEpsilon h) ξ :=
    (tailKernel_integrable ξ hh).div_const 16
  have hmass : ν.real univ = ρ := quantileTail_real_mass μ hρ hρ1
  change (∫ d, cutWeight _ _ d * (1/2 + if plus then tailEpsilon h d else -tailEpsilon h d) ∂μ) = _
  cases plus <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  · rw [integral_cutWeight μ hρ hρ1 (fun d => 1/2 + -tailEpsilon h d) ((integrable_const (1/2 : ℝ)).add (he μ).neg)]
    change (∫ d, 1/2 + -tailEpsilon h d ∂ν) = _
    rw [integral_add (f := fun _ : Gap => (1/2 : ℝ)) (g := fun d : Gap => -tailEpsilon h d) (integrable_const _) (he ν).neg, integral_neg, integral_const]
    simp only [tailEpsilon, integral_div, tailModulus, smul_eq_mul, hmass]
    ring
  · rw [integral_cutWeight μ hρ hρ1 (fun d => 1/2 + tailEpsilon h d) ((integrable_const (1/2 : ℝ)).add (he μ))]
    change (∫ d, 1/2 + tailEpsilon h d ∂ν) = _
    rw [integral_add (integrable_const _) (he ν), integral_const]
    simp only [tailEpsilon, integral_div, tailModulus, smul_eq_mul, hmass]
    ring

theorem tailEndpoint_rare (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ h : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hh : 0 ≤ h) (plus : Bool) :
    RarePrior μ ρ (tailEndpoint μ hρ hρ1 hh plus) := by
  let : IsFiniteMeasure (quantileTail μ ρ) := isFiniteMeasure_of_le μ (quantileTail_le μ hρ hρ1)
  have hm := tailModulus_le_mass (quantileTail μ ρ) hh
  rw [quantileTail_real_mass μ hρ hρ1] at hm
  have hn := tailModulus_nonneg (quantileTail μ ρ) hh
  unfold RarePrior
  rw [tailEndpoint_mean]
  cases plus <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> linarith

end ThresholdHC.FiniteQuantile
