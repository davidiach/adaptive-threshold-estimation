import ThresholdHC.Envelope.Moments
import ThresholdHC.BlindUpper.Full
import ThresholdHC.Confidence.Full
import ThresholdHC.OracleLower.Confidence
import ThresholdHC.Tier6.Full

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.Envelope
open ThresholdHC.Tier6 ThresholdHC.Confidence ThresholdHC.BlindUpper ThresholdHC.OracleLower

/-- A single original estimator must obey the work and risk bounds under
every probability law in the reference envelope. -/
def minimaxRMS (μ : Measure Gap) (B : ℝ) : ℝ≥0∞ :=
  sInf {t | ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R),
    ∀ (ν : Measure Gap) [IsProbabilityMeasure ν], Within μ ν →
      UniformBudget ν A B ∧ maximalRMSRisk ν A ≤ t}

def minimaxRadius (μ : Measure Gap) (B δ : ℝ) : ℝ≥0∞ :=
  sInf {t | ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R) (r : ℝ),
    0 ≤ r ∧ (∀ (ν : Measure Gap) [IsProbabilityMeasure ν], Within μ ν →
      UniformBudget ν A B ∧ UniformConfidence ν A r δ) ∧ t = ENNReal.ofReal r}

theorem blind_rms_upper (B : ℝ) (hb : 1 ≤ B) (μ ν : Measure Gap)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (h : Within μ ν) :
    UniformBudget ν (budgetEstimator B) B ∧
      maximalRMSRisk ν (budgetEstimator B) ≤ ENNReal.ofReal (512*modulus μ (1/Real.sqrt B)) := by
  have hp : 0 < B := by linarith
  exact ⟨budgetEstimator_uniformBudget B ν,(budgetEstimator_maximalRMSRisk B hb ν).trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (modulus_le μ ν h (by positivity)) (by norm_num)))⟩

theorem rms_bounds (μ : Measure Gap) [IsProbabilityMeasure μ] {B : ℝ} (hb : 1 ≤ B) :
    ENNReal.ofReal (modulus μ (1/Real.sqrt B)/64) ≤ minimaxRMS μ B ∧
      minimaxRMS μ B ≤ ENNReal.ofReal (512*modulus μ (1/Real.sqrt B)) := by
  constructor
  · apply le_sInf
    rintro t ⟨R,mR,A,hA⟩
    obtain ⟨hw,hr⟩ := hA μ (within_self μ)
    exact (adaptive_algorithm_lower_bound R μ A B hb hw).trans hr
  · exact sInf_le ⟨_,inferInstance,budgetEstimator B,fun ν _ h => blind_rms_upper B hb μ ν h⟩

/-- The same family works for every reference envelope and every actual law. -/
theorem blind_confidence_upper :
    ∃ (R : Type) (_ : MeasurableSpace R) (rule : ℝ → ℝ → AdaptiveEstimator R),
      ∀ (B δ : ℝ), 1 ≤ B → 0 < δ → δ ≤ 1/4 →
      ∀ (μ ν : Measure Gap) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν], Within μ ν →
        UniformBudget ν (rule B δ) B ∧ UniformConfidence ν (rule B δ) (8192*modulus μ (confidenceScale B δ)) δ := by
  obtain ⟨R,mR,rule,h⟩ := confidence_upper
  refine ⟨R,mR,rule,?_⟩
  intro B δ hb hd hd' μ ν _ _ he
  obtain ⟨hw,hc⟩ := h B δ hb hd hd' ν
  refine ⟨hw,fun q => (failureProbability_mono ν _ q ?_).trans (hc q)⟩
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact modulus_le μ ν he (confidenceScale_pos (by linarith) hd hd')

/-- A blind rule embeds in the magnitude oracle by ignoring the revealed
gaps. Its full experiment, physical work and observable output coincide. -/
private theorem original_confidence_lower {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    {B δ r : ℝ} (hb : 1 ≤ B) (hd : 0 < δ) (hd' : δ ≤ 1/4) (hr : 0 ≤ r)
    (hw : UniformBudget μ A B) (hc : UniformConfidence μ A r δ) :
    (15/(256*Real.sqrt 2))*modulus μ (confidenceScale B δ) ≤ r := by
  let O : OracleEstimator (PopulationSeed R) :=
    { randomLaw := populationSeedLaw μ A, probability := inferInstance
      policy := populationPolicy A, policy_measurable := measurable_populationPolicy A
      gap := fun z i => z.2 i, gap_measurable := fun i => (measurable_pi_apply i).comp measurable_snd
      output := populationOutput A, output_measurable := measurable_populationOutput A }
  exact oracle_confidence_lower (PopulationSeed R) μ O B δ r hb hd hd' hr hw hc

theorem confidence_bounds (μ : Measure Gap) [IsProbabilityMeasure μ] {B δ : ℝ}
    (hb : 1 ≤ B) (hd : 0 < δ) (hd' : δ ≤ 1/4) :
    ENNReal.ofReal ((15/(256*Real.sqrt 2))*modulus μ (confidenceScale B δ)) ≤ minimaxRadius μ B δ ∧
      minimaxRadius μ B δ ≤ ENNReal.ofReal (8192*modulus μ (confidenceScale B δ)) := by
  constructor
  · apply le_sInf
    rintro t ⟨R,mR,A,r,hr,hA,rfl⟩
    obtain ⟨hw,hc⟩ := hA μ (within_self μ)
    exact ENNReal.ofReal_le_ofReal (original_confidence_lower μ A hb hd hd' hr hw hc)
  · obtain ⟨R,mR,rule,h⟩ := blind_confidence_upper
    exact sInf_le ⟨R,mR,rule B δ,_,mul_nonneg (by norm_num)
      (modulus_nonneg μ (Real.sqrt_nonneg _)),fun ν _ he => h B δ hb hd hd' μ ν he,rfl⟩

end ThresholdHC.Envelope
