import ThresholdHC.RareAboveTwo.Specification
import ThresholdHC.Tier6.Full

/-! Nonempty budget classes and the saturated half-rarity guarantee in the
canonical observable experiment. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.RareAboveTwo
open ThresholdHC.Tier6

def constantEstimator (t : ℝ) : AdaptiveEstimator Unit :=
  { immediateEstimator with output := fun _ => t, output_measurable := measurable_const }

theorem constant_experiment (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (t : ℝ) :
    experimentLaw μ (constantEstimator t) q = experimentLaw μ immediateEstimator q := rfl

theorem constant_work (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (t : ℝ) : expectedWork μ (constantEstimator t) q = 0 :=
  immediate_expectedWork_zero population_realization μ q

theorem constant_risk (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (t : ℝ) :
    rootMeanRisk (experimentLaw μ (constantEstimator t) q)
      (populationOutput (constantEstimator t)) (signMean μ q.val) =
      ENNReal.ofReal |t-signMean μ q.val| := by
  have he : squaredRisk (experimentLaw μ (constantEstimator t) q)
      (populationOutput (constantEstimator t)) (signMean μ q.val) =
      ENNReal.ofReal ((t-signMean μ q.val)^2) := by
    simp [squaredRisk,populationOutput,constantEstimator]
  unfold rootMeanRisk
  rw [he,← sq_abs (t-signMean μ q.val),ENNReal.ofReal_pow (abs_nonneg _)]
  simpa only [Nat.cast_ofNat,one_div] using
    ENNReal.pow_rpow_inv_natCast (n := 2) (by norm_num)
      (ENNReal.ofReal |t-signMean μ q.val|)

theorem constant_rare_budget (μ : Measure Gap) [IsProbabilityMeasure μ]
    (ρ B t : ℝ) : RareBudget μ (constantEstimator t) ρ B := by
  intro q _
  rw [constant_work]
  exact bot_le

theorem half_rarity_risk (μ : Measure Gap) [IsProbabilityMeasure μ]
    (ρ : ℝ) (_hρ : 0 ≤ ρ) :
    rareRisk μ (constantEstimator (ρ/2)) ρ ≤ ENNReal.ofReal (ρ/2) := by
  apply iSup_le
  intro q
  apply iSup_le
  intro hq
  rw [constant_risk]
  apply ENNReal.ofReal_le_ofReal
  apply abs_le.mpr
  have hmean := (signMean_bounds μ q).1
  change signMean μ q.val ≤ ρ at hq
  constructor <;> linarith

theorem rare_nonvacuity : RareNonvacuityStatement := by
  intro μ _ ρ B hρ _
  have hb := constant_rare_budget μ ρ B (ρ/2)
  have hr := half_rarity_risk μ ρ hρ
  refine ⟨⟨constantEstimator (ρ/2),hb,hr⟩,?_⟩
  apply le_trans _ hr
  apply sInf_le
  exact ⟨Unit,inferInstance,constantEstimator (ρ/2),hb,rfl⟩

end ThresholdHC.RareAboveTwo
