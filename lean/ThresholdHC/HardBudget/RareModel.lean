import ThresholdHC.HardBudget.Specification

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.HardBudget
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo

def hardRareMinimaxRisk (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ B : ℝ) : ℝ≥0∞ :=
  sInf {t | ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R),
    PathwiseCap A ⌊B⌋₊ ∧ t = rareRisk μ A ρ}

theorem rms_le_rare {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (ρ : ℝ) (q : SignLaw) (hq : RarePrior μ ρ q) :
    rootMeanRisk (experimentLaw μ A q) (populationOutput A) (signMean μ q.val) ≤ rareRisk μ A ρ := by
  let V (u : SignLaw) := rootMeanRisk (experimentLaw μ A u) (populationOutput A) (signMean μ u.val)
  exact (le_iSup (fun _ : RarePrior μ ρ q => V q) hq).trans
    (le_iSup (fun u => ⨆ _ : RarePrior μ ρ u, V u) q)

end ThresholdHC.HardBudget
