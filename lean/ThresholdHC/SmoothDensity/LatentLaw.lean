import ThresholdHC.SmoothDensity.Representation
import ThresholdHC.ObservableSimulation.OriginalExperiment

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThresholdHC.SmoothDensity
open ThresholdHC.Tier6 ThresholdHC.CriticalEntropy ThresholdHC.ObservableSimulation

/-- The existing independent Bernoulli-tape construction uses this parameter law. -/
def latentLaw (μ : Measure Gap) (q : SignLaw) : Measure unitInterval :=
  populationParameterLaw μ (gapParameter false) (gapParameter true) (signUnit q)

theorem represents_latent_integral (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (f : ℝ → ℝ) (h : Represents μ q f)
    (F : ℝ → ℝ) (hF : Measurable F) (C : ℝ) (hb : ∀ p, |F p| ≤ C) :
    (∫ p, F (p : ℝ) ∂latentLaw μ q) = ∫ p, f p * F p := by
  rw [latentLaw,populationParameterLaw_integral μ _ _ _
    (measurable_gapParameter false) (measurable_gapParameter true) (measurable_signUnit q)
    (fun p => F (p : ℝ)) (hF.comp measurable_subtype_coe) C (fun p => hb p)]
  simpa only [gapParameter,signUnit,Bool.false_eq_true,ite_false,ite_true,
    sub_eq_add_neg] using h F hF ⟨C,hb⟩

theorem represents_threshold_mean (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (f : ℝ → ℝ) (h : Represents μ q f) :
    signMean μ q.val = ∫ p in Ioi (1 / 2 : ℝ), f p := by
  let F := (Ioi (1 / 2 : ℝ)).indicator (fun _ => (1 : ℝ))
  have hm : Measurable F := measurable_const.indicator measurableSet_Ioi
  have hb (p : ℝ) : |F p| ≤ 1 := by
    dsimp [F,Set.indicator]
    split <;> norm_num
  have he := h F hm ⟨1,hb⟩
  have hpair (d : Gap) : q.val d * F (1 / 2 + (d : ℝ)) +
      (1 - q.val d) * F (1 / 2 - (d : ℝ)) = q.val d := by
    have hp : (1 / 2 : ℝ) + d ∈ Ioi (1 / 2 : ℝ) := by
      change (1 / 2 : ℝ) < 1 / 2 + d
      linarith [d.property.1]
    have hn : (1 / 2 : ℝ) - d ∉ Ioi (1 / 2 : ℝ) := by
      change ¬ (1 / 2 : ℝ) < 1 / 2 - d
      linarith [d.property.1]
    dsimp only [F]
    rw [Set.indicator_of_mem hp,Set.indicator_of_notMem hn]
    ring
  simp_rw [hpair] at he
  have heF : (fun p => f p * F p) = (Ioi (1 / 2 : ℝ)).indicator f := by
    funext p
    dsimp only [F]
    by_cases hp : p ∈ Ioi (1 / 2 : ℝ)
    · simp only [Set.indicator_of_mem hp,mul_one]
    · simp only [Set.indicator_of_notMem hp,mul_zero]
  rw [heF,integral_indicator measurableSet_Ioi] at he
  exact he

end ThresholdHC.SmoothDensity
