import ThresholdHC.LatentDisintegration.Disintegration
import ThresholdHC.LatentThreshold.Threshold

/-! The population class and the `G`-form of the target. -/
noncomputable section
open MeasureTheory
namespace ThresholdHC.LatentDisintegration
open ThresholdHC.Tier6 ThresholdHC.SmoothDensity

theorem latent_magnitude : LatentMagnitudeStatement := by
  intro μ _ q
  exact latent_magnitude_eq μ q

theorem latent_disintegration : DisintegrationStatement := by
  intro G _ hG
  exact exists_latentLaw_eq G hG

theorem population_class : PopulationClassStatement := by
  intro μ _ G
  constructor
  · rintro ⟨q, rfl⟩
    exact latent_magnitude_eq μ q
  · exact exists_latentLaw_of_magnitude μ G

theorem g_form_target : GFormTargetStatement := by
  intro μ _ G h
  refine ⟨exists_latentLaw_of_magnitude μ G h, ?_⟩
  rintro q rfl
  exact LatentThreshold.threshold_mean_eq μ q

end ThresholdHC.LatentDisintegration
