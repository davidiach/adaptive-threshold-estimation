import ThresholdHC.LatentThreshold.Threshold

/-! The threshold form of the target for every gap law. -/
noncomputable section
namespace ThresholdHC.LatentThreshold

theorem threshold_mean : ThresholdMeanStatement := by
  intro μ _ q
  exact threshold_mean_eq μ q

end ThresholdHC.LatentThreshold
