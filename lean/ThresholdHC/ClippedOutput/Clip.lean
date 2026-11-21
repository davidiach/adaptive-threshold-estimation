import ThresholdHC.ClippedOutput.Specification
import ThresholdHC.HardBudget.StageMoments
import ThresholdHC.Tier6.AlgorithmNonempty

/-! The estimator with its output clipped to `[0,1]`.

`unitClip A` replaces the output of `A` by `clipEstimate 1` of it, that is
`max 0 (min 1 ·)`, and keeps every other field. The seed law, the policy and so
the experiment and the expected work are unchanged by definition. Since the
target `signMean μ q.val` lies in `[0,1]`, clipping cannot increase the squared
error at any outcome (`HardBudget.clip_loss_le`), and the clipped squared error
is at most `1` at every outcome. This mirrors the rfl lemmas of
`RobustContinuation.clippedEstimator` with `M = 1` without importing that
group. -/
noncomputable section
namespace ThresholdHC.ClippedOutput
open MeasureTheory ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.HardBudget
open scoped ENNReal

/-- The estimator `A` with its output clipped to `[0,1]`. -/
def unitClip {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) : AdaptiveEstimator R :=
  { A with output := fun z => clipEstimate 1 (A.output z)
           output_measurable := (measurable_clip 1).comp A.output_measurable }

theorem unitClip_randomLaw {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) :
    (unitClip A).randomLaw = A.randomLaw := rfl

theorem unitClip_policy {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) :
    (unitClip A).policy = A.policy := rfl

theorem unitClip_output {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R)
    (z : R × ProcessTape) : (unitClip A).output z = max 0 (min 1 (A.output z)) := rfl

theorem unitClip_output_range {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R)
    (z : R × ProcessTape) : 0 ≤ (unitClip A).output z ∧ (unitClip A).output z ≤ 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

theorem unitClip_experimentLaw {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (q : SignLaw) :
    experimentLaw μ (unitClip A) q = experimentLaw μ A q := rfl

theorem unitClip_expectedWork {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (q : SignLaw) :
    expectedWork μ (unitClip A) q = expectedWork μ A q := rfl

theorem unitClip_uniformBudget {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (B : ℝ) :
    UniformBudget μ (unitClip A) B ↔ UniformBudget μ A B := Iff.rfl

theorem unitClip_squaredRisk_le {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (q : SignLaw) :
    squaredRisk (experimentLaw μ (unitClip A) q) (populationOutput (unitClip A))
        (signMean μ q.val) ≤
      squaredRisk (experimentLaw μ A q) (populationOutput A) (signMean μ q.val) :=
  lintegral_mono fun z => clip_loss_le 1 _ (A.output (z.1.1, z.2)) (signMean_bounds μ q)

theorem unitClip_squaredRisk_le_one {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (q : SignLaw) :
    squaredRisk (experimentLaw μ (unitClip A) q) (populationOutput (unitClip A))
      (signMean μ q.val) ≤ 1 := by
  obtain ⟨hθ0, hθ1⟩ := signMean_bounds μ q
  calc
    squaredRisk (experimentLaw μ (unitClip A) q) (populationOutput (unitClip A))
        (signMean μ q.val) ≤ ∫⁻ _, (1 : ℝ≥0∞) ∂experimentLaw μ (unitClip A) q := by
      apply lintegral_mono
      intro z
      obtain ⟨h0, h1⟩ := unitClip_output_range A (z.1.1, z.2)
      rw [← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      change ((unitClip A).output (z.1.1, z.2) - signMean μ q.val) ^ 2 ≤ 1
      nlinarith
    _ = 1 := by simp

theorem unitClip_rootMeanRisk_le {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (q : SignLaw) :
    rootMeanRisk (experimentLaw μ (unitClip A) q) (populationOutput (unitClip A))
        (signMean μ q.val) ≤
      rootMeanRisk (experimentLaw μ A q) (populationOutput A) (signMean μ q.val) :=
  ENNReal.rpow_le_rpow (unitClip_squaredRisk_le μ A q) (by norm_num)

theorem unitClip_rootMeanRisk_le_one {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (q : SignLaw) :
    rootMeanRisk (experimentLaw μ (unitClip A) q) (populationOutput (unitClip A))
      (signMean μ q.val) ≤ 1 :=
  ENNReal.rpow_le_one (unitClip_squaredRisk_le_one μ A q) (by norm_num)

/-- Clipping does not increase the maximal RMS risk and bounds it by `1`. -/
theorem unitClip_maximalRMSRisk_le {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) :
    maximalRMSRisk μ (unitClip A) ≤ min 1 (maximalRMSRisk μ A) :=
  le_min (iSup_le fun q => unitClip_rootMeanRisk_le_one μ A q)
    (iSup_mono fun q => unitClip_rootMeanRisk_le μ A q)

end ThresholdHC.ClippedOutput
