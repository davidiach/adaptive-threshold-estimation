import ThresholdHC.RobustContinuation.CDFBridge
import ThresholdHC.HardBudget.StageMoments

/-! Clipping the observable estimator preserves its experiment and work and
cannot increase error when the target is in the clipping interval. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace ThresholdHC.RobustContinuation
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.RareAboveTwo
open ThresholdHC.HardBudget ThresholdHC.ArbitraryLawAdaptation
open ThresholdHC.KnownLawPlanner

def clippedEstimator {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R)
    (M : ℝ) : AdaptiveEstimator R :=
  { A with output := fun z => clipEstimate M (A.output z)
           output_measurable := (measurable_clip M).comp A.output_measurable }

theorem clippedEstimator_policy {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R)
    (M : ℝ) : (clippedEstimator A M).policy = A.policy := rfl

theorem clippedEstimator_output_range {R : Type} [MeasurableSpace R]
    (A : AdaptiveEstimator R) {M : ℝ} (hM : 0 ≤ M) (z : R × ProcessTape) :
    0 ≤ (clippedEstimator A M).output z ∧ (clippedEstimator A M).output z ≤ M :=
  ⟨le_max_left _ _, max_le hM (min_le_left _ _)⟩

theorem clippedEstimator_experimentLaw {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    (q : SignLaw) (M : ℝ) : experimentLaw μ (clippedEstimator A M) q = experimentLaw μ A q := rfl

theorem clippedEstimator_expectedWork {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    (q : SignLaw) (M : ℝ) : expectedWork μ (clippedEstimator A M) q = expectedWork μ A q := rfl

theorem clippedEstimator_pathwiseCap {R : Type} [MeasurableSpace R]
    (A : AdaptiveEstimator R) (M : ℝ) (n : ℕ) :
    PathwiseCap (clippedEstimator A M) n ↔ PathwiseCap A n := Iff.rfl

theorem clippedEstimator_squaredRisk_le {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    (q : SignLaw) {M θ : ℝ} (hθ : 0 ≤ θ ∧ θ ≤ M) :
    squaredRisk (experimentLaw μ (clippedEstimator A M) q)
      (populationOutput (clippedEstimator A M)) θ ≤
      squaredRisk (experimentLaw μ A q) (populationOutput A) θ := by
  exact lintegral_mono fun z => clip_loss_le M θ (A.output (z.1.1,z.2)) hθ

theorem clippedEstimator_rareBudget {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (M ρ B : ℝ) :
    RareBudget μ (clippedEstimator A M) ρ B ↔ RareBudget μ A ρ B := Iff.rfl

theorem clippedEstimator_rareRisk_le {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (ρ : ℝ) :
    rareRisk μ (clippedEstimator A ρ) ρ ≤ rareRisk μ A ρ := by
  apply iSup₂_le
  intro q hq
  apply le_iSup_of_le q
  apply le_iSup_of_le hq
  apply ENNReal.rpow_le_rpow _ (by norm_num : (0:ℝ) ≤ 1/2)
  exact clippedEstimator_squaredRisk_le μ A q
    ⟨integral_nonneg (fun d => (q.property.2 d).1), hq⟩

/-- A named plan keeps any certified budget and risk after clipping. -/
theorem clippedEstimator_valid {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) {ρ B : ℝ}
    {e : ℝ≥0∞} (hB : RareBudget μ A ρ B) (he : rareRisk μ A ρ ≤ e) :
    RareBudget μ (clippedEstimator A ρ) ρ B ∧ rareRisk μ (clippedEstimator A ρ) ρ ≤ e :=
  ⟨hB, (clippedEstimator_rareRisk_le μ A ρ).trans he⟩

/-- A bounded-output estimator fixed before the true law keeps the CDF
planner's expected budget and rate. -/
theorem clipped_cdf_planner_rate (η : Measure Gap) [IsProbabilityMeasure η] {z₀ ρ B : ℝ}
    (hz0 : 0 ≤ z₀) (hzρ : z₀ < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) :
    ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R),
      (∀ z, 0 ≤ A.output z ∧ A.output z ≤ ρ) ∧
      ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
        (∀ x, cdf (μ.map Subtype.val) x ≤ cdf (zeroAtomLaw z₀ η) x) →
        RareBudget μ A ρ B ∧ rareRisk μ A ρ ≤
          ENNReal.ofReal (plannedCoefficient 28000) * zeroSelection (zeroAtomLaw z₀ η) ρ B := by
  obtain ⟨R, mR, A, hA⟩ := cdf_robust_planner_rate η hz0 hzρ hρ4 hB
  refine ⟨R, mR, clippedEstimator A ρ,
    clippedEstimator_output_range A (hz0.trans hzρ.le), ?_⟩
  intro μ hμ hdom
  exact clippedEstimator_valid μ A (hA μ hdom).1 (hA μ hdom).2

end ThresholdHC.RobustContinuation
