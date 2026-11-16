import ThresholdHC.RobustContinuation.ReferenceBase
import ThresholdHC.RobustContinuation.PilotIndependence
import ThresholdHC.ConfidenceProgram.Amplify

/-! The CDF-robust reference estimator, amplified by the existing physical-cap
median and exposed as a paid learned-law continuation. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace ThresholdHC.RobustContinuation
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.RareAboveTwo
open ThresholdHC.ArbitraryLawAdaptation ThresholdHC.KnownLawPlanner
open ThresholdHC.HardBudget ThresholdHC.ConfidenceProgram ThresholdHC.Confidence
open ThresholdHC.ObservableSimulation ThresholdHC.BlindUpper

def medianBaseBudget (B : ℝ) (m : ℕ) : ℝ := B / (8 * (2 * (m : ℝ) + 1))
def medianCopyCap (B : ℝ) (m : ℕ) : ℕ := ⌊B / (2 * (m : ℝ) + 1)⌋₊
def medianRadius (α : Measure ℝ) (ρ B : ℝ) (m : ℕ) : ℝ :=
  Real.sqrt 8 * referenceRadius α ρ (medianBaseBudget B m)

theorem medianRadius_nonneg (α : Measure ℝ) (ρ B : ℝ) (m : ℕ) :
    0 ≤ medianRadius α ρ B m :=
  mul_nonneg (Real.sqrt_nonneg _) (referenceRadius_nonneg _ _ _)

theorem medianRadius_le (α : Measure ℝ) (ρ B : ℝ) (m : ℕ) :
    medianRadius α ρ B m ≤ 6 * plannedCoefficient 28000 *
      (zeroSelection α ρ (medianBaseBudget B m)).toReal := by
  have hs : Real.sqrt 8 ≤ 6 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8)]
  have h := mul_le_mul_of_nonneg_right hs (referenceRadius_nonneg α ρ (medianBaseBudget B m))
  simpa only [medianRadius, referenceRadius, mul_assoc] using h

theorem reference_median_coverage (α : Measure ℝ) (ρ B : ℝ) (m : ℕ)
    (hv : ValidReference α ρ (medianBaseBudget B m)) (hB : 0 < B)
    (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (hq : RarePrior μ ρ q)
    (hdom : ∀ x, cdf (μ.map Subtype.val) x ≤ cdf α x) :
    PathwiseCap (cappedMedian (referenceBase α ρ (medianBaseBudget B m)) m
      (medianCopyCap B m) ρ) ⌊B⌋₊ ∧
    failureProbability μ (cappedMedian (referenceBase α ρ (medianBaseBudget B m)) m
      (medianCopyCap B m) ρ) q (medianRadius α ρ B m) ≤ ENNReal.ofReal ((3/4:ℝ)^m/2) := by
  obtain ⟨hw, hr⟩ := (referenceBase_valid α ρ (medianBaseBudget B m) hv).2 μ hdom
  exact hard_median_transfer μ _ q m hB ⟨(signMean_bounds μ q).1, hq⟩
    (referenceRadius_nonneg _ _ _) (hw q hq) ((rms_le_rare μ _ ρ q hq).trans hr)

theorem measurable_median_reader {R : Type} [MeasurableSpace R]
    (A : AdaptiveEstimator R) (N k start : ℕ) (w : List Bool) :
    Measurable (fun r => blockReader N (medianReader A r) k start w) := by
  induction k generalizing start w with
  | zero => exact measurable_const
  | succ k ih =>
    by_cases h : w.length < N
    · simp only [blockReader, thenRead, ite_eq_left h, Function.comp_apply, ConfidenceProgram.medianReader]
      exact (measurable_of_countable (fun a : Option ℕ => Nat.pair start (a.getD 0))).comp
        ((measurable_to_countable' (A.policy_measurable w)).comp (measurable_pi_apply start))
    · simpa only [blockReader, thenRead, ite_eq_right_iff.mpr (fun h' => (h h').elim)] using
        ih (start+1) (w.drop N)

def medianWord {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R)
    (m N : ℕ) (M : ℝ) (r : ℕ → R) (w : List Bool) : ℝ :=
  median m (fun i => (stageOutput A M (r i.val) (blockAt N i.val w)).getD (M/2))

theorem measurable_medianWord {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R)
    (m N : ℕ) (M : ℝ) (w : List Bool) : Measurable (fun r => medianWord A m N M r w) := by
  apply measurable_median
  intro i
  exact measurable_stage_getD A M (blockAt N i.val w)
    (fun r : ℕ → R => r i.val) (measurable_pi_apply _) (fun _ => M/2) measurable_const

theorem medianWord_output {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R)
    (m N : ℕ) (M : ℝ) (r : ℕ → R) (s : Table) :
    medianWord A m N M r (readBlock ((2*m+1)*N)
      (blockReader N (medianReader A r) (2*m+1) 0) s).1 =
      (cappedMedian A m N M).output (r, populationPath ((cappedMedian A m N M).policy r) s) := by
  change medianWord A m N M r _ = medianWord A m N M r
    (processHistory (populationPath (stopAt _ _) s) _)
  rw [wordEstimator_history]

abbrev MedianSeed (ρ B : ℝ) (m : ℕ) :=
  ∀ α : Measure ℝ, ℕ → ReferenceSeed α ρ (medianBaseBudget B m)

def medianStage (ρ B : ℝ) (m : ℕ) : LearnedStage (MedianSeed ρ B m) where
  randomLaw := Measure.infinitePi (fun α : Measure ℝ =>
    (cappedMedian (referenceBase α ρ (medianBaseBudget B m)) m (medianCopyCap B m) ρ).randomLaw)
  probability := inferInstance
  pilotCost := 0
  continuationCost := (2*m+1) * medianCopyCap B m
  depth := 0
  pilot := fun _ => 0
  upper := fun _ _ => 1
  upper_nonneg := fun _ _ => zero_le_one
  upper_zero := fun _ => rfl
  continuation α r := blockReader (medianCopyCap B m)
    (medianReader (referenceBase α ρ (medianBaseBudget B m)) (r α)) (2*m+1) 0
  continuation_measurable := by
    intro α w
    have he : Measurable (fun r : MedianSeed ρ B m => r α) := measurable_pi_apply α
    exact (measurable_median_reader (referenceBase α ρ (medianBaseBudget B m))
      (medianCopyCap B m) (2*m+1) 0 w).comp he
  interval α r w :=
    let v := medianWord (referenceBase α ρ (medianBaseBudget B m)) m (medianCopyCap B m) ρ (r α) w
    (v - medianRadius α ρ B m, v + medianRadius α ρ B m)
  interval_measurable := by
    intro α w
    have he : Measurable (fun r : MedianSeed ρ B m => r α) := measurable_pi_apply α
    have h := (measurable_medianWord (referenceBase α ρ (medianBaseBudget B m)) m
      (medianCopyCap B m) ρ w).comp he
    exact (h.sub_const _).prodMk (h.add_const _)

theorem medianStage_radius (ρ B : ℝ) (m : ℕ) (α : Measure ℝ)
    (r : MedianSeed ρ B m) (w : List Bool) :
    ((medianStage ρ B m).interval α r w).2 - ((medianStage ρ B m).interval α r w).1 =
      2 * medianRadius α ρ B m := by
  dsimp only [medianStage]
  ring

end ThresholdHC.RobustContinuation
