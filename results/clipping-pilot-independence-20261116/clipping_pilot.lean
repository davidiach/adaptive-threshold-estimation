
import ThresholdHC.RobustContinuation.Clipping
import ThresholdHC.RobustContinuation.PilotIndependence
noncomputable section
set_option linter.unusedVariables false
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open ThresholdHC.RobustContinuation
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.RareAboveTwo
open ThresholdHC.HardBudget ThresholdHC.ArbitraryLawAdaptation
open ThresholdHC.ObservableSimulation ThresholdHC.KnownLawPlanner
example : ∀ {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (M : ℝ),
    clippedEstimator A M =
      { A with output := fun z => clipEstimate M (A.output z)
               output_measurable := (measurable_clip M).comp A.output_measurable } := by
  intros; rfl
example : ∀ {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (M : ℝ),
    (clippedEstimator A M).policy = A.policy := @clippedEstimator_policy
example : ∀ {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) {M : ℝ}
    (hM : 0 ≤ M) (z : R × ProcessTape),
    0 ≤ (clippedEstimator A M).output z ∧ (clippedEstimator A M).output z ≤ M := @clippedEstimator_output_range
example : ∀ {R : List Bool → Type} [∀ xs, MeasurableSpace (R xs)]
    (P : ∀ xs, Measure (R xs)) [∀ xs, IsProbabilityMeasure (P xs)]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (n : ℕ) (p : Reader) (xs : List Bool)
    (hxs : ((Measure.infinitePi P).prod
      (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)))
      {z | (readBlock n p (z.2 ∘ Nat.pair 0)).1 = xs} ≠ 0),
    ((((Measure.infinitePi P).prod
      (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)))
      {z | (readBlock n p (z.2 ∘ Nat.pair 0)).1 = xs})⁻¹ •
      ((Measure.infinitePi P).prod
        (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q))).restrict
        {z | (readBlock n p (z.2 ∘ Nat.pair 0)).1 = xs}).map
      (fun z => (z.1 xs, z.2 ∘ Nat.pair 1)) =
      (P xs).prod (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)) := @pilot_selected_seed_law
example : ∀ {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (q : SignLaw) (M : ℝ),
    experimentLaw μ (clippedEstimator A M) q = experimentLaw μ A q := @clippedEstimator_experimentLaw
example : ∀ {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (q : SignLaw) (M : ℝ),
    expectedWork μ (clippedEstimator A M) q = expectedWork μ A q := @clippedEstimator_expectedWork
example : ∀ {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (M : ℝ) (n : ℕ),
    PathwiseCap (clippedEstimator A M) n ↔ PathwiseCap A n := @clippedEstimator_pathwiseCap
example : ∀ {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (q : SignLaw) {M θ : ℝ} (hθ : 0 ≤ θ ∧ θ ≤ M),
    squaredRisk (experimentLaw μ (clippedEstimator A M) q)
      (populationOutput (clippedEstimator A M)) θ ≤
      squaredRisk (experimentLaw μ A q) (populationOutput A) θ := @clippedEstimator_squaredRisk_le
example : ∀ {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (M ρ B : ℝ),
    RareBudget μ (clippedEstimator A M) ρ B ↔ RareBudget μ A ρ B := @clippedEstimator_rareBudget
example : ∀ {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (ρ : ℝ),
    rareRisk μ (clippedEstimator A ρ) ρ ≤ rareRisk μ A ρ := @clippedEstimator_rareRisk_le
example : ∀ {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) {ρ B : ℝ} {e : ℝ≥0∞}
    (hB : RareBudget μ A ρ B) (he : rareRisk μ A ρ ≤ e),
    RareBudget μ (clippedEstimator A ρ) ρ B ∧
      rareRisk μ (clippedEstimator A ρ) ρ ≤ e := @clippedEstimator_valid
example : ∀ (η : Measure Gap) [IsProbabilityMeasure η] {z₀ ρ B : ℝ}
    (hz0 : 0 ≤ z₀) (hzρ : z₀ < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B),
    ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R),
      (∀ z, 0 ≤ A.output z ∧ A.output z ≤ ρ) ∧
      ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
        (∀ x, cdf (μ.map Subtype.val) x ≤ cdf (zeroAtomLaw z₀ η) x) →
        RareBudget μ A ρ B ∧ rareRisk μ A ρ ≤
          ENNReal.ofReal (plannedCoefficient 28000) * zeroSelection (zeroAtomLaw z₀ η) ρ B := @clipped_cdf_planner_rate
example : ∀ {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν],
    (Measure.infinitePi (fun _ : ℕ => ν)).map
      (fun ω => ((fun i => ω (Nat.pair 0 i)), (fun i => ω (Nat.pair 1 i)))) =
      (Measure.infinitePi (fun _ : ℕ => ν)).prod
        (Measure.infinitePi (fun _ : ℕ => ν)) := @infinitePi_two_blocks
example : ∀ {R X : Type*} [MeasurableSpace R] [MeasurableSpace X]
    (P : Measure R) (ν : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure ν],
    (P.prod (Measure.infinitePi (fun _ : ℕ => ν))).map
      (fun z => ((fun i => z.2 (Nat.pair 0 i)), (z.1, fun i => z.2 (Nat.pair 1 i)))) =
      (Measure.infinitePi (fun _ : ℕ => ν)).prod
        (P.prod (Measure.infinitePi (fun _ : ℕ => ν))) := @seed_two_blocks
example : ∀ (n : ℕ) (p : Reader),
    Measurable (fun s : Table => (readBlock n p s).1) := @measurable_pilot_word
example : ∀ {R : Type} [MeasurableSpace R] (n : ℕ) (p : R → Reader)
    (hp : ∀ xs, Measurable (fun r => p r xs)),
    Measurable (fun z : R × Table => (readBlock n (p z.1) z.2).1) := @measurable_seeded_word
example : ∀ {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (q : SignLaw) (n : ℕ) (p : Reader),
    (originalSimulationLaw μ A q).map
      (fun z => ((readBlock n p (z.2 ∘ Nat.pair 0)).1, (z.1, z.2 ∘ Nat.pair 1))) =
      ((Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)).map
        (fun s => (readBlock n p s).1)).prod (originalSimulationLaw μ A q) := @pilot_production_joint_law
example : ∀ {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (q : SignLaw) (n : ℕ) (p : Reader) (xs : List Bool),
    ((originalSimulationLaw μ A q).restrict
      {z | (readBlock n p (z.2 ∘ Nat.pair 0)).1 = xs}).map
      (fun z => (z.1, z.2 ∘ Nat.pair 1)) =
      ((Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q))
        {s | (readBlock n p s).1 = xs}) • originalSimulationLaw μ A q := @pilot_restrict_production_law
example : ∀ {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (q : SignLaw) (n : ℕ) (p : Reader) (xs : List Bool),
    (originalSimulationLaw μ A q) {z | (readBlock n p (z.2 ∘ Nat.pair 0)).1 = xs} =
      (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q))
        {s | (readBlock n p s).1 = xs} := @pilot_history_probability
example : ∀ {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (q : SignLaw) (n : ℕ) (p : Reader) (xs : List Bool)
    (hxs : (originalSimulationLaw μ A q)
      {z | (readBlock n p (z.2 ∘ Nat.pair 0)).1 = xs} ≠ 0),
    (((originalSimulationLaw μ A q)
      {z | (readBlock n p (z.2 ∘ Nat.pair 0)).1 = xs})⁻¹ •
      (originalSimulationLaw μ A q).restrict
        {z | (readBlock n p (z.2 ∘ Nat.pair 0)).1 = xs}).map
      (fun z => (z.1, z.2 ∘ Nat.pair 1)) = originalSimulationLaw μ A q := @pilot_conditional_production_law
example : ∀ {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (S : LearnedStage R) (q : SignLaw) (J m : ℕ) (ρ : ℝ),
    (originalSimulationLaw μ ((pilotStage S J m ρ).endpoint false) q).map
      (fun z => (pilotStageWord J m ρ z.2, (z.1, z.2 ∘ Nat.pair 1))) =
      ((Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)).map
        (fun s => (readBlock (pilotCost J m) (pilotReader J m (pilotCoinCap J ρ)) s).1)).prod
      (originalSimulationLaw μ ((pilotStage S J m ρ).endpoint false) q) := @pilotStage_production_joint_law
example : ∀ {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (S : LearnedStage R) (q : SignLaw) (J m : ℕ) (ρ : ℝ) (xs : List Bool)
    (hxs : (originalSimulationLaw μ ((pilotStage S J m ρ).endpoint false) q)
      {z | pilotStageWord J m ρ z.2 = xs} ≠ 0),
    (((originalSimulationLaw μ ((pilotStage S J m ρ).endpoint false) q)
      {z | pilotStageWord J m ρ z.2 = xs})⁻¹ •
      (originalSimulationLaw μ ((pilotStage S J m ρ).endpoint false) q).restrict
        {z | pilotStageWord J m ρ z.2 = xs}).map
      (fun z => (z.1, z.2 ∘ Nat.pair 1)) =
      originalSimulationLaw μ ((pilotStage S J m ρ).endpoint false) q := @pilotStage_conditional_production_law
example : ∀ {R : Type} [MeasurableSpace R] (S : LearnedStage R) (r : R) (s : Table),
    (processHistory (populationPath ((S.endpoint false).policy r) s) S.cap).take S.pilotCost =
      (readBlock S.pilotCost S.pilot (s ∘ Nat.pair 0)).1 := @learnedStage_pilot_history
example : ∀ {R : Type} [MeasurableSpace R] (S : LearnedStage R)
    (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw),
    (experimentLaw μ (S.endpoint false) q).map (fun z =>
      ((processHistory z.2 S.cap).take S.pilotCost,
        ((S.endpoint false).output (z.1.1,z.2), (S.endpoint true).output (z.1.1,z.2)))) =
      (originalSimulationLaw μ (S.endpoint false) q).map (fun z =>
        ((readBlock S.pilotCost S.pilot (z.2 ∘ Nat.pair 0)).1,
          S.tableInterval z.1 z.2)) := @original_pilot_interval_law
example : ∀ {R : Type} [MeasurableSpace R] (S : LearnedStage R) (xs : List Bool),
    Measurable (fun z : R × Table => S.interval (S.learnedLaw xs) z.1
      (readBlock S.continuationCost (S.continuation (S.learnedLaw xs) z.1) z.2).1) := @measurable_selected_interval
example : ∀ {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (S : LearnedStage R) (q : SignLaw) (xs : List Bool)
    (hxs : (originalSimulationLaw μ (S.endpoint false) q)
      {z | (readBlock S.pilotCost S.pilot (z.2 ∘ Nat.pair 0)).1 = xs} ≠ 0),
    (((originalSimulationLaw μ (S.endpoint false) q)
      {z | (readBlock S.pilotCost S.pilot (z.2 ∘ Nat.pair 0)).1 = xs})⁻¹ •
      (originalSimulationLaw μ (S.endpoint false) q).restrict
        {z | (readBlock S.pilotCost S.pilot (z.2 ∘ Nat.pair 0)).1 = xs}).map
      (fun z => S.tableInterval z.1 z.2) =
      (originalSimulationLaw μ (S.endpoint false) q).map
        (fun z => S.interval (S.learnedLaw xs) z.1
          (readBlock S.continuationCost (S.continuation (S.learnedLaw xs) z.1) z.2).1) := @learnedStage_conditional_interval_law
#print axioms ThresholdHC.RobustContinuation.clippedEstimator
#print axioms ThresholdHC.RobustContinuation.clippedEstimator_expectedWork
#print axioms ThresholdHC.RobustContinuation.clippedEstimator_experimentLaw
#print axioms ThresholdHC.RobustContinuation.clippedEstimator_output_range
#print axioms ThresholdHC.RobustContinuation.clippedEstimator_pathwiseCap
#print axioms ThresholdHC.RobustContinuation.clippedEstimator_policy
#print axioms ThresholdHC.RobustContinuation.clippedEstimator_rareBudget
#print axioms ThresholdHC.RobustContinuation.clippedEstimator_rareRisk_le
#print axioms ThresholdHC.RobustContinuation.clippedEstimator_squaredRisk_le
#print axioms ThresholdHC.RobustContinuation.clippedEstimator_valid
#print axioms ThresholdHC.RobustContinuation.clipped_cdf_planner_rate
#print axioms ThresholdHC.RobustContinuation.infinitePi_two_blocks
#print axioms ThresholdHC.RobustContinuation.learnedStage_conditional_interval_law
#print axioms ThresholdHC.RobustContinuation.learnedStage_pilot_history
#print axioms ThresholdHC.RobustContinuation.measurable_pilot_word
#print axioms ThresholdHC.RobustContinuation.measurable_seeded_word
#print axioms ThresholdHC.RobustContinuation.measurable_selected_interval
#print axioms ThresholdHC.RobustContinuation.original_pilot_interval_law
#print axioms ThresholdHC.RobustContinuation.pilotStage_conditional_production_law
#print axioms ThresholdHC.RobustContinuation.pilotStage_production_joint_law
#print axioms ThresholdHC.RobustContinuation.pilot_conditional_production_law
#print axioms ThresholdHC.RobustContinuation.pilot_history_probability
#print axioms ThresholdHC.RobustContinuation.pilot_production_joint_law
#print axioms ThresholdHC.RobustContinuation.pilot_restrict_production_law
#print axioms ThresholdHC.RobustContinuation.pilot_selected_seed_law
#print axioms ThresholdHC.RobustContinuation.seed_two_blocks
