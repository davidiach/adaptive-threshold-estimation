
import ThresholdHC.ArbitraryLawAdaptation.LearnedStage
noncomputable section
set_option linter.unusedVariables false
open MeasureTheory
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.HardBudget
open ThresholdHC.ObservableSimulation ThresholdHC.ArbitraryLawAdaptation
open ThresholdHC.LawAdaptation
variable {R : Type} [MeasurableSpace R]

example : ∀ S : LearnedStage R, S.cap = S.pilotCost + S.continuationCost := fun _ => rfl
example : ∀ (S : LearnedStage R) (xs : List Bool),
    S.learnedLaw xs = envelopeLaw (prefixMinimum (S.upper xs)) S.depth := fun _ _ => rfl
example : ∀ (S : LearnedStage R) (xs : List Bool), IsProbabilityMeasure (S.learnedLaw xs) :=
  @LearnedStage.learnedLaw_probability R _
example : ∀ (S : LearnedStage R) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hsupport : μ (Set.Iio 0) = 0) (xs : List Bool)
    (hgrid : ∀ j ≤ S.depth, μ.real (Set.Iic (gridPoint j)) ≤ S.upper xs j) (x : ℝ),
    μ (Set.Iic x) ≤ S.learnedLaw xs (Set.Iic x) := @LearnedStage.learnedLaw_dominates R _
example : ∀ (S : LearnedStage R) (r : R), S.reader r =
    thenChoose S.pilotCost (Nat.pair 0 ∘ S.pilot)
      (fun xs => Nat.pair 1 ∘ S.continuation (S.learnedLaw xs) r) := fun _ _ => rfl
example : ∀ (S : LearnedStage R) (r : R) (xs : List Bool),
    S.historyInterval r xs = S.interval (S.learnedLaw (xs.take S.pilotCost)) r
      (xs.drop S.pilotCost) := fun _ _ _ => rfl
example : ∀ (S : LearnedStage R) (r : R) (s : Table), S.tableInterval r s =
    let v := (readBlock S.pilotCost S.pilot (s ∘ Nat.pair 0)).1
    let law := S.learnedLaw v
    S.interval law r (readBlock S.continuationCost (S.continuation law r)
      (s ∘ Nat.pair 1)).1 := fun _ _ _ => rfl
example : ∀ (S : LearnedStage R) (s : Table) (j : ℕ),
    (readBlock S.pilotCost (Nat.pair 0 ∘ S.pilot) s).2 (Nat.pair 1 j) = s (Nat.pair 1 j) :=
  @LearnedStage.pilot_fresh R _
example : ∀ (S : LearnedStage R) (r : R) (s : Table),
    S.historyInterval r (readBlock S.cap (S.reader r) s).1 = S.tableInterval r s :=
  @LearnedStage.interval_readBlock R _
example : ∀ (S : LearnedStage R) (xs : List Bool), Measurable (fun r => S.reader r xs) :=
  @LearnedStage.measurable_reader R _
example : ∀ (S : LearnedStage R) (xs : List Bool), Measurable (fun r => S.historyInterval r xs) :=
  @LearnedStage.measurable_historyInterval R _
example : ∀ (S : LearnedStage R) (upper : Bool),
    (S.endpoint upper).policy = fun r => stopAt S.cap (S.reader r) := fun _ _ => rfl
example : ∀ (S : LearnedStage R) (upper : Bool),
    (S.endpoint upper).output = fun z =>
      let I := S.historyInterval z.1 (processHistory z.2 S.cap)
      if upper then I.2 else I.1 := fun _ _ => rfl
example : ∀ (S : LearnedStage R) (upper : Bool), PathwiseCap (S.endpoint upper) S.cap :=
  @LearnedStage.endpoint_cap R _
example : ∀ S : LearnedStage R, (S.endpoint true).policy = (S.endpoint false).policy :=
  @LearnedStage.endpoint_policy_eq R _
example : ∀ (S : LearnedStage R) (upper : Bool) (r : R) (s : Table),
    (S.endpoint upper).output (r,populationPath ((S.endpoint upper).policy r) s) =
      if upper then (S.tableInterval r s).2 else (S.tableInterval r s).1 :=
  @LearnedStage.endpoint_output R _
example : ∀ (S : LearnedStage R) (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw),
    (experimentLaw μ (S.endpoint false) q).map
      (fun z => ((S.endpoint false).output (z.1.1,z.2), (S.endpoint true).output (z.1.1,z.2))) =
      (originalSimulationLaw μ (S.endpoint false) q).map
        (fun z => S.tableInterval z.1 z.2) := @LearnedStage.original_interval_law R _
#print axioms ThresholdHC.ArbitraryLawAdaptation.LearnedStage.cap
#print axioms ThresholdHC.ArbitraryLawAdaptation.LearnedStage.endpoint
#print axioms ThresholdHC.ArbitraryLawAdaptation.LearnedStage.endpoint_cap
#print axioms ThresholdHC.ArbitraryLawAdaptation.LearnedStage.endpoint_output
#print axioms ThresholdHC.ArbitraryLawAdaptation.LearnedStage.endpoint_policy_eq
#print axioms ThresholdHC.ArbitraryLawAdaptation.LearnedStage.historyInterval
#print axioms ThresholdHC.ArbitraryLawAdaptation.LearnedStage.interval_readBlock
#print axioms ThresholdHC.ArbitraryLawAdaptation.LearnedStage.learnedLaw
#print axioms ThresholdHC.ArbitraryLawAdaptation.LearnedStage.learnedLaw_dominates
#print axioms ThresholdHC.ArbitraryLawAdaptation.LearnedStage.learnedLaw_probability
#print axioms ThresholdHC.ArbitraryLawAdaptation.LearnedStage.measurable_historyInterval
#print axioms ThresholdHC.ArbitraryLawAdaptation.LearnedStage.measurable_reader
#print axioms ThresholdHC.ArbitraryLawAdaptation.LearnedStage.original_interval_law
#print axioms ThresholdHC.ArbitraryLawAdaptation.LearnedStage.pilot_fresh
#print axioms ThresholdHC.ArbitraryLawAdaptation.LearnedStage.reader
#print axioms ThresholdHC.ArbitraryLawAdaptation.LearnedStage.tableInterval
