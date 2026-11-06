import ThresholdHC.ArbitraryLawAdaptation.CDFEnvelope
import ThresholdHC.LawAdaptation.Controller

/-! Observable composition of a paid envelope-learning pilot and a selected
continuation. The pilot and continuation use disjoint persistent coin labels.
No oracle risk or statistical pilot premise is assumed in these execution
lemmas. Instantiating the stage and proving those bounds remain separate. -/

noncomputable section
open MeasureTheory
namespace ThresholdHC.ArbitraryLawAdaptation
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.HardBudget
open ThresholdHC.ObservableSimulation ThresholdHC.LawAdaptation
open ThresholdHC.BlindUpper

structure LearnedStage (R : Type) [MeasurableSpace R] where
  randomLaw : Measure R
  probability : IsProbabilityMeasure randomLaw
  pilotCost : ℕ
  continuationCost : ℕ
  depth : ℕ
  pilot : Reader
  upper : List Bool → ℕ → ℝ
  upper_nonneg : ∀ xs j, 0 ≤ upper xs j
  upper_zero : ∀ xs, upper xs 0 = 1
  continuation : Measure ℝ → R → Reader
  continuation_measurable : ∀ law xs, Measurable (fun r => continuation law r xs)
  interval : Measure ℝ → R → List Bool → ℝ × ℝ
  interval_measurable : ∀ law xs, Measurable (fun r => interval law r xs)

namespace LearnedStage
variable {R : Type} [MeasurableSpace R]

def cap (S : LearnedStage R) : ℕ := S.pilotCost + S.continuationCost

def learnedLaw (S : LearnedStage R) (xs : List Bool) : Measure ℝ :=
  envelopeLaw (prefixMinimum (S.upper xs)) S.depth

theorem learnedLaw_probability (S : LearnedStage R) (xs : List Bool) :
    IsProbabilityMeasure (S.learnedLaw xs) :=
  learnedEnvelope_probability (S.upper_nonneg xs) (S.upper_zero xs) S.depth

theorem learnedLaw_dominates (S : LearnedStage R) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hsupport : μ (Set.Iio 0) = 0) (xs : List Bool)
    (hgrid : ∀ j ≤ S.depth, μ.real (Set.Iic (gridPoint j)) ≤ S.upper xs j) (x : ℝ) :
    μ (Set.Iic x) ≤ S.learnedLaw xs (Set.Iic x) :=
  learnedEnvelope_dominates μ (S.upper_nonneg xs) (S.upper_zero xs) hsupport S.depth hgrid x

def reader (S : LearnedStage R) (r : R) : Reader :=
  thenChoose S.pilotCost (Nat.pair 0 ∘ S.pilot)
    (fun xs => Nat.pair 1 ∘ S.continuation (S.learnedLaw xs) r)

def historyInterval (S : LearnedStage R) (r : R) (xs : List Bool) : ℝ × ℝ :=
  S.interval (S.learnedLaw (xs.take S.pilotCost)) r (xs.drop S.pilotCost)

def tableInterval (S : LearnedStage R) (r : R) (s : Table) : ℝ × ℝ :=
  let v := (readBlock S.pilotCost S.pilot (s ∘ Nat.pair 0)).1
  let law := S.learnedLaw v
  S.interval law r (readBlock S.continuationCost (S.continuation law r) (s ∘ Nat.pair 1)).1

theorem pilot_fresh (S : LearnedStage R) (s : Table) (j : ℕ) :
    (readBlock S.pilotCost (Nat.pair 0 ∘ S.pilot) s).2 (Nat.pair 1 j) = s (Nat.pair 1 j) := by
  apply readBlock_untouched
  intro xs h
  have he := (Nat.pair_eq_pair.mp h).1
  norm_num at he

/-- The selected law and continuation word are both computed from the
chronological observed history; the continuation sees the original fresh tapes. -/
theorem interval_readBlock (S : LearnedStage R) (r : R) (s : Table) :
    S.historyInterval r (readBlock S.cap (S.reader r) s).1 = S.tableInterval r s := by
  let v := readBlock S.pilotCost (Nat.pair 0 ∘ S.pilot) s
  let law := S.learnedLaw v.1
  let q := S.continuation law r
  let u := readBlock S.continuationCost (Nat.pair 1 ∘ q) v.2
  have hword : (readBlock S.cap (S.reader r) s).1 = v.1++u.1 :=
    congrArg Prod.fst (readBlock_thenChoose S.pilotCost S.continuationCost
      (Nat.pair 0 ∘ S.pilot) (fun xs => Nat.pair 1 ∘ S.continuation (S.learnedLaw xs) r) s)
  have hlen : v.1.length = S.pilotCost := readBlock_length _ _ _
  have hp : v.1 = (readBlock S.pilotCost S.pilot (s ∘ Nat.pair 0)).1 :=
    readBlock_relabel _ _ (fun _ _ h => (Nat.pair_eq_pair.mp h).2) _ _
  have hfresh : v.2 ∘ Nat.pair 1 = s ∘ Nat.pair 1 := funext (S.pilot_fresh s)
  have hu := readBlock_relabel S.continuationCost (Nat.pair 1)
    (fun _ _ h => (Nat.pair_eq_pair.mp h).2) q v.2
  rw [hfresh] at hu
  change u.1 = _ at hu
  rw [historyInterval,hword,← hlen,List.take_left,List.drop_left,hu]
  dsimp only [tableInterval,q,law]
  rw [hp]

theorem measurable_reader (S : LearnedStage R) (xs : List Bool) :
    Measurable (fun r => S.reader r xs) := by
  by_cases h : xs.length < S.pilotCost
  · simp only [reader,thenChoose,ite_eq_left h]
    exact measurable_const
  · simp only [reader,thenChoose,ite_eq_right h,Function.comp_apply]
    exact (measurable_of_countable (Nat.pair 1)).comp (S.continuation_measurable _ _)

theorem measurable_historyInterval (S : LearnedStage R) (xs : List Bool) :
    Measurable (fun r => S.historyInterval r xs) := S.interval_measurable _ _

def endpoint (S : LearnedStage R) (upper : Bool) : AdaptiveEstimator R where
  randomLaw := S.randomLaw
  probability := S.probability
  policy r := stopAt S.cap (S.reader r)
  policy_measurable := by
    intro xs a
    by_cases h : xs.length < S.cap
    · simp only [stopAt,ite_eq_left h]
      exact measurableSet_eq_fun ((measurable_of_countable some).comp
        (S.measurable_reader xs)) measurable_const
    · simp [stopAt,h]
  output z :=
    let I := S.historyInterval z.1 (processHistory z.2 S.cap)
    if upper then I.2 else I.1
  output_measurable := by
    have hm : Measurable (fun z : R × List Bool => S.historyInterval z.1 z.2) :=
      measurable_from_prod_countable_left S.measurable_historyInterval
    have ht := hm.comp (measurable_fst.prodMk
      ((measurable_processHistory_fixed S.cap).comp measurable_snd))
    cases upper
    · exact ht.fst
    · exact ht.snd

theorem endpoint_cap (S : LearnedStage R) (upper : Bool) : PathwiseCap (S.endpoint upper) S.cap :=
  stopAt_pathwise_cap _ _ _ (fun _ => rfl)

theorem endpoint_policy_eq (S : LearnedStage R) :
    (S.endpoint true).policy = (S.endpoint false).policy := rfl

theorem endpoint_output (S : LearnedStage R) (upper : Bool) (r : R) (s : Table) :
    (S.endpoint upper).output (r,populationPath ((S.endpoint upper).policy r) s) =
      if upper then (S.tableInterval r s).2 else (S.tableInterval r s).1 := by
  let w := (readBlock S.cap (S.reader r) s).1
  have hp := block_path S.cap (S.reader r) s
  change populationPath ((S.endpoint upper).policy r) s = fun i => w[i]? at hp
  change (if upper then (S.historyInterval r (processHistory _ S.cap)).2
    else (S.historyInterval r (processHistory _ S.cap)).1) = _
  rw [hp,← show w.length = S.cap from readBlock_length _ _ _,processHistory_word,
    S.interval_readBlock r s]

/-- Joint law of both endpoints in the original hidden-gap experiment. -/
theorem original_interval_law (S : LearnedStage R) (μ : Measure Gap)
    [IsProbabilityMeasure μ] (q : SignLaw) :
    (experimentLaw μ (S.endpoint false) q).map
      (fun z => ((S.endpoint false).output (z.1.1,z.2), (S.endpoint true).output (z.1.1,z.2))) =
      (originalSimulationLaw μ (S.endpoint false) q).map
        (fun z => S.tableInterval z.1 z.2) := by
  let A := S.endpoint false
  let U := S.endpoint true
  let F (z : R × ProcessTape) := (A.output z,U.output z)
  have hF : Measurable F := A.output_measurable.prodMk U.output_measurable
  have hg : Measurable (fun z : PopulationSeed R × ProcessTape => (z.1.1,z.2)) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hp : Measurable (fun z : R × Table => (z.1,populationPath (A.policy z.1) z.2)) :=
    measurable_fst.prodMk (measurable_seeded_populationPath A.policy
      (fun xs => measurable_to_countable' (A.policy_measurable xs)))
  change (experimentLaw μ A q).map (F ∘ fun z => (z.1.1,z.2)) = _
  rw [← Measure.map_map hF hg,original_observable_simulation_law,Measure.map_map hF hp]
  apply congrArg (fun f => (originalSimulationLaw μ A q).map f)
  funext z
  change ((S.endpoint false).output (z.1,populationPath ((S.endpoint false).policy z.1) z.2),
    (S.endpoint true).output (z.1,populationPath ((S.endpoint true).policy z.1) z.2)) = _
  rw [S.endpoint_output,S.endpoint_output]
  rfl

end LearnedStage
end ThresholdHC.ArbitraryLawAdaptation
