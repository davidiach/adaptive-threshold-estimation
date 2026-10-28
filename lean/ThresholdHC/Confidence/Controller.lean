import ThresholdHC.Confidence.Median
import ThresholdHC.BlindUpper.TerminalOutput

/-!
Sequential independent repetitions of the existing finite-cutoff estimator.
The controller retains only the individual observable machine states. Coin
labels are pair-numbered by repetition and local label, so repetitions use
disjoint coins. The seed contains independent copies of the old seed only.
-/

noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory ProbabilityTheory
namespace ThresholdHC.Confidence
open ThresholdHC.Tier2 ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.Tier6
open ThresholdHC.CriticalEntropy ThresholdHC.BlindUpper

abbrev RepeatSeed := ℕ → BatchSeed
abbrev RepeatState (m : ℕ) := MedianIndex m → BatchMachineState

def repeatSeedLaw : Measure RepeatSeed := Measure.infinitePi (fun _ : ℕ => batchSeedLaw)

instance repeatSeedLaw_probability : IsProbabilityMeasure repeatSeedLaw := by
  unfold repeatSeedLaw
  infer_instance

def activeSet {m : ℕ} (s : RepeatState m) : Finset (MedianIndex m) :=
  Finset.univ.filter (fun i => (controlLabel (s i).1).isSome)

def selectActive {m : ℕ} (s : RepeatState m) : Option (MedianIndex m) :=
  if h : (activeSet s).Nonempty then some ((activeSet s).min' h) else none

def repeatLabel {m : ℕ} (s : RepeatState m) : Option ℕ :=
  (selectActive s).bind (fun i => (controlLabel (s i).1).map (Nat.pair i.val))

def repeatInitial (m : ℕ) : RepeatState m := fun _ => batchInitial

def repeatStep (m L : ℕ) (r : RepeatSeed) (s : RepeatState m) (b : Bool) : RepeatState m :=
  match selectActive s with
  | none => s
  | some i => Function.update s i (batchStep L (r i.val) (s i) b)

theorem measurable_repeatStep (m L : ℕ) (s : RepeatState m) (b : Bool) :
    Measurable (fun r => repeatStep m L r s b) := by
  classical
  cases hs : selectActive s with
  | none => simp only [repeatStep,hs]; exact measurable_const
  | some i =>
    simp only [repeatStep,hs]
    apply Measurable.of_eval
    intro j
    by_cases hji : j = i
    · subst j
      simp only [Function.update_self]
      exact (measurable_batchStep L (s i) b).comp
        (show Measurable (fun r : RepeatSeed => r i.val) from measurable_pi_apply i.val)
    · simp [Function.update_of_ne hji]

def repeatRun (m L : ℕ) (r : RepeatSeed) (s : RepeatState m) (xs : List Bool) : RepeatState m :=
  xs.foldl (repeatStep m L r) s

theorem measurable_repeatRun (m L : ℕ) (xs : List Bool) :
    Measurable (fun z : RepeatSeed × RepeatState m => repeatRun m L z.1 z.2 xs) := by
  induction xs with
  | nil => exact measurable_snd
  | cons b xs ih =>
    have hs : Measurable (fun z : RepeatSeed × RepeatState m => repeatStep m L z.1 z.2 b) :=
      measurable_from_prod_countable_left (fun s => measurable_repeatStep m L s b)
    exact ih.comp (measurable_fst.prodMk hs)

theorem repeatRun_append (m L : ℕ) (r : RepeatSeed) (s : RepeatState m) (xs ys : List Bool) :
    repeatRun m L r s (xs++ys) = repeatRun m L r (repeatRun m L r s xs) ys :=
  List.foldl_append

def repeatPolicy (m L : ℕ) (r : RepeatSeed) (xs : List Bool) : Option ℕ :=
  repeatLabel (repeatRun m L r (repeatInitial m) xs)

theorem measurable_repeatPolicy (m L : ℕ) (xs : List Bool) :
    Measurable (fun r => repeatPolicy m L r xs) :=
  (measurable_of_countable repeatLabel).comp
    ((measurable_repeatRun m L xs).comp (measurable_id.prodMk measurable_const))

theorem repeatPolicy_measurable (m L : ℕ) : MeasurableCreationPolicy (repeatPolicy m L) :=
  fun xs _a => measurableSet_eq_fun (measurable_repeatPolicy m L xs) measurable_const

def repeatControlOutput (m L : ℕ) (r : RepeatSeed) (s : RepeatState m) : ℝ :=
  median m (fun i => controlOutput L (r i.val) (s i).1)

theorem measurable_repeatControlOutput (m L : ℕ) (s : RepeatState m) :
    Measurable (fun r => repeatControlOutput m L r s) :=
  measurable_median m _ (fun i => (measurable_controlOutput L (s i).1).comp (measurable_pi_apply i.val))

attribute [local irreducible] repeatPolicy repeatRun repeatControlOutput

def repeatHaltTime (m L : ℕ) (z : RepeatSeed × ProcessTape) : ℕ∞ :=
  firstSuccess (fun n => (repeatPolicy m L z.1 (processHistory z.2 n)).isNone)

theorem measurable_repeatHaltTime (m L : ℕ) : Measurable (repeatHaltTime m L) := by
  unfold repeatHaltTime
  have hp : Measurable (fun z : RepeatSeed × List Bool => repeatPolicy m L z.1 z.2) :=
    measurable_from_prod_countable_left (measurable_repeatPolicy m L)
  have hm : Measurable (fun z : RepeatSeed × ProcessTape =>
      fun n => (repeatPolicy m L z.1 (processHistory z.2 n)).isNone) := by
    apply Measurable.of_eval
    intro n
    have hh : Measurable (fun z : RepeatSeed × ProcessTape => (z.1, processHistory z.2 n)) :=
      measurable_fst.prodMk ((measurable_processHistory_fixed n).comp measurable_snd)
    have hn := (measurable_of_countable Option.isNone).comp (hp.comp hh)
    simpa only [Function.comp_def] using hn
  exact measurable_firstSuccess.comp hm

attribute [local irreducible] repeatHaltTime

def repeatOutput (m L : ℕ) (z : RepeatSeed × ProcessTape) : ℝ :=
  repeatControlOutput m L z.1 (repeatRun m L z.1 (repeatInitial m)
    (processHistory z.2 (repeatHaltTime m L z).toNat))

theorem measurable_repeatOutput (m L : ℕ) : Measurable (repeatOutput m L) := by
  unfold repeatOutput
  have ht :=
    (measurable_of_countable ENat.toNat).comp (measurable_repeatHaltTime m L)
  have hh : Measurable (fun z : ℕ × ProcessTape => processHistory z.2 z.1) :=
    measurable_from_prod_countable_right measurable_processHistory_fixed
  have hr : Measurable (fun z : RepeatSeed × List Bool => repeatRun m L z.1 (repeatInitial m) z.2) :=
    measurable_from_prod_countable_left (fun xs =>
      (measurable_repeatRun m L xs).comp (measurable_id.prodMk measurable_const))
  have ho : Measurable (fun z : RepeatSeed × RepeatState m => repeatControlOutput m L z.1 z.2) :=
    measurable_from_prod_countable_left (measurable_repeatControlOutput m L)
  have hout := ho.comp (measurable_fst.prodMk
    (hr.comp (measurable_fst.prodMk (hh.comp (ht.prodMk measurable_snd)))))
  exact hout

def repeatEstimator (m L : ℕ) : AdaptiveEstimator RepeatSeed where
  randomLaw := repeatSeedLaw
  probability := repeatSeedLaw_probability
  policy := repeatPolicy m L
  policy_measurable := repeatPolicy_measurable m L
  output := repeatOutput m L
  output_measurable := measurable_repeatOutput m L

end ThresholdHC.Confidence
