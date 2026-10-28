import ThresholdHC.BlindUpper.CallObservation
import ThresholdHC.BlindUpper.SeedInput

noncomputable section
namespace ThresholdHC.BlindUpper
open MeasureTheory ThresholdHC.CriticalEntropy ThresholdHC.Tier2
open ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.Tier6
open ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.Tier6
open ThresholdHC.CriticalEntropy

/-- Controller state retains only call counts and observed production words. -/
inductive BatchControl
  | pilotOne (failures : ℕ)
  | pilotTwo (firstFailures failures : ℕ)
  | production (failures : ℕ) (samples : List (List Bool))
  | stopped (samples : List (List Bool))
  deriving Countable, DecidableEq

instance batchControlMeasurableSpace : MeasurableSpace BatchControl := ⊤

def controlLabel : BatchControl → Option ℕ
  | .pilotOne i => some (Nat.pair 0 i)
  | .pilotTwo _ i => some (Nat.pair 1 i)
  | .production _ xs => some (Nat.pair 2 xs.length)
  | .stopped _ => none

def observedMark (L : ℕ) (r : BatchSeed) (j : ℕ) (xs : List Bool) : Bool :=
  decide ((r j).2 < (xs.length : ℝ)/(2 : ℝ)^L)

theorem measurable_observedMark (L j : ℕ) (xs : List Bool) :
    Measurable (fun r : BatchSeed => observedMark L r j xs) := by
  unfold observedMark
  have hm : Measurable (fun r : BatchSeed => (r j).2) := (measurable_pi_apply j).snd
  have he : (fun r : BatchSeed => decide ((r j).2 < (xs.length : ℝ)/(2 : ℝ)^L)) =
      (fun r => if (r j).2 < (xs.length : ℝ)/(2 : ℝ)^L then true else false) := by
    funext r
    split_ifs <;> simp_all
  rw [he]
  exact measurable_const.ite (measurableSet_lt hm measurable_const) measurable_const

def controlAdvance (L : ℕ) (r : BatchSeed) (c : BatchControl) (xs : List Bool) : BatchControl :=
  match c with
  | .pilotOne i => if observedMark L r (Nat.pair 0 i) xs then .pilotTwo i 0 else .pilotOne (i+1)
  | .pilotTwo a i => if observedMark L r (Nat.pair 1 i) xs then .production (a+i) [] else .pilotTwo a (i+1)
  | .production f ws => if ws.length = f then .stopped (ws++[xs]) else .production f (ws++[xs])
  | .stopped ws => .stopped ws

theorem measurable_controlAdvance (L : ℕ) (c : BatchControl) (xs : List Bool) :
    Measurable (fun r => controlAdvance L r c xs) := by
  cases c with
  | pilotOne i =>
    exact measurable_const.ite
      (measurableSet_eq_fun (measurable_observedMark L _ xs) measurable_const) measurable_const
  | pilotTwo a i =>
    exact measurable_const.ite
      (measurableSet_eq_fun (measurable_observedMark L _ xs) measurable_const) measurable_const
  | production f ws => exact measurable_const
  | stopped ws => exact measurable_const

abbrev BatchMachineState := BatchControl × List Bool

def batchInitial : BatchMachineState := (.pilotOne 0,[])

/-- Every step consumes one observed flip. A call's seed level and its observed
prefix decide completion. Only the observed cost enters its randomized mark. -/
def batchStep (L : ℕ) (r : BatchSeed) (s : BatchMachineState) (b : Bool) : BatchMachineState :=
  match controlLabel s.1 with
  | none => s
  | some j =>
    let xs := s.2++[b]
    if observedCutoffDone L (r j).1 xs then (controlAdvance L r s.1 xs,[]) else (s.1,xs)

theorem measurable_batchStep (L : ℕ) (s : BatchMachineState) (b : Bool) :
    Measurable (fun r => batchStep L r s b) := by
  cases hj : controlLabel s.1 with
  | none => simp only [batchStep,hj]; exact measurable_const
  | some j =>
    simp only [batchStep,hj]
    have hm : Measurable (fun r : BatchSeed => observedCutoffDone L (r j).1 (s.2++[b])) :=
      (measurable_of_countable (fun l => observedCutoffDone L l (s.2++[b]))).comp
        (measurable_pi_apply j).fst
    exact ((measurable_controlAdvance L s.1 (s.2++[b])).prodMk measurable_const).ite
      (measurableSet_eq_fun hm measurable_const) measurable_const

def batchRun (L : ℕ) (r : BatchSeed) (s : BatchMachineState) (xs : List Bool) : BatchMachineState :=
  xs.foldl (batchStep L r) s

theorem measurable_batchRun (L : ℕ) (xs : List Bool) :
    Measurable (fun z : BatchSeed × BatchMachineState => batchRun L z.1 z.2 xs) := by
  induction xs with
  | nil => exact measurable_snd
  | cons b xs ih =>
    have hs : Measurable (fun z : BatchSeed × BatchMachineState => batchStep L z.1 z.2 b) :=
      measurable_from_prod_countable_left (fun s => measurable_batchStep L s b)
    exact ih.comp (measurable_fst.prodMk hs)

theorem batchRun_append (L : ℕ) (r : BatchSeed) (s : BatchMachineState) (xs ys : List Bool) :
    batchRun L r s (xs++ys) = batchRun L r (batchRun L r s xs) ys :=
  List.foldl_append

def batchPolicy (L : ℕ) (r : BatchSeed) (xs : List Bool) : Option ℕ :=
  controlLabel (batchRun L r batchInitial xs).1

theorem measurable_batchPolicy (L : ℕ) (xs : List Bool) : Measurable (fun r => batchPolicy L r xs) :=
  (measurable_of_countable controlLabel).comp
    (((measurable_batchRun L xs).comp (measurable_id.prodMk measurable_const)).fst)

theorem batchPolicy_measurable (L : ℕ) : MeasurableCreationPolicy (batchPolicy L) :=
  fun xs a => measurableSet_eq_fun (measurable_batchPolicy L xs) measurable_const

theorem batchStep_stopped (L : ℕ) (r : BatchSeed) (ws : List (List Bool)) (xs : List Bool) (b : Bool) :
    batchStep L r (.stopped ws,xs) b = (.stopped ws,xs) := rfl

theorem batchRun_stopped (L : ℕ) (r : BatchSeed) (ws : List (List Bool)) (xs ys : List Bool) :
    batchRun L r (.stopped ws,xs) ys = (.stopped ws,xs) := by
  induction ys with
  | nil => rfl
  | cons b ys ih => exact ih

def controlOutput (L : ℕ) (r : BatchSeed) : BatchControl → ℝ
  | .stopped ws => (∑ i : Fin ws.length,
      cutoffValue L ((r (Nat.pair 2 i.val)).1,completeList ws[i.val])) / (ws.length : ℝ)
  | _ => 0

theorem measurable_controlOutput (L : ℕ) (c : BatchControl) :
    Measurable (fun r => controlOutput L r c) := by
  cases c with
  | stopped ws =>
    apply Measurable.div_const
    apply Finset.measurable_sum
    intro i hi
    exact (measurable_cutoffValue L).comp
      ((measurable_pi_apply (Nat.pair 2 i.val)).fst.prodMk measurable_const)
  | _ => exact measurable_const

theorem measurable_processHistory_fixed (n : ℕ) : Measurable (fun x : ProcessTape => processHistory x n) :=
  (measurable_of_countable (fun w : Fin n → Option Bool => (List.ofFn w).filterMap id)).comp
    (Measurable.of_eval (fun i => measurable_pi_apply i.val))

def batchHaltTime (L : ℕ) (z : BatchSeed × ProcessTape) : ℕ∞ :=
  firstSuccess (fun n => (batchPolicy L z.1 (processHistory z.2 n)).isNone)

set_option maxHeartbeats 800000 in
theorem measurable_batchHaltTime (L : ℕ) : Measurable (batchHaltTime L) := by
  apply measurable_firstSuccess.comp
  apply Measurable.of_eval
  intro n
  have hp : Measurable (fun z : BatchSeed × List Bool => batchPolicy L z.1 z.2) :=
    measurable_from_prod_countable_left (measurable_batchPolicy L)
  exact (measurable_of_countable Option.isNone).comp
    (hp.comp (measurable_fst.prodMk ((measurable_processHistory_fixed n).comp measurable_snd)))

def batchOutput (L : ℕ) (z : BatchSeed × ProcessTape) : ℝ :=
  controlOutput L z.1 (batchRun L z.1 batchInitial (processHistory z.2 (batchHaltTime L z).toNat)).1

set_option maxHeartbeats 800000 in
theorem measurable_batchOutput (L : ℕ) : Measurable (batchOutput L) := by
  have ht : Measurable (fun z : BatchSeed × ProcessTape => (batchHaltTime L z).toNat) :=
    (measurable_of_countable ENat.toNat).comp (measurable_batchHaltTime L)
  have hh : Measurable (fun z : ℕ × ProcessTape => processHistory z.2 z.1) :=
    measurable_from_prod_countable_right measurable_processHistory_fixed
  have hr : Measurable (fun z : BatchSeed × List Bool => batchRun L z.1 batchInitial z.2) :=
    measurable_from_prod_countable_left (fun xs =>
      (measurable_batchRun L xs).comp (measurable_id.prodMk measurable_const))
  have ho : Measurable (fun z : BatchSeed × BatchControl => controlOutput L z.1 z.2) :=
    measurable_from_prod_countable_left (measurable_controlOutput L)
  exact ho.comp (measurable_fst.prodMk
    ((hr.comp (measurable_fst.prodMk (hh.comp (ht.prodMk measurable_snd)))).fst))

/-- A concrete member of the original algorithm class. Performance identities
with the calibrated independent calls are separate obligations. -/
def batchEstimator (L : ℕ) : AdaptiveEstimator BatchSeed where
  randomLaw := batchSeedLaw
  probability := batchSeedLaw_probability
  policy := batchPolicy L
  policy_measurable := batchPolicy_measurable L
  output := batchOutput L
  output_measurable := measurable_batchOutput L

end ThresholdHC.BlindUpper
