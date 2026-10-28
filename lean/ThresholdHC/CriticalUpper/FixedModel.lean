import ThresholdHC.CriticalUpper.Average
import ThresholdHC.BlindUpper.CallExecution

/-! A measurable fixed-count controller that observes only its seeds and coin flips. -/

noncomputable section
namespace ThresholdHC.CriticalUpper
open MeasureTheory ProbabilityTheory Set ThresholdHC.CriticalEntropy ThresholdHC.Uniform713
open ThresholdHC.Tier2 ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.Tier6
open ThresholdHC.ObservableSimulation ThresholdHC.BlindUpper
open scoped ENNReal

open ThresholdHC.Tier2 ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.Tier6
open ThresholdHC.ObservableSimulation
open BlindUpper

theorem coupledCost_pos (ρ : ℝ) (j : ℕ) (ω : ℕ → Bool) : 0 < coupledCost ρ j ω := by
  have h (k : ℕ) : 0 < calibratedCost ρ k ω := screenCost_pos _ _ _ _
  cases j with
  | zero => exact h 0
  | succ j => exact lt_of_lt_of_le (h (j+1)) (le_max_left _ _)

def criticalReady (ρ : ℝ) (j : ℕ) (xs : List Bool) : Bool :=
  decide (coupledCost ρ j (completeList xs) ≤ xs.length)

theorem criticalReady_word (ρ : ℝ) (j n : ℕ) (ω : ℕ → Bool) :
    criticalReady ρ j (tapeWord n ω) = decide (coupledCost ρ j ω ≤ n) := by
  have h := finiteCall_ready_iff (fun z : ℕ × (ℕ → Bool) => coupledCost ρ z.1 z.2)
    (fun j ω ω' h => (coupled_prefix_ext ρ j ω ω' h).1) j ω n
  simp only [criticalReady,tapeWord_length,h]

abbrev FixedState := List (List Bool) × List Bool

instance boolWordsMeasurableSpace : MeasurableSpace (List (List Bool)) := ⊤

def fixedLabel (N : ℕ) (s : FixedState) : Option ℕ :=
  if s.1.length < N then some s.1.length else none

def fixedStep (ρ : ℝ) (N : ℕ) (r : CriticalSeed) (s : FixedState) (b : Bool) : FixedState :=
  if s.1.length < N then
    let xs := s.2++[b]
    if criticalReady ρ (r s.1.length) xs then (s.1++[xs],[]) else (s.1,xs)
  else s

theorem measurable_fixedStep (ρ : ℝ) (N : ℕ) (s : FixedState) (b : Bool) :
    Measurable (fun r => fixedStep ρ N r s b) := by
  unfold fixedStep
  by_cases h : s.1.length < N
  · simp only [h,ite_true]
    have hm : Measurable (fun r : CriticalSeed => criticalReady ρ (r s.1.length) (s.2++[b])) :=
      (measurable_of_countable (fun j => criticalReady ρ j (s.2++[b]))).comp
        (measurable_pi_apply s.1.length)
    exact measurable_const.ite (measurableSet_eq_fun hm measurable_const) measurable_const
  · simpa only [h,ite_false] using (measurable_const : Measurable (fun _ : CriticalSeed => s))

def fixedRun (ρ : ℝ) (N : ℕ) (r : CriticalSeed) (s : FixedState) (xs : List Bool) : FixedState :=
  xs.foldl (fixedStep ρ N r) s

theorem fixedRun_append (ρ : ℝ) (N : ℕ) (r : CriticalSeed) (s : FixedState) (xs ys : List Bool) :
    fixedRun ρ N r s (xs++ys) = fixedRun ρ N r (fixedRun ρ N r s xs) ys :=
  List.foldl_append

theorem measurable_fixedRun (ρ : ℝ) (N : ℕ) (xs : List Bool) :
    Measurable (fun z : CriticalSeed × FixedState => fixedRun ρ N z.1 z.2 xs) := by
  induction xs with
  | nil => exact measurable_snd
  | cons b xs ih =>
    have hs : Measurable (fun z : CriticalSeed × FixedState => fixedStep ρ N z.1 z.2 b) :=
      measurable_from_prod_countable_left (fun s => measurable_fixedStep ρ N s b)
    exact ih.comp (measurable_fst.prodMk hs)

def fixedPolicy (ρ : ℝ) (N : ℕ) (r : CriticalSeed) (xs : List Bool) : Option ℕ :=
  fixedLabel N (fixedRun ρ N r ([],[]) xs)

theorem measurable_fixedPolicy (ρ : ℝ) (N : ℕ) (xs : List Bool) :
    Measurable (fun r => fixedPolicy ρ N r xs) :=
  (measurable_of_countable (fixedLabel N)).comp
    ((measurable_fixedRun ρ N xs).comp (measurable_id.prodMk measurable_const))

theorem fixedPolicy_measurable (ρ : ℝ) (N : ℕ) : MeasurableCreationPolicy (fixedPolicy ρ N) :=
  fun xs _ => measurableSet_eq_fun (measurable_fixedPolicy ρ N xs) measurable_const

theorem fixedRun_absorbs (ρ : ℝ) (N : ℕ) (r : CriticalSeed) (s : FixedState)
    (h : N ≤ s.1.length) (xs : List Bool) : fixedRun ρ N r s xs = s := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    change fixedRun ρ N r (fixedStep ρ N r s b) xs = s
    rw [show fixedStep ρ N r s b = s by simp [fixedStep,not_lt.mpr h]]
    exact ih

def fixedWordsOutput (ρ : ℝ) (r : CriticalSeed) (ws : List (List Bool)) : ℝ :=
  (∑ i : Fin ws.length, coupledValue ρ (r i.val) (completeList ws[i.val]))/(ws.length : ℝ)

theorem measurable_fixedWordsOutput (ρ : ℝ) (ws : List (List Bool)) :
    Measurable (fun r => fixedWordsOutput ρ r ws) := by
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro i _
  exact (measurable_of_countable (fun j => coupledValue ρ j (completeList ws[i.val]))).comp
    (measurable_pi_apply i.val)

def fixedHaltTime (ρ : ℝ) (N : ℕ) (z : CriticalSeed × ProcessTape) : ℕ∞ :=
  firstSuccess (fun n => (fixedPolicy ρ N z.1 (processHistory z.2 n)).isNone)

theorem measurable_fixedHaltTime (ρ : ℝ) (N : ℕ) : Measurable (fixedHaltTime ρ N) := by
  apply measurable_firstSuccess.comp
  apply Measurable.of_eval
  intro n
  have hp : Measurable (fun z : CriticalSeed × List Bool => fixedPolicy ρ N z.1 z.2) :=
    measurable_from_prod_countable_left (measurable_fixedPolicy ρ N)
  exact (measurable_of_countable Option.isNone).comp
    (hp.comp (measurable_fst.prodMk ((measurable_processHistory_fixed n).comp measurable_snd)))

def fixedOutput (ρ : ℝ) (N : ℕ) (z : CriticalSeed × ProcessTape) : ℝ :=
  fixedWordsOutput ρ z.1 (fixedRun ρ N z.1 ([],[])
    (processHistory z.2 (fixedHaltTime ρ N z).toNat)).1

set_option maxHeartbeats 800000 in
theorem measurable_fixedOutput (ρ : ℝ) (N : ℕ) : Measurable (fixedOutput ρ N) := by
  have ht : Measurable (fun z : CriticalSeed × ProcessTape => (fixedHaltTime ρ N z).toNat) :=
    (measurable_of_countable ENat.toNat).comp (measurable_fixedHaltTime ρ N)
  have hh : Measurable (fun z : ℕ × ProcessTape => processHistory z.2 z.1) :=
    measurable_from_prod_countable_right measurable_processHistory_fixed
  have hr : Measurable (fun z : CriticalSeed × List Bool => fixedRun ρ N z.1 ([],[]) z.2) :=
    measurable_from_prod_countable_left (fun xs =>
      (measurable_fixedRun ρ N xs).comp (measurable_id.prodMk measurable_const))
  have ho : Measurable (fun z : CriticalSeed × List (List Bool) => fixedWordsOutput ρ z.1 z.2) :=
    measurable_from_prod_countable_left (measurable_fixedWordsOutput ρ)
  exact ho.comp (measurable_fst.prodMk
    ((hr.comp (measurable_fst.prodMk (hh.comp (ht.prodMk measurable_snd)))).fst))

def fixedEstimator (ρ : ℝ) (n : ℕ) : AdaptiveEstimator CriticalSeed where
  randomLaw := criticalSeedLaw
  probability := criticalSeedLaw_probability
  policy := fixedPolicy ρ (n+1)
  policy_measurable := fixedPolicy_measurable ρ (n+1)
  output := fixedOutput ρ (n+1)
  output_measurable := measurable_fixedOutput ρ (n+1)

theorem fixedRun_call_partial (ρ : ℝ) (N : ℕ) (r : CriticalSeed) (ws : List (List Bool))
    (hws : ws.length < N) (ω : ℕ → Bool) (n : ℕ)
    (hn : n < coupledCost ρ (r ws.length) ω) :
    fixedRun ρ N r (ws,[]) (tapeWord n ω) = (ws,tapeWord n ω) := by
  induction n with
  | zero => simp [fixedRun,tapeWord]
  | succ n ih =>
    rw [tapeWord_succ,fixedRun_append,ih (by omega)]
    change fixedStep ρ N r (ws,tapeWord n ω) (ω n) = _
    simp only [fixedStep,hws,ite_true]
    rw [← tapeWord_succ,criticalReady_word]
    simp only [show ¬coupledCost ρ (r ws.length) ω ≤ n+1 by omega,decide_false,Bool.false_eq_true,ite_false]

theorem fixedRun_call_complete (ρ : ℝ) (N : ℕ) (r : CriticalSeed) (ws : List (List Bool))
    (hws : ws.length < N) (ω : ℕ → Bool) :
    fixedRun ρ N r (ws,[]) (tapeWord (coupledCost ρ (r ws.length) ω) ω) =
      (ws++[tapeWord (coupledCost ρ (r ws.length) ω) ω],[]) := by
  let T := coupledCost ρ (r ws.length) ω
  have hT : 0 < T := coupledCost_pos ρ _ _
  have hs : T = (T-1)+1 := by omega
  change fixedRun ρ N r (ws,[]) (tapeWord T ω) = (ws++[tapeWord T ω],[])
  conv_lhs => rw [hs,tapeWord_succ,fixedRun_append]
  rw [fixedRun_call_partial ρ N r ws hws ω (T-1) (by omega)]
  change fixedStep ρ N r (ws,tapeWord (T-1) ω) (ω (T-1)) = _
  simp only [fixedStep,hws,ite_true]
  rw [← tapeWord_succ,← hs,criticalReady_word]
  simp only [show coupledCost ρ (r ws.length) ω ≤ T from le_rfl,decide_true,ite_true]

theorem coupledValue_observed (ρ : ℝ) (j : ℕ) (ω : ℕ → Bool) :
    coupledValue ρ j (completeList (tapeWord (coupledCost ρ j ω) ω)) = coupledValue ρ j ω :=
  (coupled_prefix_ext ρ j ω _ (completeList_tapeWord_prefix _ _).symm).2

end ThresholdHC.CriticalUpper
