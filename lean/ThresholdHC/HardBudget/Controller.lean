import ThresholdHC.HardBudget.Schedule

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.HardBudget
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.CriticalEntropy ThresholdHC.BlindUpper
open ThresholdHC.ObservableSimulation

local instance : MeasurableSpace (Option (List Bool)) := ⊤

private theorem measurable_decode {R : Type} [MeasurableSpace R]
    (p : R → List Bool → Option ℕ) (hp : ThresholdHC.Tier5.MeasurableCreationPolicy p)
    (w : List Bool) : Measurable (fun r => decode (p r) w) := by
  induction w generalizing p with
  | nil => exact Measurable.ite (hp [] none) measurable_const measurable_const
  | cons b w ih =>
    have h := ih (fun r xs => p r (b::xs)) (fun xs => hp (b::xs))
    exact Measurable.ite (hp [] none) measurable_const
      ((measurable_of_countable (fun v : Option (List Bool) => v.map (b::·))).comp h)

theorem measurable_clip (M : ℝ) : Measurable (clipEstimate M) := by
  unfold clipEstimate; fun_prop

theorem measurable_stage_getD {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R)
    (M : ℝ) (w : List Bool) {S : Type} [MeasurableSpace S] (r : S → R) (hr : Measurable r)
    (z : S → ℝ) (hz : Measurable z) :
    Measurable (fun u => (stageOutput A M (r u) w).getD (z u)) := by
  let f (x : S × Option (List Bool)) : ℝ :=
    match x.2 with
    | none => z x.1
    | some v => clipEstimate M (A.output (r x.1,fun n => v[n]?))
  have hf : Measurable f := by
    apply measurable_from_prod_countable_left
    intro a; cases a with
    | none => exact hz
    | some v => exact (measurable_clip M).comp (A.output_measurable.comp (hr.prodMk measurable_const))
  convert hf.comp (measurable_id.prodMk ((measurable_decode _ A.policy_measurable w).comp hr)) using 1
  funext u
  dsimp only [Function.comp_apply,id_eq,stageOutput,f]
  cases decode (A.policy (r u)) w <;> rfl

variable {R : ℕ → Type} [∀ j, MeasurableSpace (R j)]

theorem measurable_planReader (base : ∀ j, AdaptiveEstimator (R j)) (k : ℕ) (xs : List Bool) :
    Measurable (fun r => planReader base r k xs) := by
  induction k generalizing xs with
  | zero => exact measurable_const
  | succ n ih =>
    by_cases h : xs.length < paid n
    · simp only [planReader,thenRead,ite_eq_left h]; exact ih xs
    · simp only [planReader,thenRead,ite_eq_right_iff.mpr (fun h' => (h h').elim),Function.comp_apply]
      exact (measurable_of_countable (fun a : Option ℕ => Nat.pair n (a.getD 0))).comp
        ((measurable_to_countable' ((base n).policy_measurable _)).comp (measurable_pi_apply n))

theorem measurable_planOutput (base : ∀ j, AdaptiveEstimator (R j)) (M : ℝ) (k : ℕ) (xs : List Bool) :
    Measurable (fun r => planOutput base M r k xs) := by
  induction k generalizing xs with
  | zero => exact measurable_const
  | succ k ih => exact measurable_stage_getD _ _ _ _ (measurable_pi_apply _) _ (ih _)

def estimator (base : ∀ j, AdaptiveEstimator (R j)) (M : ℝ) (k : ℕ) :
    AdaptiveEstimator (∀ j, R j) where
  randomLaw := Measure.infinitePi (fun j => (base j).randomLaw)
  probability := inferInstance
  policy r := stopAt (paid k) (planReader base r k)
  policy_measurable := by
    intro xs a
    by_cases h : xs.length < paid k
    · simp only [stopAt,ite_eq_left h]
      exact measurableSet_eq_fun ((measurable_of_countable some).comp (measurable_planReader base k xs)) measurable_const
    · simp [stopAt,h]
  output z := planOutput base M z.1 k (processHistory z.2 (paid k))
  output_measurable := by
    have hm : Measurable (fun z : (∀ j, R j) × List Bool => planOutput base M z.1 k z.2) :=
      measurable_from_prod_countable_left (measurable_planOutput base M k)
    exact hm.comp (measurable_fst.prodMk ((measurable_processHistory_fixed (paid k)).comp measurable_snd))

theorem estimator_output (base : ∀ j, AdaptiveEstimator (R j)) (M : ℝ) (k : ℕ)
    (r : ∀ j, R j) (s : Table) :
    (estimator base M k).output (r,populationPath ((estimator base M k).policy r) s) =
      idealFallback base M r s k := by
  let w := (readBlock (paid k) (planReader base r k) s).1
  have hp := block_path (paid k) (planReader base r k) s
  change populationPath ((estimator base M k).policy r) s = fun i => w[i]? at hp
  change planOutput base M r k (processHistory _ (paid k)) = _
  rw [hp,← show w.length = paid k from readBlock_length _ _ _,processHistory_word]
  exact planOutput_readBlock base M r s k

private theorem history_succ (x : ProcessTape) (j : ℕ) :
    processHistory x (j+1) = processHistory x j ++ (x j).toList := by
  unfold processHistory
  rw [List.ofFn_succ']
  cases h : x j <;> simp [processPrefix,List.concat_eq_append,h] <;> rfl

private theorem work_history (x : ProcessTape) (j : ℕ) :
    ThresholdHC.workOf (processPrefix j x) = ((processHistory x j).length : ℝ) := by
  induction j with
  | zero => simp [ThresholdHC.workOf,processHistory]
  | succ j ih =>
    rw [processPrefix_snoc,ThresholdHC.Proofs.workOf_snoc,ih,history_succ,List.length_append]
    cases h : x j <;> simp

theorem stopAt_pathwise_cap {S : Type} [MeasurableSpace S] (A : AdaptiveEstimator S) (n : ℕ)
    (p : S → Reader) (hp : ∀ r, A.policy r = stopAt n (p r)) : PathwiseCap A n := by
  intro r x hv
  simp_rw [hp] at hv
  have hlen (j : ℕ) : (processHistory x j).length ≤ n := by
    induction j with
    | zero => simp [processHistory]
    | succ j ih =>
      rw [history_succ,List.length_append]
      by_cases h : (processHistory x j).length < n
      · cases x j <;> simp <;> omega
      · have hx := hv j
        simp [stopAt,h] at hx
        rw [hx]; simpa using ih
  apply iSup_le
  intro j
  rw [work_history,ENNReal.ofReal_natCast]
  exact_mod_cast hlen j

theorem estimator_cap (base : ∀ j, AdaptiveEstimator (R j)) (M : ℝ) (k : ℕ) :
    PathwiseCap (estimator base M k) (paid k) :=
  stopAt_pathwise_cap _ _ _ (fun _ => rfl)

end ThresholdHC.HardBudget
