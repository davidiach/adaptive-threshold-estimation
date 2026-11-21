import ThresholdHC.HardCapNecessity.Base

/-! The two controllers without independent complete runs, and their floors.

`sharedController` runs the fallback controller of `HardBudget` on the
constant seed array, so one delay bit drives every stage. `singleFallback`
makes one capped run of a stage and returns the midpoint on timeout. On the
delay bit every stage `j ≥ 2` of the base family times out at its cap, so any
estimator with the base seed law and either output has squared risk at least
`(1/8) (1/8)^2 = 1/512` at `theta = 0`. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.HardCapNecessity
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.ObservableSimulation ThresholdHC.HardBudget
open ThresholdHC.BlindUpper ThresholdHC.PaperStatements ThresholdHC.UpperMixture ThresholdHC.RareAboveTwo

section Controllers
variable {S : Type} [MeasurableSpace S]

theorem measurable_constArray : Measurable (fun r : S => fun _ : ℕ => r) :=
  Measurable.of_eval (fun _ => measurable_id)

/-- The fallback controller of `HardBudget` fed one seed at every stage. -/
def sharedController (base : ℕ → AdaptiveEstimator S) (M : ℝ) (k : ℕ) : AdaptiveEstimator S where
  randomLaw := (base 0).randomLaw
  probability := inferInstance
  policy r := (estimator (R := fun _ => S) base M k).policy (fun _ => r)
  policy_measurable := fun xs a =>
    measurable_constArray ((estimator (R := fun _ => S) base M k).policy_measurable xs a)
  output z := (estimator (R := fun _ => S) base M k).output (fun _ => z.1, z.2)
  output_measurable := (estimator (R := fun _ => S) base M k).output_measurable.comp
    ((measurable_constArray.comp measurable_fst).prodMk measurable_snd)

theorem shared_output (base : ℕ → AdaptiveEstimator S) (M : ℝ) (k : ℕ) (r : S) (s : Table) :
    (sharedController base M k).output (r, populationPath ((sharedController base M k).policy r) s) =
      idealFallback (R := fun _ => S) base M (fun _ => r) s k :=
  estimator_output (R := fun _ => S) base M k (fun _ => r) s

theorem shared_cap (base : ℕ → AdaptiveEstimator S) (M : ℝ) (k : ℕ) :
    PathwiseCap (sharedController base M k) (paid k) :=
  stopAt_pathwise_cap _ _ (fun r => planReader (R := fun _ => S) base (fun _ => r) k) (fun _ => rfl)

/-- One run of `A` capped at `n` flips, returning the midpoint on timeout. -/
def singleFallback (A : AdaptiveEstimator S) (M : ℝ) (n : ℕ) : AdaptiveEstimator S where
  randomLaw := A.randomLaw
  probability := A.probability
  policy r := stopAt n (fun h => (A.policy r h).getD 0)
  policy_measurable := by
    intro xs a
    by_cases h : xs.length < n
    · simp only [stopAt, ite_eq_left h]
      have hg : Measurable (fun r => (A.policy r xs).getD 0) :=
        (measurable_of_countable (fun o : Option ℕ => o.getD 0)).comp
          (measurable_to_countable' (A.policy_measurable xs))
      exact measurableSet_eq_fun ((measurable_of_countable some).comp hg) measurable_const
    · simp [stopAt, h]
  output z := (stageOutput A M z.1 (processHistory z.2 n)).getD (M/2)
  output_measurable := by
    have hm : Measurable (fun u : S × List Bool => (stageOutput A M u.1 u.2).getD (M/2)) :=
      measurable_from_prod_countable_left (fun w =>
        measurable_stage_getD A M w id measurable_id (fun _ => M/2) measurable_const)
    exact hm.comp (measurable_fst.prodMk ((measurable_processHistory_fixed n).comp measurable_snd))

theorem single_output (A : AdaptiveEstimator S) (M : ℝ) (n : ℕ) (r : S) (s : Table) :
    (singleFallback A M n).output (r, populationPath ((singleFallback A M n).policy r) s) =
      (stageResult A n M r s).getD (M/2) := by
  obtain ⟨w, hw⟩ : ∃ w, w = (readBlock n (fun h => (A.policy r h).getD 0) s).1 := ⟨_, rfl⟩
  have hlen : w.length = n := hw ▸ readBlock_length _ _ _
  have hp : populationPath ((singleFallback A M n).policy r) s = fun k => w[k]? :=
    hw ▸ block_path n (fun h => (A.policy r h).getD 0) s
  have hh : processHistory (fun k => w[k]?) n = w := by
    have h := processHistory_word w
    rwa [hlen] at h
  change (stageOutput A M r (processHistory (populationPath ((singleFallback A M n).policy r) s) n)).getD (M/2) = _
  rw [hp, hh, hw, stageOutput_correct]

theorem single_cap (A : AdaptiveEstimator S) (M : ℝ) (n : ℕ) :
    PathwiseCap (singleFallback A M n) n :=
  stopAt_pathwise_cap _ _ (fun r h => (A.policy r h).getD 0) (fun _ => rfl)

end Controllers

theorem history_length_le (x : ProcessTape) (n : ℕ) : (processHistory x n).length ≤ n := by
  unfold processHistory
  exact (List.length_filterMap_le _ _).trans (by simp)

/-- Stages `0` and `1` return the midpoint on every seed. -/
theorem mid_stage (r : Bool × Unit) (n : ℕ) (s : Table) :
    stageResult midBase n (1/4) r s = some (1/8) := by
  obtain ⟨b, u⟩ := r
  have hc : clipEstimate (1/4) (1/8) = 1/8 := by norm_num [clipEstimate]
  cases b <;> simpa [stageResult, midBase, mixEstimator, constantEstimator, immediateEstimator] using hc

/-- On the delay bit, stage `i+2` is still buying flips at its cap. -/
theorem delay_timeout (i : ℕ) (s : Table) :
    stageResult (capBase (i+2)) (stageCap (i+2)) (1/4) (true, ()) s = none := by
  let x := populationPath ((capBase (i+2)).policy (true, ())) s
  have hlen := history_length_le x (stageCap (i+2))
  have hcap : stageCap (i+2) < 17*2^i-1+1 := by
    have := @Nat.one_le_two_pow i
    simp only [stageCap, stageAllowance, pow_add]
    omega
  have hpol : (capBase (i+2)).policy (true, ()) (processHistory x (stageCap (i+2))) ≠ none := by
    change ThresholdHC.Tier5.freshPolicy (17*2^i-1) (processHistory x (stageCap (i+2))) ≠ none
    unfold ThresholdHC.Tier5.freshPolicy
    rw [ite_eq_left (lt_of_le_of_lt hlen hcap)]
    exact Option.some_ne_none _
  unfold stageResult
  exact ite_eq_right hpol

/-- With the delay bit at every stage, the ladder output is the midpoint. -/
theorem all_delay (s : Table) (k : ℕ) :
    idealFallback (R := fun _ => Bool × Unit) capBase (1/4) (fun _ => (true, ())) s k = 1/8 := by
  induction k with
  | zero => change (1/4 : ℝ)/2 = 1/8; norm_num
  | succ k ih =>
    change (stageResult (capBase k) (stageCap k) (1/4) (true, ()) (fun c => s (Nat.pair k c))).getD
      (idealFallback (R := fun _ => Bool × Unit) capBase (1/4) (fun _ => (true, ())) s k) = 1/8
    match k, ih with
    | 0, _ => rw [show capBase 0 = midBase from rfl, mid_stage]; rfl
    | 1, _ => rw [show capBase 1 = midBase from rfl, mid_stage]; rfl
    | i+2, ih => rw [delay_timeout, Option.getD_none, ih]

/-- An estimator with the delay-coin seed law that returns `t` on every table
when the coin shows `true` has squared risk at least `clip p * (t - θ)^2`. -/
theorem seed_floor (A : AdaptiveEstimator (Bool × Unit)) (p : ℝ)
    (hA : A.randomLaw = (coinLaw p).prod (Measure.dirac ())) (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (θ t : ℝ)
    (ht : ∀ s, A.output ((true, ()), populationPath (A.policy (true, ())) s) = t) :
    ENNReal.ofReal (clip p) * ENNReal.ofReal ((t - θ)^2) ≤
      squaredRisk (experimentLaw μ A q) (populationOutput A) θ := by
  rw [original_squaredRisk_simulation]
  unfold originalSimulationLaw
  rw [hA]
  have hm : Measurable (fun z : (Bool × Unit) × (ℕ → ℕ → Bool) =>
      (z.1, populationPath (A.policy z.1) z.2)) :=
    measurable_fst.prodMk (measurable_seeded_populationPath A.policy
      (fun xs => measurable_to_countable' (A.policy_measurable xs)))
  have hO : Measurable (fun z : (Bool × Unit) × ProcessTape => ENNReal.ofReal ((A.output z - θ) ^ 2)) :=
    ((A.output_measurable.sub measurable_const).pow_const 2).ennreal_ofReal
  rw [lintegral_coin_prod p (Measure.dirac ()) _
    (fun z => ENNReal.ofReal ((A.output (z.1, populationPath (A.policy z.1) z.2) - θ)^2)) (hO.comp hm)]
  refine le_trans ?_ le_self_add
  gcongr
  have he : (fun z : Unit × (ℕ → ℕ → Bool) => ((fun z : (Bool × Unit) × (ℕ → ℕ → Bool) =>
      ENNReal.ofReal ((A.output (z.1, populationPath (A.policy z.1) z.2) - θ) ^ 2)) ((true, z.1), z.2))) =
      fun _ => ENNReal.ofReal ((t - θ)^2) := by
    funext z
    dsimp only
    rw [ht z.2]
  rw [he, lintegral_const, measure_univ, mul_one]

theorem zero_target : signMean (Measure.dirac halfGap) zeroSigns.val = 0 := by
  simp [signMean, zeroSigns]

theorem eighth_floor (A : AdaptiveEstimator (Bool × Unit)) (hA : A.randomLaw = delaySeedLaw)
    (ht : ∀ s, A.output ((true, ()), populationPath (A.policy (true, ())) s) = 1/8) :
    ENNReal.ofReal (1/512) ≤
      squaredRisk (experimentLaw (Measure.dirac halfGap) A zeroSigns) (populationOutput A)
        (signMean (Measure.dirac halfGap) zeroSigns.val) := by
  have h := seed_floor A (1/8) hA (Measure.dirac halfGap) zeroSigns 0 (1/8) ht
  rw [clip_eighth, ← ENNReal.ofReal_mul (by norm_num)] at h
  rw [zero_target]
  convert h using 2
  norm_num

/-- Every estimator with the base seed law and the shared-seed ladder output
at any depth has squared risk at least `1/512` at `theta = 0`. -/
theorem ladder_floor (k : ℕ) (A : AdaptiveEstimator (Bool × Unit))
    (hA : A.randomLaw = (capBase 0).randomLaw)
    (hout : ∀ r table, A.output (r, populationPath (A.policy r) table) =
      idealFallback (R := fun _ => Bool × Unit) capBase (1/4) (fun _ => r) table k) :
    ENNReal.ofReal (1/512) ≤
      squaredRisk (experimentLaw (Measure.dirac halfGap) A zeroSigns) (populationOutput A)
        (signMean (Measure.dirac halfGap) zeroSigns.val) :=
  eighth_floor A (hA.trans (capBase_seed 0)) (fun s => (hout (true, ()) s).trans (all_delay s k))

/-- Every estimator with the stage seed law whose output is one capped run of a
stage `j ≥ 2` with the midpoint on timeout has squared risk at least `1/512`. -/
theorem single_floor (j : ℕ) (hj : 2 ≤ j) (A : AdaptiveEstimator (Bool × Unit))
    (hA : A.randomLaw = (capBase j).randomLaw)
    (hout : ∀ r table, A.output (r, populationPath (A.policy r) table) =
      (stageResult (capBase j) (stageCap j) (1/4) r table).getD (1/8)) :
    ENNReal.ofReal (1/512) ≤
      squaredRisk (experimentLaw (Measure.dirac halfGap) A zeroSigns) (populationOutput A)
        (signMean (Measure.dirac halfGap) zeroSigns.val) := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le' hj
  refine eighth_floor A (hA.trans (capBase_seed _)) (fun s => ?_)
  rw [hout, delay_timeout, Option.getD_none]

end ThresholdHC.HardCapNecessity
