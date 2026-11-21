import ThresholdHC.TimeUniformTwoSided.Specification
import ThresholdHC.Anytime.Full

/-! The stage controllers of `ThresholdHC.Anytime` as one online policy in the
original observable experiment.

The limit policy reads the stage plan with enough reserved flips for every
history, so it never stops. Before the reservation `paid k` of stage `k` is
exhausted it makes the same choices as the stage-`k` endpoint controller
(`ThresholdHC.Anytime.planReader_compatible`). Its path therefore has the same
first `paid k` symbols. The interval at integer budget `n` is the stage-indexed
interval at stage `stageCount n`, computed from the first `n` observations;
since `paid (stageCount n) ≤ n`, it equals the stage-indexed interval pathwise.
The two experiments have the same seed-and-table law, so the simultaneous
coverage event of the stage family transfers to the original experiment. -/
noncomputable section
namespace ThresholdHC.TimeUniformTwoSided
open MeasureTheory
open scoped ENNReal
open ThresholdHC.Tier3 ThresholdHC.Tier4 ThresholdHC.Tier6 ThresholdHC.RareAboveTwo
open ThresholdHC.AnytimeLower ThresholdHC.HardBudget ThresholdHC.ObservableSimulation
open ThresholdHC.BlindUpper

variable {R : ℕ → Type} [∀ j, MeasurableSpace (R j)]

/-- The stage plan with a reservation longer than the history: it never stops. -/
def limitPolicy (base : ∀ j, AdaptiveEstimator (R j)) (r : ∀ j, R j) (xs : List Bool) :
    Option ℕ :=
  some (planReader base r (xs.length+1) xs)

/-- One adaptive estimator running every stage in turn on one private seed. Its
scalar output is unused; the intervals are read from its observed prefixes. -/
def limitEstimator (base : ∀ j, AdaptiveEstimator (R j)) : AdaptiveEstimator (∀ j, R j) where
  randomLaw := Measure.infinitePi (fun j => (base j).randomLaw)
  probability := inferInstance
  policy := limitPolicy base
  policy_measurable := by
    intro xs a
    change MeasurableSet {u | some (planReader base u (xs.length+1) xs) = a}
    exact measurableSet_eq_fun ((measurable_of_countable some).comp
      (measurable_planReader base (xs.length+1) xs)) measurable_const
  output := fun _ => 0
  output_measurable := measurable_const

theorem limitPolicy_agree (base : ∀ j, AdaptiveEstimator (R j)) (r : ∀ j, R j) (k : ℕ)
    (xs : List Bool) (hx : xs.length < paid k) :
    limitPolicy base r xs = stopAt (paid k) (planReader base r k) xs := by
  rw [limitPolicy,stopAt,ite_eq_left hx]
  congr 1
  by_cases hk : k ≤ xs.length+1
  · exact ThresholdHC.Anytime.planReader_compatible base r hk xs hx
  · exact (ThresholdHC.Anytime.planReader_compatible base r (by omega) xs
      (lt_of_lt_of_le (Nat.lt_succ_self _) (index_le_paid _))).symm

/-- Two policies that agree on every history shorter than `n` produce the same
first `n` symbols on every table. -/
theorem prefix_of_agree {pol pol' : List Bool → Option ℕ} (n : ℕ)
    (h : ∀ xs : List Bool, xs.length < n → pol' xs = pol xs) (s : Table) :
    processPrefix n (populationPath pol' s) = processPrefix n (populationPath pol s) := by
  rw [populationPath_prefix,populationPath_prefix]
  exact populationSimulation_word_embed id Function.injective_id n pol pol'
    (fun xs hx => by rw [h xs hx]; cases pol xs <;> rfl) s

theorem history_of_prefix {x y : ProcessTape} {n : ℕ}
    (h : processPrefix n x = processPrefix n y) : processHistory x n = processHistory y n := by
  unfold processHistory
  rw [h]

theorem history_pad {n m : ℕ} (hm : m ≤ n) (x : ProcessTape) :
    processHistory (padPrefix n (processPrefix n x)) m = processHistory x m := by
  apply history_of_prefix
  funext i
  have hi : i.val < n := lt_of_lt_of_le i.isLt hm
  simp only [processPrefix,padPrefix,dite_eq_left hi]

/-- The interval at integer budget `n`, from the seed and the first `n`
observations: the stage-indexed interval at the last completed stage. -/
def onlineInterval (base : ∀ j, AdaptiveEstimator (R j)) (M : ℝ) (radius : ℕ → ℝ) (n : ℕ)
    (y : (∀ j, R j) × Prefix n) : ℝ × ℝ :=
  ThresholdHC.Anytime.historyInterval base M radius y.1 (stageCount (n:ℝ))
    (processHistory (padPrefix n y.2) (paid (stageCount (n:ℝ))))

theorem measurable_onlineInterval (base : ∀ j, AdaptiveEstimator (R j)) (M : ℝ)
    (radius : ℕ → ℝ) (n : ℕ) : Measurable (onlineInterval base M radius n) := by
  have hm : Measurable (fun z : (∀ j, R j) × List Bool =>
      ThresholdHC.Anytime.historyInterval base M radius z.1 (stageCount (n:ℝ)) z.2) :=
    measurable_from_prod_countable_left
      (ThresholdHC.Anytime.measurable_historyInterval base M radius _)
  exact hm.comp (measurable_fst.prodMk ((measurable_processHistory_fixed _).comp
    ((measurable_padPrefix n).comp measurable_snd)))

/-- Pathwise readback: on every seed and table, the budget-`n` interval of the
limit policy is the stage-indexed interval at stage `stageCount n`. -/
theorem onlineInterval_readback (base : ∀ j, AdaptiveEstimator (R j)) (M : ℝ)
    (radius : ℕ → ℝ) (n : ℕ) (z : (∀ j, R j) × Table) :
    onlineInterval base M radius n
        (z.1,processPrefix n (populationPath ((limitEstimator base).policy z.1) z.2)) =
      ThresholdHC.Anytime.observedInterval base M radius (stageCount (n:ℝ)) z := by
  have hk : paid (stageCount (n:ℝ)) ≤ n := by
    simpa only [Nat.floor_natCast] using paid_fits (n:ℝ)
  have hh : processHistory (padPrefix n (processPrefix n
        (populationPath ((limitEstimator base).policy z.1) z.2))) (paid (stageCount (n:ℝ))) =
      processHistory (populationPath ((ThresholdHC.Anytime.endpointEstimator base M radius
        (stageCount (n:ℝ)) false).policy z.1) z.2) (paid (stageCount (n:ℝ))) := by
    rw [history_pad hk]
    apply history_of_prefix
    exact prefix_of_agree _ (fun xs hx => limitPolicy_agree base z.1 _ xs hx) z.2
  unfold onlineInterval ThresholdHC.Anytime.observedInterval
  dsimp only
  rw [hh]
  rfl

/-- Law transfer: if the stage family covers on one event of probability at
least `1-δ` under its stream law and its intervals obey a pathwise width
envelope, the limit policy has joint coverage and width control in the
original experiment. -/
theorem online_coverage (μ : Measure Gap) [IsProbabilityMeasure μ]
    (base : ∀ j, AdaptiveEstimator (R j)) (M : ℝ) (radius : ℕ → ℝ) (ρ : ℝ) {δ : ℝ}
    (hd : 0 ≤ δ) (t : ℕ → ℝ)
    (hcov : ∀ q : SignLaw, RarePrior μ ρ q →
      (ThresholdHC.Anytime.streamLaw μ base q) {z | ∃ k, ¬ (
        (ThresholdHC.Anytime.observedInterval base M radius k z).1 ≤ signMean μ q.val ∧
        signMean μ q.val ≤ (ThresholdHC.Anytime.observedInterval base M radius k z).2)} ≤
        ENNReal.ofReal δ)
    (hwidth : ∀ (n : ℕ) (z : (∀ j, R j) × Table),
      (ThresholdHC.Anytime.observedInterval base M radius (stageCount (n:ℝ)) z).2 -
        (ThresholdHC.Anytime.observedInterval base M radius (stageCount (n:ℝ)) z).1 ≤ 2*t n) :
    OnlineIntervalCoverage μ (limitEstimator base)
      (fun n y => (onlineInterval base M radius n y).1)
      (fun n y => (onlineInterval base M radius n y).2) ρ δ t := by
  intro q hq
  let θ := signMean μ q.val
  let S : Set ((∀ j, R j) × ProcessTape) := {y | ∀ n,
    (onlineInterval base M radius n (y.1,processPrefix n y.2)).1 ≤ θ ∧
    θ ≤ (onlineInterval base M radius n (y.1,processPrefix n y.2)).2 ∧
    (onlineInterval base M radius n (y.1,processPrefix n y.2)).2 -
      (onlineInterval base M radius n (y.1,processPrefix n y.2)).1 ≤ 2*t n}
  have hproj (n : ℕ) : Measurable (fun y : (∀ j, R j) × ProcessTape =>
      (y.1,processPrefix n y.2)) :=
    measurable_fst.prodMk
      (measurable_pi_iff.mpr fun i => (measurable_pi_apply i.val).comp measurable_snd)
  have hS : MeasurableSet S := by
    simp only [S,Set.ofPred_forall]
    refine MeasurableSet.iInter fun n => ?_
    have hL := (measurable_onlineInterval base M radius n).fst.comp (hproj n)
    have hU := (measurable_onlineInterval base M radius n).snd.comp (hproj n)
    exact (measurableSet_le hL measurable_const).inter
      ((measurableSet_le measurable_const hU).inter (measurableSet_le (hU.sub hL) measurable_const))
  have hg : Measurable (fun x : PopulationSeed (∀ j, R j) × ProcessTape => (x.1.1,x.2)) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hh : Measurable (fun z : (∀ j, R j) × Table =>
      (z.1,populationPath ((limitEstimator base).policy z.1) z.2)) :=
    measurable_fst.prodMk (measurable_seeded_populationPath (limitEstimator base).policy
      (fun xs => measurable_to_countable' ((limitEstimator base).policy_measurable xs)))
  have hlaw : originalSimulationLaw μ (limitEstimator base) q =
      ThresholdHC.Anytime.streamLaw μ base q := rfl
  let E := (fun z : (∀ j, R j) × Table =>
    (z.1,populationPath ((limitEstimator base).policy z.1) z.2)) ⁻¹' S
  have hE : MeasurableSet E := hh hS
  have hmeas : (experimentLaw μ (limitEstimator base) q) ((fun x => (x.1.1,x.2)) ⁻¹' S) =
      (ThresholdHC.Anytime.streamLaw μ base q) E := by
    rw [← Measure.map_apply hg hS,original_observable_simulation_law,Measure.map_apply hh hS,
      hlaw]
  have hsub : Eᶜ ⊆ {z | ∃ k, ¬ (
      (ThresholdHC.Anytime.observedInterval base M radius k z).1 ≤ θ ∧
      θ ≤ (ThresholdHC.Anytime.observedInterval base M radius k z).2)} := by
    intro z hz
    by_contra hall
    simp only [Set.mem_ofPred_eq,not_exists,not_not] at hall
    apply hz
    intro n
    have hr := onlineInterval_readback base M radius n z
    show (onlineInterval base M radius n
        (z.1,processPrefix n (populationPath ((limitEstimator base).policy z.1) z.2))).1 ≤ θ ∧
      θ ≤ (onlineInterval base M radius n
        (z.1,processPrefix n (populationPath ((limitEstimator base).policy z.1) z.2))).2 ∧
      (onlineInterval base M radius n
        (z.1,processPrefix n (populationPath ((limitEstimator base).policy z.1) z.2))).2 -
      (onlineInterval base M radius n
        (z.1,processPrefix n (populationPath ((limitEstimator base).policy z.1) z.2))).1 ≤ 2*t n
    rw [hr]
    exact ⟨(hall _).1,(hall _).2,hwidth n z⟩
  have hc : (ThresholdHC.Anytime.streamLaw μ base q).real Eᶜ ≤ δ :=
    ENNReal.toReal_le_of_le_ofReal hd ((measure_mono hsub).trans (hcov q hq))
  have hcompl := probReal_compl_eq_one_sub (μ := ThresholdHC.Anytime.streamLaw μ base q) hE
  change 1-δ ≤
    ((experimentLaw μ (limitEstimator base) q) ((fun x => (x.1.1,x.2)) ⁻¹' S)).toReal
  rw [hmeas]
  change 1-δ ≤ (ThresholdHC.Anytime.streamLaw μ base q).real E
  linarith

end ThresholdHC.TimeUniformTwoSided
