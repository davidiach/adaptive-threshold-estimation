import ThresholdHC.RareAboveTwo.Model
import ThresholdHC.Tier6.Full
import ThresholdHC.CriticalEntropy.CriticalTerminalAffinity

noncomputable section
namespace ThresholdHC.RareAboveTwo
open MeasureTheory ProbabilityTheory Set Filter ThresholdHC.Tier3 ThresholdHC.Tier4
open ThresholdHC.Tier6 ThresholdHC.CriticalEntropy
open scoped ENNReal Topology

theorem observable_tape_measurable {R : Type} [MeasurableSpace R] (k : ℕ) (b : Option Bool) :
    MeasurableSet {z : PopulationSeed R × ProcessTape | z.2 k=b} :=
  measurableSet_eq_fun ((measurable_pi_apply k).comp measurable_snd) measurable_const

theorem observable_eventual_tape_reconstruction {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (q : SignLaw)
    (hfin : expectedWork μ A q < ∞) :
    ∀ᵐ z ∂experimentLaw μ A q, ∀ᶠ n in atTop, padPrefix n (processPrefix n z.2)=z.2 := by
  have hr := (population_realization R μ A q).2
  have hv : ∀ᵐ z ∂experimentLaw μ A q, ∀ k,
      (z.2 k).isSome=(A.policy z.1.1 (processHistory z.2 k)).isSome :=
    ae_all_iff.mpr (fun k => Tier5.realized_creation_valid_step
      (populationSeedLaw μ A) (experimentLaw μ A q) Prod.fst Prod.snd
      (populationPolicy A) populationGap (populationPrior q) measurable_fst
      observable_tape_measurable (measurable_populationPolicy A) hr k)
  have hstop := Tier5.creation_stops (PopulationSeed R) (PopulationSeed R × ProcessTape)
    (populationSeedLaw μ A) (experimentLaw μ A q) Prod.fst Prod.snd
    (populationPolicy A) populationGap (populationPrior q) measurable_fst
    observable_tape_measurable (measurable_populationPolicy A) hr hfin
  filter_upwards [hv,hstop] with z hz hstopz
  obtain ⟨N,hN⟩ := hstopz
  let pol : List Bool → Option (Fin 1) := fun xs => (A.policy z.1.1 xs).map (fun _ => 0)
  have hvflag (k) : (z.2 k).isSome=(pol (processHistory z.2 k)).isSome := by
    simpa only [pol,Option.isSome_map] using hz k
  have hNflag : pol (processHistory z.2 N)=none := by
    change A.policy z.1.1 (processHistory z.2 N)=none at hN
    simp [pol,hN]
  have htail := stopped_valid_tail pol z.2 hvflag N hNflag
  exact eventually_atTop.mpr ⟨N,fun n hn => padPrefix_eq_of_tail_none z.2 n
    (fun k hk => htail k (hn.trans hk))⟩

def observablePrefixLaw {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (q : SignLaw) (n : ℕ) :=
  (experimentLaw μ A q).map (fun z => (z.1.1,processPrefix n z.2))

def observableDecisionLaw {R I : Type} [MeasurableSpace R] [MeasurableSpace I]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (q : SignLaw)
    (f : R × ProcessTape → I) := (experimentLaw μ A q).map (fun z => f (z.1.1,z.2))

instance observablePrefixLaw_probability {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (q : SignLaw) (n : ℕ) :
    IsProbabilityMeasure (observablePrefixLaw μ A q n) := by
  unfold observablePrefixLaw
  infer_instance

theorem observable_terminal_affinity_bound {R I : Type} [MeasurableSpace R]
    [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (q r : SignLaw)
    (hworkq : expectedWork μ A q < ∞)
    (hworkr : expectedWork μ A r < ∞)
    (f : R × ProcessTape → I) (hf : Measurable f)
    (k b : ℝ) (hk : 0 ≤ k)
    (hprefix : ∀ n, (1-(hellingerAffinity (observablePrefixLaw μ A q n)
      (observablePrefixLaw μ A r n)).toReal)*k ≤ b) :
    (1-(hellingerAffinity (observableDecisionLaw μ A q f)
      (observableDecisionLaw μ A r f)).toReal)*k ≤ b := by
  let P := experimentLaw μ A q
  let Q := experimentLaw μ A r
  let g : ((R × (ℕ → Gap)) × ProcessTape) → I := fun z => f (z.1.1,z.2)
  let F : ℕ → ((R × (ℕ → Gap)) × ProcessTape) → I :=
    fun n z => f (z.1.1,padPrefix n (processPrefix n z.2))
  have hproj (n : ℕ) : Measurable
      (fun z : (R × (ℕ → Gap)) × ProcessTape => (z.1.1,processPrefix n z.2)) :=
    (measurable_fst.comp measurable_fst).prodMk
      (Measurable.of_eval (fun i : Fin n => (measurable_pi_apply i.val).comp measurable_snd))
  have hF (n) : Measurable (F n) := (hf.comp (measurable_padJoint n)).comp (hproj n)
  have hg : Measurable g := hf.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hp : ∀ᵐ z ∂P, ∀ᶠ n in atTop, F n z = g z := by
    filter_upwards [observable_eventual_tape_reconstruction μ A q hworkq] with z hz
    exact hz.mono (fun n hn => by simp only [F,g,hn])
  have hq' : ∀ᵐ z ∂Q, ∀ᶠ n in atTop, F n z = g z := by
    filter_upwards [observable_eventual_tape_reconstruction μ A r hworkr] with z hz
    exact hz.mono (fun n hn => by simp only [F,g,hn])
  have hbound (n : ℕ) :
      (1-(hellingerAffinity (P.map (F n)) (Q.map (F n))).toReal)*k ≤ b := by
    let u : R × Prefix n → I := f ∘ padJoint n
    have hu : Measurable u := hf.comp (measurable_padJoint n)
    have hdp := hellingerAffinity_map_finite (observablePrefixLaw μ A q n)
      (observablePrefixLaw μ A r n) u hu
    have hm (s : SignLaw) :
        (observablePrefixLaw μ A s n).map u =
          (experimentLaw μ A s).map (F n) := by
      rw [observablePrefixLaw,Measure.map_map hu (hproj n)]
      rfl
    rw [hm q,hm r] at hdp
    let : IsProbabilityMeasure (P.map (F n)) := inferInstance
    let : IsProbabilityMeasure (Q.map (F n)) := inferInstance
    have hfinite : hellingerAffinity (P.map (F n)) (Q.map (F n)) ≠ ∞ :=
      ne_of_lt ((hellingerAffinity_probability_le_one _ _).trans_lt (by simp))
    have hdr := ENNReal.toReal_mono hfinite hdp
    exact (mul_le_mul_of_nonneg_right (sub_le_sub_left hdr 1) hk).trans (hprefix n)
  have hlim := hellingerAffinity_tendsto_eventual_maps P Q F g hF hg hp hq'
  exact le_of_tendsto ((tendsto_const_nhds.sub hlim).mul tendsto_const_nhds)
    (Eventually.of_forall hbound)


end ThresholdHC.RareAboveTwo
