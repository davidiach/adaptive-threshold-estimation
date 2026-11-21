import ThresholdHC.DepthObstruction.Specification
import ThresholdHC.CapIdentification.StoppedMatching
import ThresholdHC.CriticalEntropy.PopulationLocalWork

/-! One coin of the unchanged population experiment. The probability that its
first `N` flips form a given word is the integrated word likelihood, so matching
odd moments through depth `N` give the same law of the first `N` flips. -/

noncomputable section
namespace ThresholdHC.DepthObstruction
open MeasureTheory
open scoped ENNReal
open ThresholdHC.Tier6 (Gap SignLaw)
open ThresholdHC.CriticalEntropy ThresholdHC.ObservableSimulation ThresholdHC.CapIdentification

/-- The one-coin procedure that reads exactly `N` flips and reports nothing. -/
def readPrefix (N : ℕ) : StoppedProcedure Unit Unit where
  stop := fun _ => (N : ℕ∞)
  output := fun _ => ()
  measurable_stop := measurable_const
  measurable_output := measurable_const
  stopPrefix := fun n => {_z | n = N}
  measurable_stopPrefix := fun n => by
    by_cases h : n = N
    · simp only [h, Set.ofPred_true, MeasurableSet.univ]
    · simp only [h, Set.ofPred_false, MeasurableSet.empty]
  stop_observable := fun n z => by
    change n = N ↔ (N : ℕ∞) = (n : ℕ∞)
    rw [Nat.cast_inj, eq_comm]
  outputPrefix := fun _ _ => ()
  measurable_outputPrefix := fun _ => measurable_const
  output_observable := fun _ _ _ => rfl

theorem wordHeads_le {n : ℕ} (x : Fin n → Bool) : wordHeads x ≤ n := by
  unfold wordHeads
  simpa only [Finset.card_univ, Fintype.card_fin] using
    Finset.card_filter_le (s := Finset.univ) (fun i => x i = true)

/-- The probability of a word of the first `N` flips of one population coin. -/
theorem originalTape_prefix_measure (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (N : ℕ) (x : Fin N → Bool) :
    originalPopulationTapeLaw μ q {ω | Tier2.tapePrefix N ω = x} =
      populationWordLikelihood μ (gapParameter false) (gapParameter true) (signUnit q) N
        (wordHeads x) := by
  have hpres := populationInput_preserving (R := Unit) μ (Measure.dirac ())
    (gapParameter false) (gapParameter true) (signUnit q) (measurable_gapParameter false)
    (measurable_gapParameter true) (measurable_signUnit q)
  have hS : MeasurableSet {z : Unit × (ℕ → Bool) |
      z.1 ∈ (Set.univ : Set Unit) ∧ (readPrefix N).stop z = N ∧ Tier2.tapePrefix N z.2 = x} :=
    (measurable_fst MeasurableSet.univ).inter
      (((readPrefix N).measurable_stop (measurableSet_singleton (N : ℕ∞))).inter
        (((Tier2.measurable_prefix N).comp measurable_snd) (measurableSet_singleton x)))
  have h1 := hpres.measure_preimage hS.nullMeasurableSet
  have h2 := population_stopped_word_probability μ (Measure.dirac ())
    (gapParameter false) (gapParameter true) (signUnit q) (measurable_gapParameter false)
    (measurable_gapParameter true) (measurable_signUnit q) (readPrefix N) x Set.univ
    MeasurableSet.univ
  have hset : {z : Unit × (ℕ → Bool) |
      z.1 ∈ (Set.univ : Set Unit) ∧ (readPrefix N).stop z = N ∧ Tier2.tapePrefix N z.2 = x} =
      Set.univ ×ˢ {ω | Tier2.tapePrefix N ω = x} := by
    ext z
    simp [readPrefix]
  have hcell : stoppedSeedCell (readPrefix N) x Set.univ = Set.univ := by
    ext r
    simp [stoppedSeedCell, readPrefix]
  have : IsProbabilityMeasure (parameterTapeLaw (populationParameterLaw μ (gapParameter false)
      (gapParameter true) (signUnit q))) := originalPopulationTapeLaw_probability μ q
  rw [h1, hset, Measure.prod_prod, hcell] at h2
  simp only [measure_univ, one_mul] at h2
  exact h2

/-- Matching odd moments through depth `N` give the same law of the first `N`
flips of one population coin. -/
theorem originalTape_prefix_law_eq (μ : Measure Gap) [IsProbabilityMeasure μ]
    (qH qL : SignLaw) (N : ℕ) (h : OddMomentMatch μ qH qL N) :
    (originalPopulationTapeLaw μ qH).map (Tier2.tapePrefix N) =
      (originalPopulationTapeLaw μ qL).map (Tier2.tapePrefix N) := by
  apply Measure.ext_of_singleton
  intro x
  rw [Measure.map_apply (Tier2.measurable_prefix N) (measurableSet_singleton x),
    Measure.map_apply (Tier2.measurable_prefix N) (measurableSet_singleton x)]
  change originalPopulationTapeLaw μ qH {ω | Tier2.tapePrefix N ω = x} =
    originalPopulationTapeLaw μ qL {ω | Tier2.tapePrefix N ω = x}
  rw [originalTape_prefix_measure, originalTape_prefix_measure]
  exact wordLikelihood_eq_of_count_match μ qH qL N
    ((odd_moments_iff_count_match μ qH qL N).mp h) N (wordHeads x) le_rfl (wordHeads_le x)

/-- The same law of the first `N` flips, completed by `false`. -/
theorem originalTape_completed_law_eq (μ : Measure Gap) [IsProbabilityMeasure μ]
    (qH qL : SignLaw) (N : ℕ) (h : OddMomentMatch μ qH qL N) :
    (originalPopulationTapeLaw μ qH).map (fun ω => completePrefix N (Tier2.tapePrefix N ω)) =
      (originalPopulationTapeLaw μ qL).map (fun ω => completePrefix N (Tier2.tapePrefix N ω)) := by
  have hc := measurable_completePrefix N
  have hp := Tier2.measurable_prefix N
  change (originalPopulationTapeLaw μ qH).map (completePrefix N ∘ Tier2.tapePrefix N) =
    (originalPopulationTapeLaw μ qL).map (completePrefix N ∘ Tier2.tapePrefix N)
  rw [← Measure.map_map hc hp, ← Measure.map_map hc hp, originalTape_prefix_law_eq μ qH qL N h]

end ThresholdHC.DepthObstruction
