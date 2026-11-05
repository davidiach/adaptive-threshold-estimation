import ThresholdHC.ContinuousObserved.UniformTape
import ThresholdHC.ContinuousObserved.Noise
import ThresholdHC.BlindUpper.SeedInput

noncomputable section
open MeasureTheory ProbabilityTheory
namespace ThresholdHC.ContinuousObserved
open ThresholdHC ThresholdHC.Tier6 ThresholdHC.CriticalEntropy ThresholdHC.BlindUpper
open ThresholdHC.ObservableSimulation ThresholdHC.ObservedState

/-- Extract a fixed cell's next raw observation and the next noise value.
All unused randomness retains its original independent product law. -/
theorem fresh_pair_preserving {N : ℕ} (p : Fin N → unitInterval) (j : Fin N) :
    MeasurePreserving
      (fun z : (ℕ → ℝ) × (Fin N → ℕ → Bool) =>
        ((z.2 j 0,z.1 0),(uniformTail z.1,Function.update z.2 j (tapeDrop 1 (z.2 j)))))
      (uniformTapeMeasure.prod (Measure.pi (fun i => Tier2.tapeMeasure (p i))))
      (((bernoulliMeasure true false (p j)).prod uniformUnitMeasure).prod
        (uniformTapeMeasure.prod (Measure.pi (fun i => Tier2.tapeMeasure (p i))))) := by
  let noiseLaw := uniformUnitMeasure
  let noiseTapeLaw := uniformTapeMeasure
  let coinLaw := bernoulliMeasure true false (p j)
  let arrayLaw := Measure.pi (fun i => Tier2.tapeMeasure (p i))
  have hs := uniform_head_tail_preserving.prod (array_head_drop_preserving p j)
  have ha := measurePreserving_prodAssoc noiseLaw noiseTapeLaw (coinLaw.prod arrayLaw)
  have hb := (MeasurePreserving.id noiseLaw).prod (measurePreserving_prodAssoc noiseTapeLaw coinLaw arrayLaw).symm
  have hc := (MeasurePreserving.id noiseLaw).prod
    ((Measure.measurePreserving_swap (μ := noiseTapeLaw) (ν := coinLaw)).prod (MeasurePreserving.id arrayLaw))
  have hd := (MeasurePreserving.id noiseLaw).prod (measurePreserving_prodAssoc coinLaw noiseTapeLaw arrayLaw)
  have he := (measurePreserving_prodAssoc noiseLaw coinLaw (noiseTapeLaw.prod arrayLaw)).symm
  have hf := (Measure.measurePreserving_swap (μ := noiseLaw) (ν := coinLaw)).prod
    (MeasurePreserving.id (noiseTapeLaw.prod arrayLaw))
  exact hf.comp (he.comp (hd.comp (hc.comp (hb.comp (ha.comp hs)))))

/-- At any fixed history, the transformed observation has the requested
Bernoulli parameter and is independent of all remaining randomness. -/
theorem fresh_observation_preserving {N : ℕ} (cap : Fin N → Gap) (s : Fin N → Bool)
    (j : Fin N) (d : Gap) (hd : (d : ℝ) ≤ cap j) :
    MeasurePreserving
      (fun z : (ℕ → ℝ) × (Fin N → ℕ → Bool) =>
        (Bool.xor (z.2 j 0) (uniformCoinFlip (noiseRate (cap j) d hd) (z.1 0)),
          (uniformTail z.1,Function.update z.2 j (tapeDrop 1 (z.2 j)))))
      (uniformTapeMeasure.prod (Measure.pi (fun i => Tier2.tapeMeasure (gapParameter (s i) (cap i)))))
      ((bernoulliMeasure true false (gapParameter (s j) d)).prod
        (uniformTapeMeasure.prod (Measure.pi (fun i => Tier2.tapeMeasure (gapParameter (s i) (cap i)))))) := by
  have hn : MeasurePreserving
      (fun z : Bool × ℝ => Bool.xor z.1 (uniformCoinFlip (noiseRate (cap j) d hd) z.2))
      ((bernoulliMeasure true false (gapParameter (s j) (cap j))).prod uniformUnitMeasure)
      (bernoulliMeasure true false (gapParameter (s j) d)) := by
    refine ⟨?_,uniform_garbling_law (cap j) d hd (s j)⟩
    exact (measurable_of_countable (fun z : Bool × Bool => Bool.xor z.1 z.2)).comp
      (measurable_fst.prodMk (measurable_uniformCoinFlip.comp (measurable_const.prodMk measurable_snd)))
  exact (hn.prod (MeasurePreserving.id _)).comp
    (fresh_pair_preserving (fun i => gapParameter (s i) (cap i)) j)

end ThresholdHC.ContinuousObserved
