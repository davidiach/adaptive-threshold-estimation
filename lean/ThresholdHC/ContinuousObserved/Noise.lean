import ThresholdHC.ObservedState.Garbling
import ThresholdHC.CriticalEntropy.UniformCoin

noncomputable section
open MeasureTheory ProbabilityTheory
namespace ThresholdHC.ContinuousObserved
open ThresholdHC.Tier6 ThresholdHC.ObservableSimulation ThresholdHC.ObservedState
open ThresholdHC.CriticalEntropy

theorem measurable_noiseRate {U : Type} [MeasurableSpace U]
    (cap gap : U → Gap) (hc : Measurable cap) (hg : Measurable gap)
    (hb : ∀ u, (gap u : ℝ) ≤ cap u) :
    Measurable (fun u => noiseRate (cap u) (gap u) (hb u)) := by
  apply Measurable.subtype_mk
  exact (measurable_const.sub ((measurable_subtype_coe.comp hg).div
    (measurable_subtype_coe.comp hc))).div_const 2

/-- One larger-gap observation and one independent uniform value give
exactly the required smaller-gap observation for either fixed sign. -/
theorem uniform_garbling_law (b d : Gap) (hd : (d : ℝ) ≤ b) (s : Bool) :
    ((bernoulliMeasure true false (gapParameter s b)).prod uniformUnitMeasure).map
      (fun z => Bool.xor z.1 (uniformCoinFlip (noiseRate b d hd) z.2)) =
        bernoulliMeasure true false (gapParameter s d) := by
  let f := uniformCoinFlip (noiseRate b d hd)
  have hf : Measurable f :=
    measurable_uniformCoinFlip.comp (measurable_const.prodMk measurable_id)
  have hm : Measurable (Prod.map (id : Bool → Bool) f) := measurable_id.prodMap hf
  have hx : Measurable (fun z : Bool × Bool => Bool.xor z.1 z.2) := measurable_of_countable _
  calc
    _ = (((bernoulliMeasure true false (gapParameter s b)).prod uniformUnitMeasure).map
      (Prod.map id f)).map (fun z => Bool.xor z.1 z.2) := (Measure.map_map hx hm).symm
    _ = ((bernoulliMeasure true false (gapParameter s b)).prod
      (bernoulliMeasure true false (noiseRate b d hd))).map (fun z => Bool.xor z.1 z.2) := by
        rw [← Measure.map_prod_map _ _ measurable_id hf,Measure.map_id]
        rw [show uniformUnitMeasure.map f = _ from uniformCoinFlip_map (noiseRate b d hd)]
    _ = _ := garbling_law b d hd s

end ThresholdHC.ContinuousObserved
