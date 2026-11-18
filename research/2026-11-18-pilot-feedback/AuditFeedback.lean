import OrderedReduction
import OrderedPopulation

open MeasureTheory PilotFeedback
open scoped ENNReal
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.Tier6 ThresholdHC.SharpRMS
open ThresholdHC.SharpRMS.LargeBudget ThresholdHC.SharpRMS.Pilot

example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (r : Ω → Rule) (hm : ∀ i, Measurable fun z => ENNReal.ofReal (pointMSE (r z) i)) :
    ENNReal.ofReal ((18735887/100000000 : ℝ)^2) ≤
      ⨆ i : Fin 4, ∫⁻ z, ENNReal.ofReal (pointMSE (r z) i) ∂μ := worstFour_lower μ r hm

example {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (r : Ω → Rule) (hm : ∀ i, Measurable fun z => ENNReal.ofReal (pointMSE (r z) i)) :
    (⨆ q : SignLaw, squaredRisk (experimentLaw (Measure.dirac fifthGap) pilotEstimator q)
      (populationOutput pilotEstimator) (signMean (Measure.dirac fifthGap) q.val)) <
      ⨆ i : Fin 4, ∫⁻ z, ENNReal.ofReal (pointMSE (r z) i) ∂μ := strict_separation μ r hm

#print axioms PilotFeedback.all_rows
#print axioms PilotFeedback.worstFour_lower
#print axioms PilotFeedback.strict_separation

example (s : Ordered.Schedule) (p : ℝ) (hp : p ∈ Set.Icc 0 1) (X : List Bool → ℝ) :
    (∑ w : Prefix 25, Revisit.law (Ordered.policy s) p w * X (Proofs.fullHist w)) =
    ∑ g ∈ Ordered.support s, Ordered.groupedMass s p g * Ordered.uniformOrder s g X :=
  Ordered.ordered_reduction s p hp X

example (s : Ordered.Schedule) (p : ℝ) (hp : p ∈ Set.Icc 0 1)
    (g : Ordered.Counts) (hg : g ∈ Ordered.support s) :
    (∑ w : Prefix 25, Revisit.law (Ordered.policy s) p w *
      (if Ordered.counts s [] (Proofs.fullHist w) = g then (1:ℝ) else 0)) =
      Ordered.groupedMass s p g := Ordered.counts_marginal s p hp hg

example {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R)
    (hc : ∀ r, ∃ s : List Bool → ℕ → Option Bool, A.policy r = Ordered.policy s) :
    ENNReal.ofReal ((18735887/100000000 : ℝ)^2) ≤ Ordered.fourRisk A :=
  Ordered.original_lower A hc

example {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R)
    (hc : ∀ r, ∃ s : List Bool → ℕ → Option Bool, A.policy r = Ordered.policy s) :
    (⨆ q : SignLaw, squaredRisk (experimentLaw (Measure.dirac fifthGap) pilotEstimator q)
      (populationOutput pilotEstimator) (signMean (Measure.dirac fifthGap) q.val)) <
    ⨆ q : SignLaw, squaredRisk (experimentLaw (Measure.dirac fifthGap) A q)
      (populationOutput A) (signMean (Measure.dirac fifthGap) q.val) := Ordered.original_separation A hc

#print axioms PilotFeedback.Ordered.ordered_reduction
#print axioms PilotFeedback.Ordered.counts_marginal
#print axioms PilotFeedback.Ordered.original_lower
#print axioms PilotFeedback.Ordered.original_separation
