import ThresholdHC.CriticalEntropy.HellingerModel

noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal NNReal
namespace ThresholdHC.ConfidenceTransfer

/-- One endpoint after mixing the two input laws with weights 3/4 and 1/4. -/
def quarterMix {Ω : Type*} [MeasurableSpace Ω] (P Q : Measure Ω) : Measure Ω :=
  (3/4 : ℝ≥0) • P + (1/4 : ℝ≥0) • Q

/-- Lemma 1 uses the project's existing Hellinger normalization on the original pair. -/
def QuarterSmoothingStatement : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P Q : Measure Ω) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q],
    max (klDiv (quarterMix P Q) (quarterMix Q P)) (klDiv (quarterMix Q P) (quarterMix P Q)) ≤
      ENNReal.ofReal ((8/3) * (1 - (CriticalEntropy.hellingerAffinity P Q).toReal))

end ThresholdHC.ConfidenceTransfer
