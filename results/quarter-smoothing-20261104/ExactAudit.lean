import ThresholdHC.ConfidenceTransfer.Quarter
open MeasureTheory InformationTheory ThresholdHC.ConfidenceTransfer
open scoped NNReal ENNReal
example : QuarterSmoothingStatement := quarter_smoothing_both
example {Ω : Type} [MeasurableSpace Ω] (P Q : Measure Ω) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] :
    let A := (3/4 : ℝ≥0) • P + (1/4 : ℝ≥0) • Q
    let C := (1/4 : ℝ≥0) • P + (3/4 : ℝ≥0) • Q
    max (klDiv A C) (klDiv C A) ≤ ENNReal.ofReal
      ((8/3) * (1 - (ThresholdHC.CriticalEntropy.hellingerAffinity P Q).toReal)) := by
  simpa only [quarterMix, add_comm ((3/4 : ℝ≥0) • Q)] using
    (quarter_smoothing_both P Q)
#print axioms ThresholdHC.ConfidenceTransfer.QuarterSmoothingStatement
#print axioms ThresholdHC.ConfidenceTransfer.quarterMix
#print axioms ThresholdHC.ConfidenceTransfer.quarter_kl_density
#print axioms ThresholdHC.ConfidenceTransfer.quarter_smoothing
#print axioms ThresholdHC.ConfidenceTransfer.quarter_smoothing_both
