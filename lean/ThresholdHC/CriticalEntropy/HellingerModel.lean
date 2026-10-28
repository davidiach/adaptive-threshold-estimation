import Mathlib

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.CriticalEntropy

/-- Hellinger affinity of the actual measures, using their sum as the
dominating measure. For probability measures the normalization is in [0,1]. -/
def hellingerAffinity {Ω : Type} [MeasurableSpace Ω] (P Q : Measure Ω) : ℝ≥0∞ :=
  ∫⁻ z, (P.rnDeriv (P+Q) z * Q.rnDeriv (P+Q) z) ^ (1/2 : ℝ) ∂(P+Q)

def finiteAffinity {I : Type} [Fintype I] (p q : I → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ i, (p i*q i) ^ (1/2 : ℝ)

end ThresholdHC.CriticalEntropy
