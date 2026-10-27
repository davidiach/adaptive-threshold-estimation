import ThresholdHC.CriticalEntropy.HellingerModel

noncomputable section
open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace Topology
namespace ThresholdHC.CriticalEntropy

def realFiniteAffinity {I : Type} [Fintype I] (p q : I → ℝ) : ℝ :=
  ∑ i, Real.sqrt (p i*q i)

end ThresholdHC.CriticalEntropy
