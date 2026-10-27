import Mathlib

noncomputable section
open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace Topology
namespace ThresholdHC.CriticalEntropy

abbrev PopulationDual {D : Type} [MeasurableSpace D] (μ : Measure D) :=
  WeakDual ℝ (Lp ℝ 2 μ)

def populationDualSet {D : Type} [MeasurableSpace D]
    (μ : Measure D) [IsProbabilityMeasure μ] (ρ : ℝ) : Set (PopulationDual μ) :=
  (WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 1) ∩
    {f | ∀ (S : Set D) (hS : MeasurableSet S),
      f (indicatorConstLp 2 hS (measure_ne_top μ S) (1 : ℝ)) ∈ Icc 0 (μ.real S/2)} ∩
    {f | f (Lp.const 2 μ (1 : ℝ)) ≤ ρ}

def populationDualDensity {D : Type} [MeasurableSpace D] (μ : Measure D)
    (f : PopulationDual μ) : Lp ℝ 2 μ :=
  (InnerProductSpace.toDual ℝ (Lp ℝ 2 μ)).symm f.toStrongDual

def populationDualPrior {D : Type} [MeasurableSpace D] (μ : Measure D)
    (f : PopulationDual μ) (d : D) : unitInterval :=
  ⟨max 0 (min (populationDualDensity μ f d) (1/2)), le_max_left _ _,
    le_trans (max_le (by norm_num) (min_le_right _ _)) (by norm_num)⟩

def populationMomentMap {D I : Type} [MeasurableSpace D]
    (μ : Measure D) (g : I → Lp ℝ 2 μ) (b : I → ℝ) : PopulationDual μ →ᵃ[ℝ] (I → ℝ) :=
  (LinearMap.pi (fun i => (ContinuousLinearMap.apply ℝ ℝ (g i)).toLinearMap.comp
    WeakDual.toStrongDual.toLinearMap)).toAffineMap + AffineMap.const ℝ (PopulationDual μ) b

def boundedPriorMomentSet {D I : Type} [MeasurableSpace D]
    (μ : Measure D) (ρ : ℝ) (g : I → Lp ℝ 2 μ) (b : I → ℝ) : Set (I → ℝ) :=
  {v | ∃ q : D → unitInterval, Measurable q ∧ (∀ d, (q d : ℝ) ≤ 1/2) ∧
    (∫ d, (q d : ℝ) ∂μ) ≤ ρ ∧ ∀ i, v i = (∫ d, (q d : ℝ)*g i d ∂μ)+b i}

def populationTarget {D : Type} [MeasurableSpace D]
    (μ : Measure D) [IsProbabilityMeasure μ] : PopulationDual μ →ₗ[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ (Lp.const 2 μ (1 : ℝ))).toLinearMap.comp
    WeakDual.toStrongDual.toLinearMap

def populationPairSet {D : Type} [MeasurableSpace D]
    (μ : Measure D) [IsProbabilityMeasure μ] (ρ δ : ℝ) :
    Set (PopulationDual μ × PopulationDual μ) :=
  (populationDualSet μ ρ ×ˢ populationDualSet μ ρ) ∩
    {z | δ ≤ populationTarget μ z.2-populationTarget μ z.1}

end ThresholdHC.CriticalEntropy
