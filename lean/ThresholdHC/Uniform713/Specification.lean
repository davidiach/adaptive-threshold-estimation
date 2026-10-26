import ThresholdHC.Uniform713.Concentration
import ThresholdHC.Uniform713.Classifier
import ThresholdHC.Uniform713.Estimator

/-!
The target for the complete 713 theorem. Its assumptions describe the observation
model only: independent bounded observations of mean 1/2 ± d, an arbitrary law
of magnitudes and signs, and an integrable inverse magnitude. In particular, no
classifier error, work, estimator moment, or unbiasedness bound is assumed.

The [0,1]-valued formulation includes the intended Bernoulli model.
-/

noncomputable section

namespace ThresholdHC.Uniform713

open MeasureTheory ProbabilityTheory

def signValue (s : Bool) : ℝ := if s then 1 else 0

def coinMean (d : ℝ) (s : Bool) : ℝ := if s then 1 / 2 + d else 1 / 2 - d

def decisions {Ω : Type*} (X : ℕ → Ω → ℝ) (l : ℕ) (ω : Ω) : ℝ :=
  decision (fun k => dyadicMean X k ω) l

def levelWork {Ω : Type*} (X : ℕ → Ω → ℝ) (l : ℕ) (ω : Ω) : ℝ :=
  work (fun k => dyadicMean X k ω) l

def samplingKernel {Θ Ω : Type*} [MeasurableSpace Θ] [MeasurableSpace Ω]
    (κ : Kernel Θ Ω) : Kernel Θ (ℕ × Ω) := (Kernel.const Θ levelMeasure) ×ₖ κ

instance samplingKernel_markov {Θ Ω : Type*} [MeasurableSpace Θ] [MeasurableSpace Ω]
    (κ : Kernel Θ Ω) [IsMarkovKernel κ] : IsMarkovKernel (samplingKernel κ) := by
  unfold samplingKernel
  infer_instance

theorem samplingKernel_apply {Θ Ω : Type*} [MeasurableSpace Θ] [MeasurableSpace Ω]
    (κ : Kernel Θ Ω) [IsMarkovKernel κ] (θ : Θ) :
    samplingKernel κ θ = samplingMeasure (κ θ) := by
  simp [samplingKernel, Kernel.prod_apply, samplingMeasure]

def mixtureLaw {Θ Ω : Type*} [MeasurableSpace Θ] [MeasurableSpace Ω]
    (ν : Measure Θ) (κ : Kernel Θ Ω) : Measure (Θ × (ℕ × Ω)) := ν ⊗ₘ samplingKernel κ

def uniformEstimator {Θ Ω : Type*} (X : ℕ → Ω → ℝ) (x : Θ × (ℕ × Ω)) : ℝ :=
  estimator (decisions X) x.2

def uniformWork {Θ Ω : Type*} (X : ℕ → Ω → ℝ) (x : Θ × (ℕ × Ω)) : ℝ :=
  sampled (levelWork X) x.2

/-- Natural conditional observation assumptions; no conclusion of the theorem is a field. -/
structure ObservationModel {Θ Ω : Type*} [MeasurableSpace Θ] [MeasurableSpace Ω]
    (ν : Measure Θ) (κ : Kernel Θ Ω) (X : ℕ → Ω → ℝ) (d : Θ → ℝ) (s : Θ → Bool) : Prop where
  measurable_observations : ∀ i, Measurable (X i)
  measurable_magnitude : Measurable d
  measurable_sign : Measurable s
  magnitude_range : ∀ᵐ θ ∂ν, 0 < d θ ∧ d θ ≤ 1 / 2
  bounded : ∀ᵐ θ ∂ν, ∀ i, ∀ᵐ ω ∂κ θ, X i ω ∈ Set.Icc (0 : ℝ) 1
  mean : ∀ᵐ θ ∂ν, ∀ i, ∫ ω, X i ω ∂κ θ = coinMean (d θ) (s θ)
  independent : ∀ᵐ θ ∂ν, iIndepFun X (κ θ)
  inverse_integrable : Integrable (fun θ => (d θ)⁻¹) ν

/-- Exact target for the full, untruncated, arbitrary-magnitude-law result. -/
def FullBound713Statement : Prop :=
  ∀ (Θ Ω : Type) [MeasurableSpace Θ] [MeasurableSpace Ω]
    (ν : Measure Θ) [IsProbabilityMeasure ν] (κ : Kernel Θ Ω) [IsMarkovKernel κ]
    (X : ℕ → Ω → ℝ) (d : Θ → ℝ) (s : Θ → Bool),
    ObservationModel ν κ X d s →
    MemLp (@uniformEstimator Θ Ω X) 2 (mixtureLaw ν κ) ∧
    Integrable (@uniformWork Θ Ω X) (mixtureLaw ν κ) ∧
    (∫ x, uniformEstimator X x ∂mixtureLaw ν κ) = (∫ θ, signValue (s θ) ∂ν) ∧
    ProbabilityTheory.variance (@uniformEstimator Θ Ω X) (mixtureLaw ν κ) *
      (∫ x, uniformWork X x ∂mixtureLaw ν κ) <
      713 * (∫ θ, (d θ)⁻¹ ∂ν) ^ 2

end ThresholdHC.Uniform713
