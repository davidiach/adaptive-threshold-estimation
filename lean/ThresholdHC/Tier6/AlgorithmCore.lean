import ThresholdHC.Tier6.HardPairModel
import ThresholdHC.Tier6.TestingModel
import Mathlib.Probability.ProductMeasure

/-!
Algorithms observe their common random seed and previous coin outcomes. Fresh
coin magnitudes are independent draws from an arbitrary probability law. The
algorithm does not observe that hidden environment. Its policy may choose any
natural-number label, revisit labels, interleave observations, or stop.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.Tier6
open ThresholdHC.Tier3 ThresholdHC.Tier5

abbrev SignLaw := {q : Gap → ℝ // Measurable q ∧ ∀ d, 0 ≤ q d ∧ q d ≤ 1}

structure AdaptiveEstimator (R : Type) [MeasurableSpace R] where
  randomLaw : Measure R
  probability : IsProbabilityMeasure randomLaw
  policy : R → List Bool → Option ℕ
  policy_measurable : MeasurableCreationPolicy policy
  output : R × ProcessTape → ℝ
  output_measurable : Measurable output

instance estimatorRandomLaw_probability {R : Type} [MeasurableSpace R]
    (A : AdaptiveEstimator R) : IsProbabilityMeasure A.randomLaw := A.probability

abbrev PopulationSeed (R : Type) := R × (ℕ → Gap)

def populationSeedLaw {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) :
    Measure (PopulationSeed R) := A.randomLaw.prod (Measure.infinitePi (fun _ : ℕ => μ))

instance populationSeedLaw_probability {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) :
    IsProbabilityMeasure (populationSeedLaw μ A) := by
  unfold populationSeedLaw
  infer_instance

def populationPolicy {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R)
    (u : PopulationSeed R) : List Bool → Option ℕ := A.policy u.1

def populationGap {R : Type} (u : PopulationSeed R) (i : ℕ) : ℝ := u.2 i

def populationPrior {R : Type} (q : SignLaw) (u : PopulationSeed R) (i : ℕ) : ℝ :=
  q.val (u.2 i)

def populationOutput {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R)
    (z : PopulationSeed R × ProcessTape) : ℝ := A.output (z.1.1, z.2)

theorem measurable_populationPolicy {R : Type} [MeasurableSpace R]
    (A : AdaptiveEstimator R) : MeasurableCreationPolicy (populationPolicy A) := by
  intro xs a
  exact measurable_fst (A.policy_measurable xs a)

theorem measurable_populationGap {R : Type} [MeasurableSpace R] :
    MeasurableEnvironment (populationGap (R := R)) := by
  intro i
  exact measurable_subtype_coe.comp ((measurable_pi_apply i).comp measurable_snd)

theorem measurable_populationPrior {R : Type} [MeasurableSpace R] (q : SignLaw) :
    MeasurableEnvironment (populationPrior (R := R) q) := by
  intro i
  exact q.property.1.comp ((measurable_pi_apply i).comp measurable_snd)

theorem populationGap_range {R : Type} (u : PopulationSeed R) (i : ℕ) :
    0 ≤ populationGap u i ∧ populationGap u i ≤ 1/2 :=
  ⟨(u.2 i).property.1.le, (u.2 i).property.2⟩

theorem populationPrior_range {R : Type} (q : SignLaw) (u : PopulationSeed R) (i : ℕ) :
    0 ≤ populationPrior q u i ∧ populationPrior q u i ≤ 1 := q.property.2 (u.2 i)

theorem measurable_populationOutput {R : Type} [MeasurableSpace R]
    (A : AdaptiveEstimator R) : Measurable (populationOutput A) :=
  A.output_measurable.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)

def rootMeanRisk {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (f : Ω → ℝ) (a : ℝ) : ℝ≥0∞ := squaredRisk P f a ^ (1/2 : ℝ)

end ThresholdHC.Tier6
