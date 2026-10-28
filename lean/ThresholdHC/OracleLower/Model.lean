import ThresholdHC.Tier6.AlgorithmModel
import ThresholdHC.Confidence.Model

/-!
Magnitude oracles. A general oracle has a common random seed containing a
coordinate-measurable array of potential magnitudes, all visible to its policy
and output. The array need not be iid or have the target law. Signs are still
independent conditional on the seed, with prior q evaluated at each magnitude.
The target is the integral of q against a separate probability law mu.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.OracleLower
open ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.Tier6

structure OracleEstimator (R : Type) [MeasurableSpace R] where
  randomLaw : Measure R
  probability : IsProbabilityMeasure randomLaw
  gap : R → ℕ → Gap
  gap_measurable : ∀ i, Measurable (fun r => gap r i)
  policy : R → List Bool → Option ℕ
  policy_measurable : MeasurableCreationPolicy policy
  output : R × ProcessTape → ℝ
  output_measurable : Measurable output

instance oracleRandomLaw_probability {R : Type} [MeasurableSpace R]
    (A : OracleEstimator R) : IsProbabilityMeasure A.randomLaw := A.probability

def oracleLaw {R : Type} [MeasurableSpace R] (A : OracleEstimator R) (q : SignLaw) :
    Measure (R × ProcessTape) :=
  creationProcessLaw A.randomLaw A.policy (fun r i => A.gap r i) (fun r i => q.val (A.gap r i))
    A.policy_measurable (fun i => measurable_subtype_coe.comp (A.gap_measurable i))
    (fun i => q.property.1.comp (A.gap_measurable i))
    (fun r i => ⟨(A.gap r i).property.1.le,(A.gap r i).property.2⟩)
    (fun r i => q.property.2 (A.gap r i))

instance oracleLaw_probability {R : Type} [MeasurableSpace R]
    (A : OracleEstimator R) (q : SignLaw) : IsProbabilityMeasure (oracleLaw A q) := by
  let _ := A.probability
  exact creationProcessLaw_probability A.randomLaw A.policy
    (fun r i => A.gap r i) (fun r i => q.val (A.gap r i))
    A.policy_measurable (fun i => measurable_subtype_coe.comp (A.gap_measurable i))
    (fun i => q.property.1.comp (A.gap_measurable i))
    (fun r i => ⟨(A.gap r i).property.1.le,(A.gap r i).property.2⟩)
    (fun r i => q.property.2 (A.gap r i))

def oracleWork {R : Type} [MeasurableSpace R] (A : OracleEstimator R) (q : SignLaw) : ℝ≥0∞ :=
  ∫⁻ z, totalProcessWork z.2 ∂oracleLaw A q

def OracleBudget {R : Type} [MeasurableSpace R] (A : OracleEstimator R) (B : ℝ) : Prop :=
  ∀ q : SignLaw, oracleWork A q ≤ ENNReal.ofReal B

def oracleRisk {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) (A : OracleEstimator R) : ℝ≥0∞ :=
  ⨆ q : SignLaw, rootMeanRisk (oracleLaw A q) A.output (signMean μ q.val)

def OracleConfidence {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) (A : OracleEstimator R) (r δ : ℝ) : Prop :=
  ∀ q : SignLaw, (oracleLaw A q) {z | r < |A.output z-signMean μ q.val|} ≤ ENNReal.ofReal δ

/-! The revealed experiment grants the entire iid magnitude array for free.
This is at least as informative as revealing a magnitude only on creation. -/
structure RevealedEstimator (R : Type) [MeasurableSpace R] where
  randomLaw : Measure R
  probability : IsProbabilityMeasure randomLaw
  policy : PopulationSeed R → List Bool → Option ℕ
  policy_measurable : MeasurableCreationPolicy policy
  output : PopulationSeed R × ProcessTape → ℝ
  output_measurable : Measurable output

def revealedOracle {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : RevealedEstimator R) : OracleEstimator (PopulationSeed R) where
  randomLaw := A.randomLaw.prod (Measure.infinitePi (fun _ : ℕ => μ))
  probability := by let _ := A.probability; infer_instance
  gap := fun r i => r.2 i
  gap_measurable := fun i => (measurable_pi_apply i).comp measurable_snd
  policy := A.policy
  policy_measurable := A.policy_measurable
  output := A.output
  output_measurable := A.output_measurable

/-! In the selected experiment, none stops, some none creates a coin at the
chosen magnitude, and some (some j) revisits the coin born at observation j.
Legality requires that j names an earlier creation. A creation at a history
uses its encoded history as the canonical coin label. Thus choices may depend
on every previous flip, while a revisited coin retains its original gap. -/
instance selectedRequestMeasurableSpace : MeasurableSpace (Option (Option ℕ)) := ⊤

structure SelectedEstimator (R : Type) [MeasurableSpace R] where
  randomLaw : Measure R
  probability : IsProbabilityMeasure randomLaw
  request : R → List Bool → Option (Option ℕ)
  request_measurable : ∀ xs, Measurable (fun r => request r xs)
  newGap : R → List Bool → Gap
  newGap_measurable : ∀ xs, Measurable (fun r => newGap r xs)
  reuse_valid : ∀ r xs j, request r xs = some (some j) →
    j < xs.length ∧ request r (xs.take j) = some none
  output : R × ProcessTape → ℝ
  output_measurable : Measurable output

def selectedLabel (xs : List Bool) : Option (Option ℕ) → Option ℕ
  | none => none
  | some none => some (Encodable.encode xs)
  | some (some j) => some (Encodable.encode (xs.take j))

def selectedOracle {R : Type} [MeasurableSpace R]
    (A : SelectedEstimator R) : OracleEstimator R where
  randomLaw := A.randomLaw
  probability := A.probability
  gap := fun r i => A.newGap r ((Encodable.decode (α := List Bool) i).getD [])
  gap_measurable := fun _ => A.newGap_measurable _
  policy := fun r xs => selectedLabel xs (A.request r xs)
  policy_measurable := fun xs _ => measurableSet_eq_fun
    ((measurable_of_countable (selectedLabel xs)).comp (A.request_measurable xs)) measurable_const
  output := A.output
  output_measurable := A.output_measurable

def revealedMinimaxRisk (μ : Measure Gap) [IsProbabilityMeasure μ] (B : ℝ) : ℝ≥0∞ :=
  sInf {t | ∃ (R : Type) (_ : MeasurableSpace R) (A : RevealedEstimator R),
    OracleBudget (revealedOracle μ A) B ∧ t = oracleRisk μ (revealedOracle μ A)}

def selectedMinimaxRisk (μ : Measure Gap) (B : ℝ) : ℝ≥0∞ :=
  sInf {t | ∃ (R : Type) (_ : MeasurableSpace R) (A : SelectedEstimator R),
    OracleBudget (selectedOracle A) B ∧ t = oracleRisk μ (selectedOracle A)}

def revealedConfidenceRadius (μ : Measure Gap) [IsProbabilityMeasure μ] (B δ : ℝ) : ℝ≥0∞ :=
  sInf {t | ∃ (R : Type) (_ : MeasurableSpace R) (A : RevealedEstimator R) (r : ℝ),
    0 ≤ r ∧ OracleBudget (revealedOracle μ A) B ∧
    OracleConfidence μ (revealedOracle μ A) r δ ∧ t = ENNReal.ofReal r}

def selectedConfidenceRadius (μ : Measure Gap) (B δ : ℝ) : ℝ≥0∞ :=
  sInf {t | ∃ (R : Type) (_ : MeasurableSpace R) (A : SelectedEstimator R) (r : ℝ),
    0 ≤ r ∧ OracleBudget (selectedOracle A) B ∧
    OracleConfidence μ (selectedOracle A) r δ ∧ t = ENNReal.ofReal r}

end ThresholdHC.OracleLower
