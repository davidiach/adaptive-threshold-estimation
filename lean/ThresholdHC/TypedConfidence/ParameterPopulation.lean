import ThresholdHC.ConfidenceTransfer.FiniteTransfer

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace ThresholdHC.TypedConfidence
open ThresholdHC ThresholdHC.Proofs ThresholdHC.Tier3 ThresholdHC.CriticalEntropy

local instance : MeasurableSpace (Option Bool) := ⊤
local instance : MeasurableSingletonClass (Option Bool) := ⟨fun _ => trivial⟩

/-- Each fixed label has its own parameter law. Choosing a new label
therefore permits adaptive choice of its component type. -/
def parameterWeight {m n : ℕ} (κ : Fin m → Measure unitInterval)
    (pol : List Bool → Option (Fin m)) (w : Prefix n) : ℝ :=
  ∫ p : Fin m → unitInterval, pathProb pol (fun i => (p i : ℝ)) w ∂Measure.pi κ

def parameterWordLaw {m : ℕ} (κ : Fin m → Measure unitInterval)
    (pol : List Bool → Option (Fin m)) (n : ℕ) : Measure (Prefix n) :=
  finiteWeightMeasure (parameterWeight κ pol)

def coinMass {m n : ℕ} (pol : List Bool → Option (Fin m))
    (w : Prefix n) (i : Fin m) (κ : Measure unitInterval) : ℝ :=
  ∫ p : unitInterval, coinLike pol w i p ∂κ

theorem parameter_word_law {m : ℕ} (κ : Fin m → Measure unitInterval)
    [∀ i, IsProbabilityMeasure (κ i)] (pol : List Bool → Option (Fin m)) (n : ℕ) :
    (Measure.pi (fun i => parameterTapeLaw (κ i))).map
      (fun raw => (populationSimulation pol n raw).2) = parameterWordLaw κ pol n :=
  parameterTapeLaw_population_word_law κ n pol

instance parameterWordLaw_probability {m : ℕ} (κ : Fin m → Measure unitInterval)
    [∀ i, IsProbabilityMeasure (κ i)] (pol : List Bool → Option (Fin m)) (n : ℕ) :
    IsProbabilityMeasure (parameterWordLaw κ pol n) := by
  rw [← parameter_word_law κ pol n]
  infer_instance

theorem parameter_weight_factor {m n : ℕ} (κ : Fin m → Measure unitInterval)
    [∀ i, IsProbabilityMeasure (κ i)] (pol : List Bool → Option (Fin m)) (w : Prefix n) :
    parameterWeight κ pol w = pathValidity pol w * ∏ i, coinMass pol w i (κ i) :=
  parameter_pathProb_factor κ pol w

theorem parameter_weight_nonneg {m n : ℕ} (κ : Fin m → Measure unitInterval)
    (pol : List Bool → Option (Fin m)) (w : Prefix n) : 0 ≤ parameterWeight κ pol w :=
  integral_nonneg (fun p => (pathProb_parameters_bounds pol w p).1)

theorem parameter_weight_total {m n : ℕ} (κ : Fin m → Measure unitInterval)
    [∀ i, IsProbabilityMeasure (κ i)] (pol : List Bool → Option (Fin m)) :
    ∑ w : Prefix n, parameterWeight κ pol w = 1 := by
  unfold parameterWeight
  rw [← integral_finsetSum _ (fun w _ => integrable_pathProb_parameters κ pol w)]
  simp only [pathProb_total,integral_const,probReal_univ,smul_eq_mul,one_mul]

theorem coinMass_nonneg {m n : ℕ} (pol : List Bool → Option (Fin m))
    (w : Prefix n) (i : Fin m) (κ : Measure unitInterval) : 0 ≤ coinMass pol w i κ :=
  integral_nonneg (fun p => coinLike_nonneg pol w i p.property.1 p.property.2)

theorem coinMass_integrable {m n : ℕ} (pol : List Bool → Option (Fin m))
    (w : Prefix n) (i : Fin m) (κ : Measure unitInterval) [IsProbabilityMeasure κ] :
    Integrable (fun p : unitInterval => coinLike pol w i p) κ :=
  ThresholdHC.Tier5.integrable_of_abs_bound _ _
    ((continuous_coinLike pol w i).measurable.comp measurable_subtype_coe) 1
    (fun p => by
      rw [abs_of_nonneg (coinLike_nonneg pol w i p.property.1 p.property.2)]
      exact coinLike_le_one pol w i p p.property.1 p.property.2)

end ThresholdHC.TypedConfidence
