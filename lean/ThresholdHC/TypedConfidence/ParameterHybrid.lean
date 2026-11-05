import ThresholdHC.TypedConfidence.ParameterPopulation
import ThresholdHC.TypedConfidence.Factorization

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal
namespace ThresholdHC.TypedConfidence
open ThresholdHC ThresholdHC.Proofs ThresholdHC.Tier3 ThresholdHC.CriticalEntropy
open ThresholdHC.ConfidenceTransfer

local instance : MeasurableSpace (Option Bool) := ⊤
local instance : MeasurableSingletonClass (Option Bool) := ⟨fun _ => trivial⟩

instance probability_update {I X : Type} [DecidableEq I] [MeasurableSpace X]
    (κ : I → Measure X) [∀ i, IsProbabilityMeasure (κ i)]
    (τ : Measure X) [IsProbabilityMeasure τ] (i j : I) :
    IsProbabilityMeasure (Function.update κ i τ j) := by
  by_cases h : j=i
  · subst j
    simpa only [Function.update_self] using (inferInstance : IsProbabilityMeasure τ)
  · simpa only [Function.update_of_ne h] using (inferInstance : IsProbabilityMeasure (κ j))

instance quarter_probability {X : Type} [MeasurableSpace X]
    (κ τ : Measure X) [IsProbabilityMeasure κ] [IsProbabilityMeasure τ] :
    IsProbabilityMeasure (quarterMix κ τ) := by
  constructor
  simp only [quarterMix,Measure.add_apply,Measure.smul_apply,measure_univ,
    ENNReal.smul_def,smul_eq_mul,mul_one,← ENNReal.coe_add]
  norm_num

theorem parameterTapeLaw_quarter (κ τ : Measure unitInterval)
    [IsProbabilityMeasure κ] [IsProbabilityMeasure τ] :
    parameterTapeLaw (quarterMix κ τ) = quarterMix (parameterTapeLaw κ) (parameterTapeLaw τ) := by
  simp only [parameterTapeLaw,quarterMix,Measure.add_prod,Measure.prod_smul_left,
    Measure.map_add _ _ measurable_uniformCoinTape,
    Measure.map_smul _ measurable_uniformCoinTape.aemeasurable]

theorem coinMass_quarter {m n : ℕ} (pol : List Bool → Option (Fin m))
    (w : Prefix n) (i : Fin m) (κ τ : Measure unitInterval)
    [IsProbabilityMeasure κ] [IsProbabilityMeasure τ] :
    coinMass pol w i (quarterMix κ τ) =
      (3*coinMass pol w i κ + coinMass pol w i τ)/4 := by
  unfold coinMass quarterMix
  rw [integral_add_measure (coinMass_integrable pol w i κ).smul_measure_nnreal
    (coinMass_integrable pol w i τ).smul_measure_nnreal,
    integral_smul_nnreal_measure,integral_smul_nnreal_measure]
  norm_num only [NNReal.smul_def,NNReal.coe_div,NNReal.coe_ofNat,NNReal.coe_one,smul_eq_mul]
  ring

/-- A single-coordinate replacement in the physical independent-tape experiment. -/
theorem parameter_local_word_law {m : ℕ}
    (κ : Fin m → Measure unitInterval) [∀ i, IsProbabilityMeasure (κ i)]
    (τ : Measure unitInterval) [IsProbabilityMeasure τ]
    (n : ℕ) (pol : List Bool → Option (Fin m)) (i : Fin m) :
    ((Measure.pi (fun j => parameterTapeLaw (κ j))).prod (parameterTapeLaw τ)).map
      (localSimulationProcedure i n pol).output =
        parameterWordLaw (Function.update κ i τ) pol n := by
  rw [localSimulation_word_law,← parameter_word_law]
  congr 2
  funext j
  by_cases h : j=i <;> simp [h]

theorem parameter_one_slot_quarter {m : ℕ}
    (κ : Fin m → Measure unitInterval) [∀ i, IsProbabilityMeasure (κ i)]
    (τ υ : Measure unitInterval) [IsProbabilityMeasure τ] [IsProbabilityMeasure υ]
    (n : ℕ) (pol : List Bool → Option (Fin m)) (i : Fin m) :
    parameterWordLaw (Function.update κ i (quarterMix τ υ)) pol n =
      quarterMix (parameterWordLaw (Function.update κ i τ) pol n)
        (parameterWordLaw (Function.update κ i υ) pol n) := by
  rw [← parameter_local_word_law,← parameter_local_word_law,← parameter_local_word_law,
    parameterTapeLaw_quarter]
  simp only [quarterMix,Measure.prod_add,Measure.prod_smul_right,
    Measure.map_add _ _ (localSimulationProcedure i n pol).measurable_output,
    Measure.map_smul _ (localSimulationProcedure i n pol).measurable_output.aemeasurable]

/-- An exact KL identity for heterogeneous parameter laws on persistent labels. -/
theorem parameter_hybrid_kl {m n : ℕ}
    (κ τ : Fin m → Measure unitInterval)
    [∀ i, IsProbabilityMeasure (κ i)] [∀ i, IsProbabilityMeasure (τ i)]
    (pol : List Bool → Option (Fin m))
    (hs : ∀ i (w : Prefix n), coinMass pol w i (τ i) = 0 → coinMass pol w i (κ i) = 0) :
    klDiv (parameterWordLaw κ pol n) (parameterWordLaw τ pol n) =
      ∑ i : Fin m, klDiv (parameterWordLaw κ pol n)
        (parameterWordLaw (Function.update κ i (τ i)) pol n) := by
  classical
  apply factorized_kl_sum (pathValidity pol)
    (fun i w => coinMass pol w i (κ i)) (fun i w => coinMass pol w i (τ i))
  · exact parameter_weight_factor κ pol
  · exact parameter_weight_factor τ pol
  · intro i w
    rw [parameter_weight_factor]
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    by_cases h : j=i <;> simp [h]
  · exact hs
  · exact ⟨parameter_weight_nonneg κ pol,parameter_weight_total κ pol⟩
  · exact ⟨parameter_weight_nonneg τ pol,parameter_weight_total τ pol⟩
  · intro i
    exact ⟨parameter_weight_nonneg _ pol,parameter_weight_total _ pol⟩

theorem quarter_parameter_hybrid_kl {m n : ℕ}
    (κ τ : Fin m → Measure unitInterval)
    [∀ i, IsProbabilityMeasure (κ i)] [∀ i, IsProbabilityMeasure (τ i)]
    (pol : List Bool → Option (Fin m)) :
    let ref := fun i => quarterMix (κ i) (τ i)
    let alt := fun i => quarterMix (τ i) (κ i)
    klDiv (parameterWordLaw ref pol n) (parameterWordLaw alt pol n) =
      ∑ i : Fin m, klDiv (parameterWordLaw ref pol n)
        (parameterWordLaw (Function.update ref i (alt i)) pol n) := by
  apply parameter_hybrid_kl
  intro i w h
  rw [coinMass_quarter] at h ⊢
  have hk := coinMass_nonneg pol w i (κ i)
  have ht := coinMass_nonneg pol w i (τ i)
  linarith

end ThresholdHC.TypedConfidence
