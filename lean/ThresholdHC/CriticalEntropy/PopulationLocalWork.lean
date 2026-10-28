import ThresholdHC.CriticalEntropy.PopulationTapeLaw

noncomputable section
namespace ThresholdHC.CriticalEntropy
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- The existing hidden-coin generator supplies an independent seed and a
mixture coin tape. The identity includes the full seed, not only the flips. -/
theorem populationInput_preserving {D R : Type} [MeasurableSpace D] [MeasurableSpace R]
    (μ : Measure D) [IsProbabilityMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (p₀ p₁ q : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q) :
    MeasurePreserving (populationInput (R := R) p₀ p₁ q) (populationMeasure μ ν)
      (ν.prod (parameterTapeLaw (populationParameterLaw μ p₀ p₁ q))) := by
  let L := μ.prod uniformUnitMeasure
  let κ := populationParameterLaw μ p₀ p₁ q
  have hm := measurable_mixtureParameter p₀ p₁ q h₀ h₁ hq
  let G (z : (D × ℝ) × (ℕ → ℝ)) := uniformCoinTape (mixtureParameter p₀ p₁ q z.1) z.2
  have hGm : Measurable G := measurable_uniformCoinTape.comp
    ((hm.comp measurable_fst).prodMk measurable_snd)
  have hM : (L.prod uniformTapeMeasure).map
      (Prod.map (mixtureParameter p₀ p₁ q) id) = κ.prod uniformTapeMeasure := by
    rw [← Measure.map_prod_map L uniformTapeMeasure hm measurable_id,Measure.map_id]
    rfl
  have hG : MeasurePreserving G (L.prod uniformTapeMeasure) (parameterTapeLaw κ) := by
    refine ⟨hGm,?_⟩
    rw [parameterTapeLaw,← hM,Measure.map_map measurable_uniformCoinTape (hm.prodMap measurable_id)]
    rfl
  have h1 := (measurePreserving_prodAssoc μ uniformUnitMeasure (ν.prod uniformTapeMeasure)).symm
  have h2 := (measurePreserving_prodAssoc L ν uniformTapeMeasure).symm
  have h3 := (Measure.measurePreserving_swap (μ := L) (ν := ν)).prod
    (MeasurePreserving.id uniformTapeMeasure)
  have h4 := measurePreserving_prodAssoc ν L uniformTapeMeasure
  have hall := ((MeasurePreserving.id ν).prod hG).comp (h4.comp (h3.comp (h2.comp h1)))
  convert hall using 1 <;> rfl

theorem populationInput_output_law {D R E : Type} [MeasurableSpace D] [MeasurableSpace R]
    [MeasurableSpace E] (μ : Measure D) [IsProbabilityMeasure μ]
    (ν : Measure R) [IsProbabilityMeasure ν] (p₀ p₁ q : D → unitInterval)
    (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q)
    (A : StoppedProcedure R E) :
    (populationMeasure μ ν).map (A.output ∘ populationInput p₀ p₁ q) =
      (ν.prod (parameterTapeLaw (populationParameterLaw μ p₀ p₁ q))).map A.output := by
  rw [← (populationInput_preserving μ ν p₀ p₁ q h₀ h₁ hq).map_eq,
    Measure.map_map A.measurable_output (measurable_populationInput p₀ p₁ q h₀ h₁ hq)]

theorem populationInput_work {D R E : Type} [MeasurableSpace D] [MeasurableSpace R]
    [MeasurableSpace E] (μ : Measure D) [IsProbabilityMeasure μ]
    (ν : Measure R) [IsProbabilityMeasure ν] (p₀ p₁ q : D → unitInterval)
    (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q)
    (A : StoppedProcedure R E) :
    populationExpectedWork μ ν p₀ p₁ q A =
      ∫⁻ z, stoppedProcedureWork A z ∂ν.prod (parameterTapeLaw (populationParameterLaw μ p₀ p₁ q)) :=
  (populationInput_preserving μ ν p₀ p₁ q h₀ h₁ hq).lintegral_comp
    (measurable_stoppedProcedureWork A)

theorem populationInput_capped_law {D R E : Type} [MeasurableSpace D] [MeasurableSpace R]
    [MeasurableSpace E] (μ : Measure D) [IsProbabilityMeasure μ]
    (ν : Measure R) [IsProbabilityMeasure ν] (p₀ p₁ q : D → unitInterval)
    (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q)
    (A : StoppedProcedure R E) (n : ℕ) :
    cappedTranscriptLaw μ ν p₀ p₁ q A n =
      (ν.prod (parameterTapeLaw (populationParameterLaw μ p₀ p₁ q))).map
        (cappedTranscript A n) := by
  rw [← (populationInput_preserving μ ν p₀ p₁ q h₀ h₁ hq).map_eq,
    Measure.map_map (measurable_cappedTranscript A n)
      (measurable_populationInput p₀ p₁ q h₀ h₁ hq)]
  rfl

end ThresholdHC.CriticalEntropy

open MeasureTheory ProbabilityTheory Set
namespace ThresholdHC.CriticalEntropy

/-- Replace one coordinate of an independent array by an independent draw.
The unused original coordinate is integrated out, with no restriction on X. -/
theorem array_replace_preserving {I X : Type} [Fintype I] [DecidableEq I]
    [MeasurableSpace X] (μ : I → Measure X) [∀ i, IsProbabilityMeasure (μ i)]
    (ν : Measure X) [IsProbabilityMeasure ν] (j : I) :
    MeasurePreserving (fun z : (I → X) × X => Function.update z.1 j z.2)
      ((Measure.pi μ).prod ν) (Measure.pi (Function.update μ j ν)) := by
  let (i : I) : IsProbabilityMeasure (Function.update μ j ν i) := by
    by_cases h : i=j
    · subst i; simpa only [Function.update_self] using (inferInstance : IsProbabilityMeasure ν)
    · simpa only [Function.update_of_ne h] using (inferInstance : IsProbabilityMeasure (μ i))
  refine ⟨measurable_update',?_⟩
  refine (Measure.pi_eq (fun S hS => ?_)).symm
  rw [Measure.map_apply measurable_update' (MeasurableSet.univ_pi hS)]
  have he : (fun z : (I → X) × X => Function.update z.1 j z.2) ⁻¹' Set.univ.pi S =
      (Set.univ.pi (Function.update S j Set.univ)) ×ˢ S j := by
    ext z
    simp only [mem_preimage,mem_pi,mem_univ,forall_true_left,mem_prod]
    constructor
    · intro h
      constructor
      · intro i
        by_cases hi : i=j
        · subst i; simp
        · simpa only [Function.update_of_ne hi] using h i
      · simpa only [Function.update_self] using h j
    · rintro ⟨h,hj⟩ i
      by_cases hi : i=j
      · subst i; simpa only [Function.update_self] using hj
      · simpa only [Function.update_of_ne hi] using h i
  rw [he,Measure.prod_prod,Measure.pi_pi]
  rw [← Finset.prod_erase_mul Finset.univ (fun i => μ i (Function.update S j univ i))
      (Finset.mem_univ j),
    ← Finset.prod_erase_mul Finset.univ (fun i => Function.update μ j ν i (S i))
      (Finset.mem_univ j)]
  simp only [Function.update_self,measure_univ,mul_one]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  simp only [Function.update_of_ne (Finset.mem_erase.mp hi).1]

end ThresholdHC.CriticalEntropy
namespace ThresholdHC.CriticalEntropy
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
local instance : MeasurableSpace (Option Bool) := ⊤

theorem measurable_populationSimulation_count {I : Type} [DecidableEq I]
    (n : ℕ) (pol : List Bool → Option I) (i : I) :
    Measurable (fun s : I → ℕ → Bool => (populationSimulation pol n s).1 i) := by
  have h := (measurable_localSimulation i n pol).fst.comp
    (measurable_id.prodMk (measurable_pi_apply i))
  simpa only [Function.comp_def,id_eq,localSimulation_eq_population,Function.update_eq_self] using h

theorem localSimulation_word_law {m : ℕ}
    (μ : Fin m → Measure (ℕ → Bool)) [∀ i, IsProbabilityMeasure (μ i)]
    (τ : Measure (ℕ → Bool)) [IsProbabilityMeasure τ]
    (n : ℕ) (pol : List Bool → Option (Fin m)) (i : Fin m) :
    ((Measure.pi μ).prod τ).map (localSimulationProcedure i n pol).output =
      (Measure.pi (Function.update μ i τ)).map (fun s => (populationSimulation pol n s).2) := by
  rw [← (array_replace_preserving μ τ i).map_eq,
    Measure.map_map (measurable_populationSimulation_word n pol) measurable_update']
  congr 1
  funext z
  exact congrArg Prod.snd (localSimulation_eq_population i n pol z.1 z.2)

theorem localSimulation_work {m : ℕ}
    (μ : Fin m → Measure (ℕ → Bool)) [∀ i, IsProbabilityMeasure (μ i)]
    (τ : Measure (ℕ → Bool)) [IsProbabilityMeasure τ]
    (n : ℕ) (pol : List Bool → Option (Fin m)) (i : Fin m) :
    (∫⁻ z, stoppedProcedureWork (localSimulationProcedure i n pol) z ∂(Measure.pi μ).prod τ) =
      ∫⁻ s, ((populationSimulation pol n s).1 i : ℝ≥0∞) ∂Measure.pi (Function.update μ i τ) := by
  have hm : Measurable (fun s => ((populationSimulation pol n s).1 i : ℝ≥0∞)) :=
    (measurable_of_countable (fun k : ℕ => (k : ℝ≥0∞))).comp
      (measurable_populationSimulation_count n pol i)
  have h := (array_replace_preserving μ τ i).lintegral_comp hm
  convert h using 1
  apply lintegral_congr
  intro z
  simp [stoppedProcedureWork,localSimulationProcedure,localSimulation_eq_population]

/-- Actual population expected work of the local simulations sums exactly to
the full population flip count when every coin is drawn from the reference law. -/
theorem population_localSimulation_total_work {D : Type} [MeasurableSpace D] {m n : ℕ}
    (μ : Measure D) [IsProbabilityMeasure μ] (p₀ p₁ q : D → unitInterval)
    (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q)
    (pol : List Bool → Option (Fin m)) :
    let τ := parameterTapeLaw (populationParameterLaw μ p₀ p₁ q)
    (∑ i : Fin m, populationExpectedWork μ (Measure.pi (fun _ : Fin m => τ)) p₀ p₁ q
      (localSimulationProcedure i n pol)) =
      ∫⁻ s, ((∑ t : Fin n, if ((populationSimulation pol n s).2 t).isSome then 1 else 0 : ℕ) : ℝ≥0∞)
        ∂Measure.pi (fun _ : Fin m => τ) := by
  let := populationParameterLaw_probability μ p₀ p₁ q h₀ h₁ hq
  dsimp only
  simp_rw [populationInput_work μ _ p₀ p₁ q h₀ h₁ hq,localSimulation_work,
    Function.update_eq_self]
  have hm (i : Fin m) : Measurable (fun s => ((populationSimulation pol n s).1 i : ℝ≥0∞)) :=
    (measurable_of_countable (fun k : ℕ => (k : ℝ≥0∞))).comp
      (measurable_populationSimulation_count n pol i)
  rw [← lintegral_finsetSum Finset.univ (fun i hi => hm i)]
  apply lintegral_congr
  intro s
  exact_mod_cast populationSimulation_total_work n pol s

end ThresholdHC.CriticalEntropy
