import ThresholdHC.CriticalEntropy.FiniteAffinity
import ThresholdHC.CriticalEntropy.MidpointWork
import ThresholdHC.CriticalEntropy.PopulationLocalWork

noncomputable section
namespace ThresholdHC.CriticalEntropy
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
local instance : MeasurableSpace (Option Bool) := ⊤

theorem population_localSimulation_word_law {D : Type} [MeasurableSpace D] {m n : ℕ}
    (μ : Measure D) [IsProbabilityMeasure μ] (p₀ p₁ q s : D → unitInterval)
    (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q) (hs : Measurable s)
    (d : D → ℝ) (h₀d : ∀ᵐ x ∂μ, (p₀ x : ℝ) = 1/2-d x)
    (h₁d : ∀ᵐ x ∂μ, (p₁ x : ℝ) = 1/2+d x)
    (pol : List Bool → Option (Fin m)) (i : Fin m) :
    let ν := Measure.pi (fun _ : Fin m => parameterTapeLaw (populationParameterLaw μ p₀ p₁ s))
    (populationMeasure μ ν).map
      ((localSimulationProcedure i n pol).output ∘ populationInput p₀ p₁ q) =
      finiteWeightMeasure (finitePopulationWeight (n := n) μ pol d
        (fun j x => if j=i then (q x : ℝ) else (s x : ℝ))) := by
  classical
  let : IsProbabilityMeasure (populationParameterLaw μ p₀ p₁ q) :=
    populationParameterLaw_probability μ p₀ p₁ q h₀ h₁ hq
  let : IsProbabilityMeasure (populationParameterLaw μ p₀ p₁ s) :=
    populationParameterLaw_probability μ p₀ p₁ s h₀ h₁ hs
  dsimp only
  rw [populationInput_output_law μ _ p₀ p₁ q h₀ h₁ hq,localSimulation_word_law]
  have h := population_tape_word_law μ p₀ p₁ h₀ h₁ (fun j => if j=i then q else s)
    (fun j => by split_ifs <;> assumption) d h₀d h₁d pol (n := n)
  convert h using 2
  · congr 1
    funext j
    by_cases hj : j=i <;> simp [hj]
  · congr 1
    funext j x
    split_ifs <;> rfl

/-- The information in a finite population word is bounded by the canonical
observation of its legal local one-coin simulation. -/
theorem localSimulation_affinity_le {D : Type} [MeasurableSpace D] {m n : ℕ}
    (μ : Measure D) [IsProbabilityMeasure μ] (p₀ p₁ q r s : D → unitInterval)
    (h₀ : Measurable p₀) (h₁ : Measurable p₁)
    (hq : Measurable q) (hr : Measurable r) (hs : Measurable s)
    (d : D → ℝ) (hdm : Measurable d) (hd : ∀ x, 0 ≤ d x ∧ d x ≤ 1/2)
    (h₀d : ∀ᵐ x ∂μ, (p₀ x : ℝ) = 1/2-d x)
    (h₁d : ∀ᵐ x ∂μ, (p₁ x : ℝ) = 1/2+d x)
    (pol : List Bool → Option (Fin m)) (i : Fin m) :
    let ν := Measure.pi (fun _ : Fin m => parameterTapeLaw (populationParameterLaw μ p₀ p₁ s))
    (hellingerAffinity
      (cappedTranscriptLaw μ ν p₀ p₁ q (localSimulationProcedure i n pol) n)
      (cappedTranscriptLaw μ ν p₀ p₁ r (localSimulationProcedure i n pol) n)).toReal ≤
    realFiniteAffinity
      (finitePopulationWeight (n := n) μ pol d (fun j x => if j=i then (q x : ℝ) else (s x : ℝ)))
      (finitePopulationWeight μ pol d (fun j x => if j=i then (r x : ℝ) else (s x : ℝ))) := by
  classical
  let τ (u : D → unitInterval) := parameterTapeLaw (populationParameterLaw μ p₀ p₁ u)
  let ν := Measure.pi (fun _ : Fin m => τ s)
  let A := localSimulationProcedure i n pol
  let : IsProbabilityMeasure (populationParameterLaw μ p₀ p₁ q) :=
    populationParameterLaw_probability μ p₀ p₁ q h₀ h₁ hq
  let : IsProbabilityMeasure (populationParameterLaw μ p₀ p₁ r) :=
    populationParameterLaw_probability μ p₀ p₁ r h₀ h₁ hr
  let : IsProbabilityMeasure (populationParameterLaw μ p₀ p₁ s) :=
    populationParameterLaw_probability μ p₀ p₁ s h₀ h₁ hs
  have hcap : ∀ z, A.stop z ≤ n := localSimulationProcedure_capped i n pol
  have h := cappedOutput_affinity A n hcap (ν.prod (τ q)) (ν.prod (τ r))
  have hfin := ne_top_of_le_ne_top (by simp : (1 : ℝ≥0∞) ≠ ⊤)
    (hellingerAffinity_probability_le_one ((ν.prod (τ q)).map A.output)
      ((ν.prod (τ r)).map A.output))
  have hreal := ENNReal.toReal_mono hfin h
  rw [← populationInput_capped_law μ ν p₀ p₁ q h₀ h₁ hq A n,
    ← populationInput_capped_law μ ν p₀ p₁ r h₀ h₁ hr A n] at hreal
  have hout (u : D → unitInterval) (hu : Measurable u) :
      (ν.prod (τ u)).map A.output = finiteWeightMeasure (finitePopulationWeight (n := n)
        μ pol d (fun j x => if j=i then (u x : ℝ) else (s x : ℝ))) := by
    rw [← populationInput_output_law μ ν p₀ p₁ u h₀ h₁ hu A]
    exact population_localSimulation_word_law μ p₀ p₁ u s h₀ h₁ hu hs d h₀d h₁d pol i
  rw [hout q hq,hout r hr,finiteWeightMeasure_affinity] at hreal
  · exact hreal
  all_goals
    apply (finite_population_total μ pol d _ hdm _ hd _).1
    · intro j
      by_cases hj : j=i <;> simp only [hj,ite_true,ite_false]
      all_goals exact measurable_subtype_coe.comp (by assumption)
    · intro j x
      split_ifs <;> first | exact (q x).property | exact (r x).property | exact (s x).property

/-- Expected number of observed flips of the finite population simulator. -/
def finitePopulationExpectedWork {D : Type} [MeasurableSpace D] {m : ℕ}
    (μ : Measure D) (p₀ p₁ q : D → unitInterval)
    (pol : List Bool → Option (Fin m)) (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ s, ((∑ t : Fin n, if ((populationSimulation pol n s).2 t).isSome then 1 else 0 : ℕ) : ℝ≥0∞)
    ∂Measure.pi (fun _ : Fin m => parameterTapeLaw (populationParameterLaw μ p₀ p₁ q))

theorem population_localSimulation_total_work_real {D : Type} [MeasurableSpace D] {m n : ℕ}
    (μ : Measure D) [IsProbabilityMeasure μ] (p₀ p₁ q : D → unitInterval)
    (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q)
    (pol : List Bool → Option (Fin m)) :
    let ν := Measure.pi (fun _ : Fin m => parameterTapeLaw (populationParameterLaw μ p₀ p₁ q))
    (∑ i : Fin m, (populationExpectedWork μ ν p₀ p₁ q
      (localSimulationProcedure i n pol)).toReal) =
      (finitePopulationExpectedWork μ p₀ p₁ q pol n).toReal := by
  let : IsProbabilityMeasure (populationParameterLaw μ p₀ p₁ q) :=
    populationParameterLaw_probability μ p₀ p₁ q h₀ h₁ hq
  dsimp only
  rw [finitePopulationExpectedWork,← population_localSimulation_total_work μ p₀ p₁ q h₀ h₁ hq pol]
  symm
  apply ENNReal.toReal_sum
  intro i hi
  exact ne_top_of_le_ne_top (by simp) (population_capped_work_le μ _ p₀ p₁ q
    (localSimulationProcedure i n pol) n (localSimulationProcedure_capped i n pol))

/-- Transfer of a common single-coin information bound to the actual finite
adaptive population experiment. Every local cost is charged to the same
midpoint population; the policy may revisit and interleave its coins. -/
theorem finite_population_transfer {D : Type} [MeasurableSpace D] {m n : ℕ}
    (μ : Measure D) [IsProbabilityMeasure μ] (p₀ p₁ q r : D → unitInterval)
    (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q) (hr : Measurable r)
    (hqhalf : ∀ x, (q x : ℝ) ≤ 1/2) (hrhalf : ∀ x, (r x : ℝ) ≤ 1/2)
    (d : D → ℝ) (hdm : Measurable d) (hd : ∀ x, 0 ≤ d x ∧ d x ≤ 1/2)
    (h₀d : ∀ᵐ x ∂μ, (p₀ x : ℝ) = 1/2-d x)
    (h₁d : ∀ᵐ x ∂μ, (p₁ x : ℝ) = 1/2+d x)
    (pol : List Bool → Option (Fin m)) (K c : ℝ) (hK : 0 ≤ K) (hc : 0 ≤ c)
    (hbound : let ν := Measure.pi (fun _ : Fin m =>
        parameterTapeLaw (populationParameterLaw μ p₀ p₁ (midpointPrior q r)))
      ∀ i : Fin m, (1-(hellingerAffinity
        (cappedTranscriptLaw μ ν p₀ p₁ q (localSimulationProcedure i n pol) n)
        (cappedTranscriptLaw μ ν p₀ p₁ r (localSimulationProcedure i n pol) n)).toReal)*K ≤
        c*(populationExpectedWork μ ν p₀ p₁ (fun _ => 0) (localSimulationProcedure i n pol)).toReal) :
    (1-realFiniteAffinity (finitePopulationWeight (n := n) μ pol d (fun _ x => (q x : ℝ)))
      (finitePopulationWeight μ pol d (fun _ x => (r x : ℝ))))*K ≤
      2*c*(finitePopulationExpectedWork μ p₀ p₁ (midpointPrior q r) pol n).toReal := by
  classical
  let s := midpointPrior q r
  have hs : Measurable s := measurable_midpointPrior q r hq hr
  have hshalf (x) : (s x : ℝ) ≤ 1/2 := by
    change ((q x : ℝ)+(r x : ℝ))/2 ≤ 1/2
    linarith [hqhalf x,hrhalf x]
  let : IsProbabilityMeasure (populationParameterLaw μ p₀ p₁ s) :=
    populationParameterLaw_probability μ p₀ p₁ s h₀ h₁ hs
  let ν := Measure.pi (fun _ : Fin m => parameterTapeLaw (populationParameterLaw μ p₀ p₁ s))
  let W (i : Fin m) := populationExpectedWork μ ν p₀ p₁ s (localSimulationProcedure i n pol)
  have hlocal (i : Fin m) :
      (1-realFiniteAffinity
        (finitePopulationWeight (n := n) μ pol d (fun j x => if j=i then (q x : ℝ) else (s x : ℝ)))
        (finitePopulationWeight μ pol d (fun j x => if j=i then (r x : ℝ) else (s x : ℝ))))*K ≤
      2*c*(W i).toReal := by
    have hA := localSimulation_affinity_le μ p₀ p₁ q r s h₀ h₁ hq hr hs
      d hdm hd h₀d h₁d pol i (n := n)
    have hW := null_work_le_twice_population_work μ ν p₀ p₁ s h₀ h₁ hs hshalf
      (localSimulationProcedure i n pol)
    have hfin : W i ≠ ⊤ := ne_top_of_le_ne_top (by simp)
      (population_capped_work_le μ ν p₀ p₁ s (localSimulationProcedure i n pol) n
        (localSimulationProcedure_capped i n pol))
    have hWr := ENNReal.toReal_mono (ENNReal.mul_ne_top (by norm_num) hfin) hW
    rw [ENNReal.toReal_mul] at hWr
    norm_num only [ENNReal.toReal_ofNat] at hWr
    calc
      _ ≤ (1-(hellingerAffinity
          (cappedTranscriptLaw μ ν p₀ p₁ q (localSimulationProcedure i n pol) n)
          (cappedTranscriptLaw μ ν p₀ p₁ r (localSimulationProcedure i n pol) n)).toReal)*K :=
        mul_le_mul_of_nonneg_right (sub_le_sub_left hA 1) hK
      _ ≤ c*(populationExpectedWork μ ν p₀ p₁ (fun _ => 0)
          (localSimulationProcedure i n pol)).toReal := hbound i
      _ ≤ c*(2*(W i).toReal) := mul_le_mul_of_nonneg_left hWr hc
      _ = 2*c*(W i).toReal := by ring
  have hhyb := finite_population_hybrid_decomposition μ pol d
    (fun x => (q x : ℝ)) (fun x => (r x : ℝ)) hdm
    (measurable_subtype_coe.comp hq) (measurable_subtype_coe.comp hr)
    hd (fun x => (q x).property) (fun x => (r x).property) (n := n)
  have he (u : D → ℝ) (i : Fin m) :
      (fun j => if j=i then u else fun x => ((q x : ℝ)+(r x : ℝ))/2) =
      (fun j x => if j=i then u x else (s x : ℝ)) := by
    funext j x
    split_ifs <;> rfl
  simp_rw [he] at hhyb
  calc
    _ ≤ (∑ i : Fin m, (1-realFiniteAffinity
        (finitePopulationWeight (n := n) μ pol d (fun j x => if j=i then (q x : ℝ) else (s x : ℝ)))
        (finitePopulationWeight μ pol d (fun j x => if j=i then (r x : ℝ) else (s x : ℝ)))))*K := by
      exact mul_le_mul_of_nonneg_right hhyb hK
    _ = ∑ i : Fin m, (1-realFiniteAffinity
        (finitePopulationWeight (n := n) μ pol d (fun j x => if j=i then (q x : ℝ) else (s x : ℝ)))
        (finitePopulationWeight μ pol d (fun j x => if j=i then (r x : ℝ) else (s x : ℝ))))*K :=
      Finset.sum_mul _ _ _
    _ ≤ ∑ i : Fin m, 2*c*(W i).toReal := Finset.sum_le_sum (fun i hi => hlocal i)
    _ = _ := by
      rw [← Finset.mul_sum]
      congr 1
      exact population_localSimulation_total_work_real μ p₀ p₁ s h₀ h₁ hs pol

end ThresholdHC.CriticalEntropy
