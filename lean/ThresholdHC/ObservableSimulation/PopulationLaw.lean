import ThresholdHC.ObservableSimulation.LawUniqueness
import ThresholdHC.ObservableSimulation.PopulationPath
import ThresholdHC.ObservableSimulation.SimulationCap
import ThresholdHC.CriticalEntropy.ObservablePopulation

noncomputable section

namespace ThresholdHC.ObservableSimulation
open MeasureTheory ThresholdHC.CriticalEntropy ThresholdHC.Tier3 ThresholdHC.Proofs
open scoped ENNReal

theorem infinite_population_word_law {D : Type} [MeasurableSpace D]
    (μ : Measure D) [IsProbabilityMeasure μ] (p₀ p₁ q : D → unitInterval)
    (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q)
    (d : D → ℝ) (hd : Measurable d)
    (h₀d : ∀ᵐ x ∂μ, (p₀ x : ℝ) = 1/2-d x)
    (h₁d : ∀ᵐ x ∂μ, (p₁ x : ℝ) = 1/2+d x)
    (n : ℕ) (pol : List Bool → Option ℕ) :
    (Measure.infinitePi (fun _ : ℕ => parameterTapeLaw (populationParameterLaw μ p₀ p₁ q))).map
      (fun s => (populationSimulation pol n s).2) =
      finiteWeightMeasure (creationPopulationWeight (n := n) μ pol d (fun x => (q x : ℝ))) := by
  let τ := parameterTapeLaw (populationParameterLaw μ p₀ p₁ q)
  letI : IsProbabilityMeasure (populationParameterLaw μ p₀ p₁ q) :=
    populationParameterLaw_probability μ p₀ p₁ q h₀ h₁ hq
  let m := Tier5.coinCap n pol
  let res (s : ℕ → ℕ → Bool) : Fin m → ℕ → Bool := fun i => s i.val
  have hm : Measurable res := Measurable.of_eval (fun i => measurable_pi_apply i.val)
  have hmap : (Measure.infinitePi (fun _ : ℕ => τ)).map res = Measure.pi (fun _ : Fin m => τ) := by
    rw [Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective,Measure.infinitePi_eq_pi]
  calc
    _ = ((Measure.infinitePi (fun _ : ℕ => τ)).map res).map
        (fun s => (populationSimulation (Tier5.capPolicy m pol) n s).2) := by
      rw [Measure.map_map (measurable_populationSimulation_word n _) hm]
      congr 1
      funext s
      exact populationSimulation_cap n pol s
    _ = _ := by
      rw [hmap,population_tape_word_law μ p₀ p₁ h₀ h₁ (fun _ => q) (fun _ => hq) d h₀d h₁d]
      congr 1
      funext w
      exact (creationPopulationWeight_eq_finite μ pol d (fun x => (q x : ℝ)) hd
        (measurable_subtype_coe.comp hq) w).symm

end ThresholdHC.ObservableSimulation

namespace ThresholdHC.ObservableSimulation
open MeasureTheory ThresholdHC.CriticalEntropy ThresholdHC.Tier3 ThresholdHC.Tier4
open scoped ENNReal

theorem seeded_population_prefix_kernel {R D : Type} [MeasurableSpace R] [MeasurableSpace D]
    (ν : Measure R) [IsProbabilityMeasure ν] (μ : Measure D) [IsProbabilityMeasure μ]
    (p₀ p₁ q : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q)
    (d : D → ℝ) (hdm : Measurable d) (hd : ∀ x, 0 ≤ d x ∧ d x ≤ 1/2)
    (h₀d : ∀ᵐ x ∂μ, (p₀ x : ℝ) = 1/2-d x)
    (h₁d : ∀ᵐ x ∂μ, (p₁ x : ℝ) = 1/2+d x)
    (pol : R → List Bool → Option ℕ) (hp : ∀ xs, Measurable (fun r => pol r xs)) (n : ℕ) :
    Tier5.FiniteKernelRealization ν
      ((ν.prod (Measure.infinitePi (fun _ : ℕ => parameterTapeLaw (populationParameterLaw μ p₀ p₁ q)))).map
        (fun z => (z.1,(populationSimulation (pol z.1) n z.2).2)))
      (fun r w => creationPopulationWeight μ (pol r) d (fun x => (q x : ℝ)) w) := by
  let τ := parameterTapeLaw (populationParameterLaw μ p₀ p₁ q)
  letI : IsProbabilityMeasure (populationParameterLaw μ p₀ p₁ q) :=
    populationParameterLaw_probability μ p₀ p₁ q h₀ h₁ hq
  let tapes := Measure.infinitePi (fun _ : ℕ => τ)
  have hm := measurable_fst.prodMk (measurable_seeded_populationSimulation n pol hp)
  intro f hf hb
  obtain ⟨C,hC⟩ := hb
  have hF : Integrable (fun z : R × (ℕ → ℕ → Bool) =>
      f (z.1,(populationSimulation (pol z.1) n z.2).2)) (ν.prod tapes) :=
    Tier5.integrable_of_abs_bound _ _ (hf.comp hm) C (fun z => hC _)
  rw [integral_map hm.aemeasurable hf.aestronglyMeasurable,integral_prod _ hF]
  apply integral_congr_ae
  apply ae_of_all
  intro r
  have hfr : Measurable (fun w => f (r,w)) := hf.comp (measurable_const.prodMk measurable_id)
  have hmap := infinite_population_word_law μ p₀ p₁ q h₀ h₁ hq d hdm h₀d h₁d n (pol r)
  have hnonneg := (creationPopulationWeight_total (n := n) μ (pol r) d (fun x => (q x : ℝ)) hdm
    (measurable_subtype_coe.comp hq) hd (fun x => (q x).property)).1
  calc
    _ = ∫ w, f (r,w) ∂tapes.map (fun s => (populationSimulation (pol r) n s).2) :=
      (integral_map (measurable_populationSimulation_word n (pol r)).aemeasurable
        hfr.aestronglyMeasurable).symm
    _ = _ := by
      rw [hmap,integral_fintype]
      · apply Finset.sum_congr rfl
        intro w hw
        simp only [finiteWeightMeasure_singleton,Measure.real,ENNReal.toReal_ofReal (hnonneg w),smul_eq_mul]
      · rw [← hmap]
        exact Tier5.integrable_of_abs_bound _ _ hfr C (fun w => hC (r,w))

/-- The independent population-tape simulation and every realization of the
original creation experiment have exactly the same full observable law. -/
theorem population_simulation_observable_law {R D Ω : Type}
    [MeasurableSpace R] [MeasurableSpace D] [MeasurableSpace Ω]
    (ν : Measure R) [IsProbabilityMeasure ν] (μ : Measure D) [IsProbabilityMeasure μ]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (seed : Ω → R × (ℕ → D)) (tape : Ω → ProcessTape)
    (p₀ p₁ q : D → unitInterval) (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q)
    (d : D → ℝ) (hdm : Measurable d) (hd : ∀ x, 0 ≤ d x ∧ d x ≤ 1/2)
    (h₀d : ∀ᵐ x ∂μ, (p₀ x : ℝ) = 1/2-d x)
    (h₁d : ∀ᵐ x ∂μ, (p₁ x : ℝ) = 1/2+d x)
    (pol : R → List Bool → Option ℕ) (hp : Tier5.MeasurableCreationPolicy pol)
    (hs : Measurable seed) (ht : Measurable tape)
    (hreal : Tier5.RealizesCreationPrefixes (ν.prod (Measure.infinitePi (fun _ : ℕ => μ)))
      P seed tape (fun z => pol z.1) (fun z i => d (z.2 i)) (fun z i => (q (z.2 i) : ℝ))) :
    P.map (fun ω => ((seed ω).1,tape ω)) =
      (ν.prod (Measure.infinitePi (fun _ : ℕ => parameterTapeLaw (populationParameterLaw μ p₀ p₁ q)))).map
        (fun z => (z.1,populationPath (pol z.1) z.2)) := by
  letI : IsProbabilityMeasure (populationParameterLaw μ p₀ p₁ q) :=
    populationParameterLaw_probability μ p₀ p₁ q h₀ h₁ hq
  have hpm : ∀ xs, Measurable (fun r => pol r xs) := fun xs =>
    measurable_to_countable' (fun a => hp xs a)
  have hm := measurable_fst.prodMk (measurable_seeded_populationPath pol hpm)
  apply joint_tape_law_ext
  intro n
  rw [Measure.map_map (measurable_jointPrefix n) (hs.fst.prodMk ht),
    Measure.map_map (measurable_jointPrefix n) hm]
  simp_rw [Function.comp_def,populationPath_prefix]
  apply measure_eq_of_bounded_real_tests
  intro f hf hb
  have hleft := observable_population_prefix_kernel ν μ P seed tape pol d (fun x => (q x : ℝ))
    hs (fun k b => ((measurable_pi_apply k).comp ht) (measurableSet_singleton b)) hp hdm
    (measurable_subtype_coe.comp hq) hd (fun x => (q x).property) hreal n
  have hright := seeded_population_prefix_kernel ν μ p₀ p₁ q h₀ h₁ hq d hdm hd h₀d h₁d pol hpm n
  exact (hleft f hf hb).trans (hright f hf hb).symm

end ThresholdHC.ObservableSimulation
