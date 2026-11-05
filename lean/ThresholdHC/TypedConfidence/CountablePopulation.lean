import ThresholdHC.TypedConfidence.LikelihoodRatio
import ThresholdHC.TypedConfidence.NullTransfer
import ThresholdHC.ObservableSimulation.PopulationLaw

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace ThresholdHC.TypedConfidence
open ThresholdHC ThresholdHC.Proofs ThresholdHC.Tier3 ThresholdHC.CriticalEntropy
open ThresholdHC.ObservableSimulation

local instance : MeasurableSpace (Option Bool) := ⊤
local instance : MeasurableSingletonClass (Option Bool) := ⟨fun _ => trivial⟩

def countableParameterWeight {n : ℕ} (κ : ℕ → Measure unitInterval)
    (pol : List Bool → Option ℕ) (w : Prefix n) : ℝ :=
  parameterWeight (fun i : Fin (Tier5.coinCap n pol) => κ i.val)
    (Tier5.capPolicy (Tier5.coinCap n pol) pol) w

/-- Arbitrarily large creation labels reduce exactly to the finite labels the
decision tree can address before this horizon. -/
theorem countable_parameter_word_law (κ : ℕ → Measure unitInterval)
    [∀ i, IsProbabilityMeasure (κ i)] (n : ℕ) (pol : List Bool → Option ℕ) :
    (Measure.infinitePi (fun i => parameterTapeLaw (κ i))).map
      (fun s => (populationSimulation pol n s).2) =
      finiteWeightMeasure (countableParameterWeight κ pol (n := n)) := by
  let m := Tier5.coinCap n pol
  let res (s : ℕ → ℕ → Bool) : Fin m → ℕ → Bool := fun i => s i.val
  have hm : Measurable res := Measurable.of_eval (fun i => measurable_pi_apply i.val)
  have hmap : (Measure.infinitePi (fun i => parameterTapeLaw (κ i))).map res =
      Measure.pi (fun i : Fin m => parameterTapeLaw (κ i.val)) := by
    rw [Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective,Measure.infinitePi_eq_pi]
  calc
    _ = ((Measure.infinitePi (fun i => parameterTapeLaw (κ i))).map res).map
        (fun s => (populationSimulation (Tier5.capPolicy m pol) n s).2) := by
      rw [Measure.map_map (measurable_populationSimulation_word n _) hm]
      congr 1
      funext s
      exact populationSimulation_cap n pol s
    _ = _ := by rw [hmap,parameter_word_law]; rfl

theorem countable_parameter_total (κ : ℕ → Measure unitInterval)
    [∀ i, IsProbabilityMeasure (κ i)] {n : ℕ} (pol : List Bool → Option ℕ) :
    (∀ w : Prefix n, 0 ≤ countableParameterWeight κ pol w) ∧
      ∑ w : Prefix n, countableParameterWeight κ pol w = 1 :=
  ⟨parameter_weight_nonneg _ _,parameter_weight_total _ _⟩

instance countable_parameter_probability (κ : ℕ → Measure unitInterval)
    [∀ i, IsProbabilityMeasure (κ i)] {n : ℕ} (pol : List Bool → Option ℕ) :
    IsProbabilityMeasure (finiteWeightMeasure (countableParameterWeight κ pol (n := n))) :=
  finiteWeightMeasure_probability _ (countable_parameter_total κ pol).1 (countable_parameter_total κ pol).2

theorem countable_parameter_weight_integral (κ : ℕ → Measure unitInterval)
    [∀ i, IsProbabilityMeasure (κ i)] {n : ℕ} (pol : List Bool → Option ℕ) (w : Prefix n) :
    countableParameterWeight κ pol w =
      (∫⁻ s, if (populationSimulation pol n s).2 = w then (1 : ℝ≥0∞) else 0
        ∂Measure.infinitePi (fun i => parameterTapeLaw (κ i))).toReal := by
  have hm := measurable_populationSimulation_word n pol
  have he := countable_parameter_word_law κ n pol
  have hn := (countable_parameter_total κ pol (n := n)).1
  rw [← finiteWeightMeasure_real_singleton _ hn,← he,Measure.real,
    Measure.map_apply hm (measurableSet_singleton w)]
  congr 1
  rw [← lintegral_indicator_one (hm (measurableSet_singleton w))]
  apply lintegral_congr
  intro s
  simp [Set.indicator,Set.mem_preimage,Set.mem_singleton_iff]

theorem measurable_countableParameterWeight {R : Type} [MeasurableSpace R]
    (κ : ℕ → Measure unitInterval) [∀ i, IsProbabilityMeasure (κ i)]
    (pol : R → List Bool → Option ℕ) (hp : ∀ xs, Measurable (fun r => pol r xs))
    {n : ℕ} (w : Prefix n) : Measurable (fun r => countableParameterWeight κ (pol r) w) := by
  simp_rw [countable_parameter_weight_integral]
  have hm := measurable_seeded_populationSimulation n pol hp
  have hf : Measurable (fun z : R × (ℕ → ℕ → Bool) =>
      if (populationSimulation (pol z.1) n z.2).2 = w then (1 : ℝ≥0∞) else 0) :=
    Measurable.ite (measurableSet_eq_fun hm measurable_const) measurable_const measurable_const
  exact hf.lintegral_prod_right'.ennreal_toReal

theorem countable_parameter_quarter_ratio (κ τ : ℕ → Measure unitInterval)
    [∀ i, IsProbabilityMeasure (κ i)] [∀ i, IsProbabilityMeasure (τ i)]
    {n : ℕ} (pol : List Bool → Option ℕ) (w : Prefix n) :
    countableParameterWeight (fun i => ConfidenceTransfer.quarterMix (κ i) (τ i)) pol w ≤
      3^n * countableParameterWeight (fun i => ConfidenceTransfer.quarterMix (τ i) (κ i)) pol w :=
  parameter_quarter_ratio _ _ _ _

/-- The private random seed is retained in the observable prefix law. -/
theorem seeded_parameter_prefix_kernel {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν]
    (κ : ℕ → Measure unitInterval) [∀ i, IsProbabilityMeasure (κ i)]
    (pol : R → List Bool → Option ℕ) (hp : ∀ xs, Measurable (fun r => pol r xs)) (n : ℕ) :
    Tier5.FiniteKernelRealization ν
      ((ν.prod (Measure.infinitePi (fun i => parameterTapeLaw (κ i)))).map
        (fun z => (z.1,(populationSimulation (pol z.1) n z.2).2)))
      (fun r w => countableParameterWeight κ (pol r) w) := by
  let tapes := Measure.infinitePi (fun i => parameterTapeLaw (κ i))
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
  have hmap := countable_parameter_word_law κ n (pol r)
  calc
    _ = ∫ w, f (r,w) ∂tapes.map (fun s => (populationSimulation (pol r) n s).2) :=
      (integral_map (measurable_populationSimulation_word n (pol r)).aemeasurable
        hfr.aestronglyMeasurable).symm
    _ = _ := by
      rw [hmap,integral_fintype Integrable.of_finite]
      apply Finset.sum_congr rfl
      intro w _
      simp only [finiteWeightMeasure_real_singleton _ (countable_parameter_total κ (pol r)).1,smul_eq_mul]

end ThresholdHC.TypedConfidence
