import ThresholdHC.TypedConfidence.CountablePopulation
import ThresholdHC.TypedConfidence.WorkLaw
import ThresholdHC.TypedConfidence.LocalBound
import ThresholdHC.ConfidenceTransfer.Terminal

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
namespace ThresholdHC.TypedConfidence
open ThresholdHC ThresholdHC.Proofs ThresholdHC.Tier3 ThresholdHC.Tier4 ThresholdHC.CriticalEntropy
open ThresholdHC.ObservableSimulation ThresholdHC.ConfidenceTransfer

local instance : MeasurableSpace (Option Bool) := ⊤
local instance : MeasurableSingletonClass (Option Bool) := ⟨fun _ => trivial⟩

/-- Actual observable law of an independent heterogeneous population, including
the independent private seed and every observation through stopping. -/
def parameterExperimentLaw {R : Type} [MeasurableSpace R]
    (ν : Measure R) (κ : ℕ → Measure unitInterval) [∀ i, IsProbabilityMeasure (κ i)]
    (pol : R → List Bool → Option ℕ) : Measure (R × ProcessTape) :=
  (ν.prod (Measure.infinitePi (fun i => parameterTapeLaw (κ i)))).map
    (fun z => (z.1,populationPath (pol z.1) z.2))

theorem parameterExperiment_probability {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν]
    (κ : ℕ → Measure unitInterval) [∀ i, IsProbabilityMeasure (κ i)]
    (pol : R → List Bool → Option ℕ) (hp : ∀ xs, Measurable (fun r => pol r xs)) :
    IsProbabilityMeasure (parameterExperimentLaw ν κ pol) :=
  (Measure.isProbabilityMeasure_map_iff
    (measurable_fst.prodMk (measurable_seeded_populationPath pol hp)).aemeasurable).2 inferInstance

theorem parameter_experiment_prefix {R : Type} [MeasurableSpace R]
    (ν : Measure R) (κ : ℕ → Measure unitInterval) [∀ i, IsProbabilityMeasure (κ i)]
    (pol : R → List Bool → Option ℕ) (hp : ∀ xs, Measurable (fun r => pol r xs)) (n : ℕ) :
    (parameterExperimentLaw ν κ pol).map (fun z => (z.1,processPrefix n z.2)) =
      (ν.prod (Measure.infinitePi (fun i => parameterTapeLaw (κ i)))).map
        (fun z => (z.1,(populationSimulation (pol z.1) n z.2).2)) := by
  rw [parameterExperimentLaw,Measure.map_map (measurable_jointPrefix n)
    (measurable_fst.prodMk (measurable_seeded_populationPath pol hp))]
  congr 1
  funext z
  exact Prod.ext rfl (populationPath_prefix _ _ _)

theorem countable_parameter_reference_kl (κ τ : ℕ → Measure unitInterval)
    [∀ i, IsProbabilityMeasure (κ i)] [∀ i, IsProbabilityMeasure (τ i)]
    (pol : List Bool → Option ℕ) (n : ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hlocal : ∀ i, ParameterReferenceBound (κ i) (τ i) K) :
    klDiv (finiteWeightMeasure (countableParameterWeight (fun i => quarterMix (κ i) (τ i)) pol (n := n)))
      (finiteWeightMeasure (countableParameterWeight (fun i => quarterMix (τ i) (κ i)) pol (n := n))) ≤
      ENNReal.ofReal ((8/3)*K*∑ w : Prefix n,
        countableParameterWeight (fun i => quarterMix (κ i) (τ i)) pol w*workOf w) := by
  let m := Tier5.coinCap n pol
  let cpol := Tier5.capPolicy m pol
  have h := finite_parameter_reference_kl (fun i : Fin m => κ i.val) (fun i : Fin m => τ i.val)
    cpol K hK (n := n) (by
      dsimp only
      intro i
      exact hlocal i.val _ (localSimulationProcedure i n cpol) n (localSimulationProcedure_capped i n cpol))
  dsimp only at h
  rw [parameter_work_real] at h
  exact h

/-- Countable labels and arbitrary private randomization preserve the same
coefficient and charge the actual physical prefix work. -/
theorem seeded_parameter_reference_kl {R : Type} [MeasurableSpace R]
    (ν : Measure R) [IsProbabilityMeasure ν]
    (κ τ : ℕ → Measure unitInterval)
    [∀ i, IsProbabilityMeasure (κ i)] [∀ i, IsProbabilityMeasure (τ i)]
    (pol : R → List Bool → Option ℕ) (hp : ∀ xs, Measurable (fun r => pol r xs))
    (n : ℕ) (K : ℝ) (hK : 0 ≤ K) (hlocal : ∀ i, ParameterReferenceBound (κ i) (τ i) K) :
    let P := parameterExperimentLaw ν (fun i => quarterMix (κ i) (τ i)) pol
    let Q := parameterExperimentLaw ν (fun i => quarterMix (τ i) (κ i)) pol
    klDiv (P.map (fun z => (z.1,processPrefix n z.2))) (Q.map (fun z => (z.1,processPrefix n z.2))) ≤
      ENNReal.ofReal ((8/3)*K*∫ z, workOf (processPrefix n z.2) ∂P) := by
  let ref := fun i => quarterMix (κ i) (τ i)
  let alt := fun i => quarterMix (τ i) (κ i)
  let P := parameterExperimentLaw ν ref pol
  let Q := parameterExperimentLaw ν alt pol
  let v := fun r (w : Prefix n) => countableParameterWeight ref (pol r) w
  let u := fun r (w : Prefix n) => countableParameterWeight alt (pol r) w
  let : IsProbabilityMeasure P := parameterExperiment_probability ν ref pol hp
  let : IsProbabilityMeasure Q := parameterExperiment_probability ν alt pol hp
  let PP := P.map (fun z => (z.1,processPrefix n z.2))
  let QQ := Q.map (fun z => (z.1,processPrefix n z.2))
  let : IsProbabilityMeasure PP :=
    (Measure.isProbabilityMeasure_map_iff (measurable_jointPrefix n).aemeasurable).2 inferInstance
  let : IsProbabilityMeasure QQ :=
    (Measure.isProbabilityMeasure_map_iff (measurable_jointPrefix n).aemeasurable).2 inferInstance
  have htotal (r : R) := countable_parameter_total ref (pol r) (n := n)
  have htotal' (r : R) := countable_parameter_total alt (pol r) (n := n)
  have hP : Tier5.FiniteKernelRealization ν PP v := by
    dsimp only [PP,P]
    rw [parameter_experiment_prefix ν ref pol hp n]
    exact seeded_parameter_prefix_kernel ν ref pol hp n
  have hQ : Tier5.FiniteKernelRealization ν QQ u := by
    dsimp only [QQ,Q]
    rw [parameter_experiment_prefix ν alt pol hp n]
    exact seeded_parameter_prefix_kernel ν alt pol hp n
  have hscalar (r : R) : klFT (v r) (u r) ≤ (8/3)*K*∑ w, v r w*workOf w := by
    have hsupp (w : Prefix n) (hw : u r w = 0) : v r w = 0 := by
      have h := countable_parameter_quarter_ratio κ τ (pol r) w
      change v r w ≤ 3^n * u r w at h
      rw [hw,mul_zero] at h
      exact le_antisymm h ((htotal r).1 w)
    have h := countable_parameter_reference_kl κ τ (pol r) n K hK hlocal
    rw [finite_weight_kl _ _ (htotal r).1 (htotal' r).1 (htotal r).2 (htotal' r).2 hsupp] at h
    exact (ENNReal.ofReal_le_ofReal_iff (by
      exact mul_nonneg (mul_nonneg (by norm_num) hK)
        (Finset.sum_nonneg fun w _ => mul_nonneg ((htotal r).1 w) (workOf_nonneg w)))).mp h
  have hb := Tier5.finite_kernel_kl_bound ν PP QQ v u
    (measurable_countableParameterWeight ref pol hp) (measurable_countableParameterWeight alt pol hp)
    (fun r => (htotal r).1) (fun r w =>
      (Finset.single_le_sum (fun j _ => (htotal r).1 j) (Finset.mem_univ w)).trans_eq (htotal r).2)
    (fun r => (htotal' r).1) (3^n) (by positivity)
    (fun r => countable_parameter_quarter_ratio κ τ (pol r))
    (fun r => countable_parameter_quarter_ratio τ κ (pol r)) hP hQ workOf ((8/3)*K) hscalar
  have hf : Measurable (fun z : R × Prefix n => workOf z.2) :=
    (measurable_of_countable workOf).comp measurable_snd
  have hw := hP (fun z => workOf z.2) hf
    ⟨n,fun z => by rw [abs_of_nonneg (workOf_nonneg z.2)]; exact workOf_le_length z.2⟩
  change (∫ z, workOf z.2 ∂P.map (fun z => (z.1,processPrefix n z.2))) = _ at hw
  rw [integral_map (measurable_jointPrefix n).aemeasurable hf.aestronglyMeasurable] at hw
  rw [← hw] at hb
  exact hb

end ThresholdHC.TypedConfidence
