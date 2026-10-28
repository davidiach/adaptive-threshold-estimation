import ThresholdHC.CriticalEntropy.FinitePopulation
import ThresholdHC.Tier5.FiniteCreation

noncomputable section

namespace ThresholdHC.CriticalEntropy
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
local instance creationPopulationSymbolSpace : MeasurableSpace (Option Bool) := ⊤

/-- Observable finite-prefix weights after integrating the iid infinite hidden
magnitude environment. The policy may use any natural-number coin label. -/
def creationPopulationWeight {D : Type} [MeasurableSpace D] {n : ℕ}
    (μ : Measure D) (pol : List Bool → Option ℕ) (d q : D → ℝ)
    (w : Fin n → Option Bool) : ℝ :=
  ∫ x : ℕ → D, Tier5.creationLaw pol (fun i => d (x i)) (fun i => q (x i)) w
    ∂Measure.infinitePi (fun _ => μ)

theorem creationPopulationWeight_eq_finite {D : Type} [MeasurableSpace D] {n : ℕ}
    (μ : Measure D) [IsProbabilityMeasure μ] (pol : List Bool → Option ℕ)
    (d q : D → ℝ) (hd : Measurable d) (hq : Measurable q) (w : Fin n → Option Bool) :
    creationPopulationWeight μ pol d q w =
      finitePopulationWeight μ (Tier5.capPolicy (Tier5.coinCap n pol) pol) d (fun _ => q) w := by
  let m := Tier5.coinCap n pol
  let F (x : Fin m → D) := ThresholdHC.transcriptLaw (Tier5.capPolicy m pol)
    (fun i => d (x i)) (fun i => q (x i)) w
  have hm : Measurable F := Tier5.measurable_variable_transcriptLaw
    (fun _ : Fin m → D => Tier5.capPolicy m pol)
    (fun xs a => by by_cases h : Tier5.capPolicy m pol xs = a <;> simp [h])
    (fun x i => d (x i)) (fun x i => q (x i))
    (fun i => hd.comp (measurable_pi_apply i))
    (fun i => hq.comp (measurable_pi_apply i)) w
  have hmap : (Measure.infinitePi (fun _ : ℕ => μ)).map (fun (x : ℕ → D) (i : Fin m) => x i.val) =
      Measure.pi (fun _ : Fin m => μ) := by
    rw [Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective,Measure.infinitePi_eq_pi]
  have hme : Measurable (fun x : ℕ → D => fun i : Fin m => x i.val) :=
    Measurable.of_eval (fun i => measurable_pi_apply i.val)
  change (∫ x, F (fun i => x i.val) ∂Measure.infinitePi (fun _ : ℕ => μ)) =
    ∫ x, F x ∂Measure.pi (fun _ : Fin m => μ)
  rw [← hmap,integral_map hme.aemeasurable hm.aestronglyMeasurable]

theorem measurable_creationPopulationWeight {D R : Type}
    [MeasurableSpace D] [MeasurableSpace R] {n : ℕ}
    (μ : Measure D) [IsProbabilityMeasure μ] (pol : R → List Bool → Option ℕ)
    (hp : Tier5.MeasurableCreationPolicy pol) (d q : D → ℝ)
    (hd : Measurable d) (hq : Measurable q) (w : Fin n → Option Bool) :
    Measurable (fun r => creationPopulationWeight μ (pol r) d q w) := by
  have hm : Measurable (fun z : R × (ℕ → D) => Tier5.creationLaw (pol z.1)
      (fun i => d (z.2 i)) (fun i => q (z.2 i)) w) :=
    Tier5.measurable_creationLaw (fun z : R × (ℕ → D) => pol z.1)
      (fun xs a => measurable_fst (hp xs a))
      (fun z i => d (z.2 i)) (fun z i => q (z.2 i))
      (fun i => hd.comp ((measurable_pi_apply i).comp measurable_snd))
      (fun i => hq.comp ((measurable_pi_apply i).comp measurable_snd)) w
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem creationPopulationWeight_total {D : Type} [MeasurableSpace D] {n : ℕ}
    (μ : Measure D) [IsProbabilityMeasure μ] (pol : List Bool → Option ℕ)
    (d q : D → ℝ) (hdm : Measurable d) (hqm : Measurable q)
    (hd : ∀ x, 0 ≤ d x ∧ d x ≤ 1/2) (hq : ∀ x, 0 ≤ q x ∧ q x ≤ 1) :
    (∀ w : Fin n → Option Bool, 0 ≤ creationPopulationWeight μ pol d q w) ∧
      (∑ w : Fin n → Option Bool, creationPopulationWeight μ pol d q w) = 1 := by
  simp_rw [creationPopulationWeight_eq_finite μ pol d q hdm hqm]
  exact finite_population_total μ _ d (fun _ => q) hdm (fun _ => hqm) hd (fun _ => hq)

end ThresholdHC.CriticalEntropy
