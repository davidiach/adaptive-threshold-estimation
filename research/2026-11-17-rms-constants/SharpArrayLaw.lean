import Mathlib.Probability.ProductMeasure

/-! Independent per-coin randomization commutes with an iid population. -/
noncomputable section
namespace ThresholdHC.SharpRMS
open MeasureTheory

theorem zip_population {A B : Type} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    MeasurePreserving (fun z : (ℕ → A) × (ℕ → B) => fun i => (z.1 i,z.2 i))
      ((Measure.infinitePi (fun _ : ℕ => μ)).prod (Measure.infinitePi (fun _ : ℕ => ν)))
      (Measure.infinitePi (fun _ : ℕ => μ.prod ν)) := by
  have hm : Measurable (fun z : (ℕ → A) × (ℕ → B) => fun i => (z.1 i,z.2 i)) :=
    Measurable.of_eval (fun i => ((measurable_pi_apply i).comp measurable_fst).prodMk
      ((measurable_pi_apply i).comp measurable_snd))
  refine ⟨hm,(Measure.isProjectiveLimit_infinitePi (fun _ : ℕ => μ.prod ν)).unique ?_ |>.symm⟩
  intro J
  rw [Measure.map_map (Finset.measurable_restrict _) hm]
  have pa : MeasurePreserving J.restrict (Measure.infinitePi (fun _ : ℕ => μ)) (Measure.pi (fun _ : J => μ)) :=
    ⟨Finset.measurable_restrict _,Measure.infinitePi_map_restrict _⟩
  have pb : MeasurePreserving J.restrict (Measure.infinitePi (fun _ : ℕ => ν)) (Measure.pi (fun _ : J => ν)) :=
    ⟨Finset.measurable_restrict _,Measure.infinitePi_map_restrict _⟩
  exact ((measurePreserving_arrowProdEquivProdArrow A B J (fun _ => μ) (fun _ => ν)).symm.comp
    (pa.prod pb)).map_eq

theorem transform_population {A B C : Type} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : A × B → C) (hf : Measurable f) :
    ((Measure.infinitePi (fun _ : ℕ => μ)).prod (Measure.infinitePi (fun _ : ℕ => ν))).map
      (fun z i => f (z.1 i,z.2 i)) = Measure.infinitePi (fun _ : ℕ => (μ.prod ν).map f) := by
  have h := zip_population μ ν
  have hm : Measurable (fun x : ℕ → A × B => fun i => f (x i)) :=
    Measurable.of_eval (fun i => hf.comp (measurable_pi_apply i))
  rw [← Measure.infinitePi_map_pi (fun _ : ℕ => μ.prod ν) (fun _ => hf),← h.map_eq,
    Measure.map_map hm h.measurable]
  rfl

end ThresholdHC.SharpRMS
