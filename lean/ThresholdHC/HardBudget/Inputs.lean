import ThresholdHC.HardBudget.Controller
import ThresholdHC.BlindUpper.InfiniteArrays

noncomputable section
open MeasureTheory
namespace ThresholdHC.HardBudget
open ThresholdHC.Tier6 ThresholdHC.BlindUpper ThresholdHC.ObservableSimulation
variable {R : ℕ → Type} [∀ j, MeasurableSpace (R j)]

/-- A dependent seed family can be zipped with a homogeneous family of tape
tables by first drawing iid whole seed arrays and retaining their diagonal. -/
private theorem zip_seeds {T : Type} [MeasurableSpace T]
    (μ : ∀ j, Measure (R j)) [∀ j, IsProbabilityMeasure (μ j)]
    (ν : ℕ → Measure T) [∀ j, IsProbabilityMeasure (ν j)] :
    ((Measure.infinitePi μ).prod (Measure.infinitePi ν)).map (fun z i => (z.1 i,z.2 i)) =
      Measure.infinitePi (fun i => (μ i).prod (ν i)) := by
  let γ := Measure.infinitePi μ
  let diag (v : ℕ → (∀ i, R i)) := fun i => v i i
  have hm : Measurable diag := Measurable.of_eval fun i => (measurable_pi_apply i).comp (measurable_pi_apply i)
  have hd : (Measure.infinitePi (fun _ : ℕ => γ)).map diag = γ := by
    rw [show diag = fun v : ℕ → (∀ i, R i) => fun i => (fun u : ∀ j, R j => u i) (v i) from rfl,
      Measure.infinitePi_map_pi _ (fun i => measurable_pi_apply i)]
    simp only [γ,Measure.infinitePi_map_eval]
  let d (z : (ℕ → (∀ i, R i)) × (ℕ → T)) := (diag z.1,z.2)
  let zipD (z : (∀ i, R i) × (ℕ → T)) := fun i => (z.1 i,z.2 i)
  let zipA (z : (ℕ → (∀ i, R i)) × (ℕ → T)) := fun i => (z.1 i,z.2 i)
  let select (u : ℕ → (∀ i, R i) × T) := fun i => ((u i).1 i,(u i).2)
  have hd' : Measurable d := (hm.comp measurable_fst).prodMk measurable_snd
  have hzd : Measurable zipD := by dsimp [zipD]; fun_prop
  have hza : Measurable zipA := by dsimp [zipA]; fun_prop
  have hs : Measurable select := by dsimp [select]; fun_prop
  have hmap : ((Measure.infinitePi (fun _ : ℕ => γ)).prod (Measure.infinitePi ν)).map d =
      γ.prod (Measure.infinitePi ν) := by
    change Measure.map (Prod.map diag id) _ = _
    rw [← Measure.map_prod_map _ _ hm measurable_id,hd,Measure.map_id]
  change (γ.prod (Measure.infinitePi ν)).map zipD = _
  rw [← hmap,Measure.map_map hzd hd',show zipD ∘ d = select ∘ zipA from rfl,← Measure.map_map hs hza]
  have hz := infinitePi_zip (fun _ : ℕ => γ) ν
  change Measure.map zipA _ = _ at hz
  rw [hz,show select = fun u : ℕ → (∀ i, R i) × T => fun i =>
    Prod.map (fun v : ∀ j, R j => v i) id (u i) from rfl,
    Measure.infinitePi_map_pi _ (fun i => (measurable_pi_apply i).prodMap measurable_id)]
  simp only [← Measure.map_prod_map _ _ (measurable_pi_apply _) measurable_id,γ,Measure.infinitePi_map_eval,
    Measure.map_id]

def stageInputs (z : (∀ j, R j) × Table) : ∀ j, R j × Table :=
  fun i => (z.1 i,fun c => z.2 (Nat.pair i c))

theorem stageInputs_preserving (base : ∀ j, AdaptiveEstimator (R j)) (M : ℝ) (k : ℕ)
    (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    MeasurePreserving stageInputs (originalSimulationLaw μ (estimator base M k) q)
      (Measure.infinitePi (fun i => originalSimulationLaw μ (base i) q)) := by
  have hm : Measurable (stageInputs (R := R)) := by unfold stageInputs; fun_prop
  refine ⟨hm,?_⟩
  let ν := originalPopulationTapeLaw μ q
  let f (z : (∀ j, R j) × (ℕ → Table)) := fun i => (z.1 i,z.2 i)
  change ((Measure.infinitePi (fun i => (base i).randomLaw)).prod (Measure.infinitePi (fun _ : ℕ => ν))).map
    (f ∘ Prod.map id splitPairArray) = _
  rw [← Measure.map_map (show Measurable f by dsimp [f]; fun_prop) (measurable_id.prodMap measurable_splitPairArray),
    ← Measure.map_prod_map _ _ measurable_id measurable_splitPairArray,Measure.map_id,splitPairArray_map]
  exact zip_seeds (fun j => (base j).randomLaw) _

end ThresholdHC.HardBudget
