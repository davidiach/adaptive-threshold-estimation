import ThresholdHC.ArbitraryLawController.Stages
import ThresholdHC.ArbitraryLawController.Intervals
import ThresholdHC.Anytime.Coverage

noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal
namespace ThresholdHC.ArbitraryLawController
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.HardBudget
open ThresholdHC.ArbitraryLawAdaptation ThresholdHC.RobustContinuation
open ThresholdHC.ObservableSimulation

abbrev Seed (ρ δ : ℝ) := ∀ s, StageSeed ρ δ s

def controller (ρ δ : ℝ) (B : ℕ) (upper : Bool) : AdaptiveEstimator (Seed ρ δ) :=
  endpoint (stage ρ δ) ρ (stageCount (B : ℝ)) upper

def interval (ρ δ : ℝ) (B : ℕ) (z : Seed ρ δ × Table) : ℝ × ℝ :=
  observedInterval (stage ρ δ) ρ (stageCount (B : ℝ)) z

def streamLaw (μ : Measure Gap) (q : SignLaw) (ρ δ : ℝ) : Measure (Seed ρ δ × Table) :=
  Anytime.streamLaw μ (fun s => (stage ρ δ s).endpoint false) q

instance streamLaw_probability (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (ρ δ : ℝ) : IsProbabilityMeasure (streamLaw μ q ρ δ) := by
  unfold streamLaw
  infer_instance

theorem controller_original_law (μ : Measure Gap) (q : SignLaw) (ρ δ : ℝ)
    (B : ℕ) (upper : Bool) :
    originalSimulationLaw μ (controller ρ δ B upper) q = streamLaw μ q ρ δ := rfl

theorem controller_cap (ρ δ : ℝ) (B : ℕ) (upper : Bool) :
    PathwiseCap (controller ρ δ B upper) B := by
  simpa only [Nat.floor_natCast, controller] using
    endpoint_budget_cap (stage ρ δ) ρ (stage_cap ρ δ) (B : ℝ) upper

theorem stageCount_mono {B C : ℕ} (h : B ≤ C) : stageCount (B : ℝ) ≤ stageCount (C : ℝ) := by
  have hf : paid (stageCount (B : ℝ)) ≤ ⌊(C : ℝ)⌋₊ := by
    simpa only [Nat.floor_natCast] using (paid_fits (B : ℝ)).trans (by simpa using h)
  exact Nat.le_findGreatest ((index_le_paid _).trans hf) hf

theorem controller_compatible (ρ δ : ℝ) {B C : ℕ} (h : B ≤ C)
    (upper upper' : Bool) (r : Seed ρ δ) (xs : List Bool)
    (hx : xs.length < spent (stage ρ δ) (stageCount (B : ℝ))) :
    (controller ρ δ C upper').policy r xs = (controller ρ δ B upper).policy r xs :=
  endpoint_policy_compatible _ _ (stageCount_mono h) upper upper' r xs hx

theorem interval_nested (ρ δ : ℝ) {B C : ℕ} (h : B ≤ C) (z : Seed ρ δ × Table) :
    (interval ρ δ B z).1 ≤ (interval ρ δ C z).1 ∧
      (interval ρ δ C z).2 ≤ (interval ρ δ B z).2 := by
  simp only [interval, observedInterval_eq]
  exact tableInterval_nested _ _ _ _ (stageCount_mono h)

def goodEvent (μ : Measure Gap) (q : SignLaw) (ρ δ : ℝ) : Set (Seed ρ δ × Table) :=
  {z | ∀ s, stageInputs z s ∉ stageBad μ q ρ δ s}

theorem measurableSet_goodEvent (μ : Measure Gap) (q : SignLaw) (ρ δ : ℝ) :
    MeasurableSet (goodEvent μ q ρ δ) := by
  simp only [goodEvent, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro s
  exact (measurableSet_stageBad μ q ρ δ s).compl.preimage (by unfold stageInputs; fun_prop)

theorem goodEvent_failure (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) {ρ δ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (hd : 0 < δ) (hu : δ ≤ 1/4) (hq : RarePrior μ ρ q) :
    streamLaw μ q ρ δ (goodEvent μ q ρ δ)ᶜ ≤ ENNReal.ofReal δ := by
  let E (s : ℕ) := {z : Seed ρ δ × Table | stageInputs z s ∈ stageBad μ q ρ δ s}
  have he : (goodEvent μ q ρ δ)ᶜ = ⋃ s, E s := by
    ext z
    simp only [goodEvent, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_not, Set.mem_iUnion, E]
  rw [he]
  apply Anytime.simultaneous_coverage _ E hd.le
  intro s
  let base := fun j => (stage ρ δ j).endpoint false
  let P := fun j => originalSimulationLaw μ (base j) q
  let (j : ℕ) : IsProbabilityMeasure (P j) := by dsimp [P, originalSimulationLaw]; infer_instance
  have hp := stageInputs_preserving base ρ 0 μ q
  have hcoord := (measurePreserving_eval_infinitePi P s).comp hp
  change (originalSimulationLaw μ (estimator base ρ 0) q)
    ((Function.eval s ∘ stageInputs) ⁻¹' stageBad μ q ρ δ s) ≤ _
  rw [hcoord.measure_preimage (measurableSet_stageBad μ q ρ δ s).nullMeasurableSet]
  exact stage_failure hρ hρ4 hd hu s μ q hq

theorem goodEvent_probability (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) {ρ δ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (hd : 0 < δ) (hu : δ ≤ 1/4) (hq : RarePrior μ ρ q) :
    1 - ENNReal.ofReal δ ≤ streamLaw μ q ρ δ (goodEvent μ q ρ δ) := by
  have hb := goodEvent_failure μ q hρ hρ4 hd hu hq
  rw [measure_compl (measurableSet_goodEvent μ q ρ δ) (measure_ne_top _ _), measure_univ] at hb
  apply tsub_le_iff_left.mpr
  simpa only [add_comm] using tsub_le_iff_left.mp hb

theorem goodEvent_pilot (μ : Measure Gap) (q : SignLaw) (ρ δ : ℝ)
    {z : Seed ρ δ × Table} (hz : z ∈ goodEvent μ q ρ δ) {s : ℕ} (hs : 1 ≤ depth δ s) :
    pilotGood μ ρ δ s (readBlock (stage ρ δ s).pilotCost (stage ρ δ s).pilot
      ((stageInputs z s).2 ∘ Nat.pair 0)).1 := by
  by_contra h
  exact hz s (Or.inl ⟨by omega, h⟩)

theorem goodEvent_coverage (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (ρ δ : ℝ) (hq : RarePrior μ ρ q) {z : Seed ρ δ × Table}
    (hz : z ∈ goodEvent μ q ρ δ) (B : ℕ) :
    (interval ρ δ B z).1 ≤ signMean μ q.val ∧ signMean μ q.val ≤ (interval ρ δ B z).2 := by
  rw [interval, observedInterval_eq]
  apply tableInterval_coverage _ _ _ _ _ ⟨(signMean_bounds μ q).1, hq⟩
  intro s
  have h := fun he => hz s (Or.inr he)
  change ¬(signMean μ q.val < _ ∨ _ < signMean μ q.val) at h
  exact ⟨le_of_not_gt (fun h' => h (Or.inl h')), le_of_not_gt (fun h' => h (Or.inr h'))⟩

theorem stopping_budget_coverage (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) {ρ δ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (hd : 0 < δ) (hu : δ ≤ 1/4) (hq : RarePrior μ ρ q)
    (τ : (Seed ρ δ × Table) → ℕ) :
    streamLaw μ q ρ δ {z | ¬((interval ρ δ (τ z) z).1 ≤ signMean μ q.val ∧
      signMean μ q.val ≤ (interval ρ δ (τ z) z).2)} ≤ ENNReal.ofReal δ := by
  apply (measure_mono (t := (goodEvent μ q ρ δ)ᶜ) ?_).trans
    (goodEvent_failure μ q hρ hρ4 hd hu hq)
  intro z hz hg
  exact hz (goodEvent_coverage μ q ρ δ hq hg (τ z))

end ThresholdHC.ArbitraryLawController
