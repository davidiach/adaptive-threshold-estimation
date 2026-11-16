import ThresholdHC.ArbitraryLawController.Rate

/-! The fixed arbitrary-law controller in the original observable experiment.
The law enters its deterministic onset and theorem only, never its procedure. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal
namespace ThresholdHC.ArbitraryLawController
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.HardBudget
open ThresholdHC.ObservableSimulation

def successEvent (μ : Measure Gap) (q : SignLaw) (ρ δ : ℝ) (H : ℕ) :
    Set (Seed ρ δ × Table) :=
  {z | (∀ B : ℕ, (interval ρ δ B z).1 ≤ signMean μ q.val ∧
      signMean μ q.val ≤ (interval ρ δ B z).2) ∧
    ∀ B : ℕ, H ≤ B → Anytime.halfWidth (interval ρ δ B z) ≤
      2 ^ 32 * radiusCoefficient *
        (EntropyTail.selection μ ρ ((B : ℝ) / Anytime.inflation B δ)).toReal}

theorem measurableSet_successEvent (μ : Measure Gap) (q : SignLaw) (ρ δ : ℝ) (H : ℕ) :
    MeasurableSet (successEvent μ q ρ δ H) := by
  have hm (B : ℕ) : Measurable (interval ρ δ B) := measurable_observedInterval _ _ _
  have hw (B : ℕ) : Measurable (fun z => Anytime.halfWidth (interval ρ δ B z)) := by
    unfold Anytime.halfWidth
    exact (measurable_const.max ((hm B).snd.sub (hm B).fst)).div_const 2
  unfold successEvent
  simp only [Set.ofPred_and, Set.ofPred_forall]
  apply MeasurableSet.inter
  · apply MeasurableSet.iInter
    intro B
    exact (measurableSet_le (hm B).fst measurable_const).inter
      (measurableSet_le measurable_const (hm B).snd)
  · apply MeasurableSet.iInter
    intro B
    apply MeasurableSet.iInter
    intro _
    exact measurableSet_le (hw B) measurable_const

theorem controller_paused (ρ δ : ℝ) {B C : ℕ}
    (h : stageCount (B : ℝ) = stageCount (C : ℝ)) (upper : Bool) :
    controller ρ δ B upper = controller ρ δ C upper := by
  simp only [controller, h]

/-- All caps and prefix consistency are unconditional. For each arbitrary
positive-gap law there is a deterministic finite onset, common to every sign
law. One event protects coverage at every integer budget and the eventual
oracle width. No statistical or execution guarantee is assumed of a stage. -/
theorem arbitrary_law_controller {ρ δ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (hd : 0 < δ) (hu : δ ≤ 1/4) :
    (∀ B : ℕ, ∀ upper : Bool, PathwiseCap (controller ρ δ B upper) B) ∧
    (∀ B C : ℕ, B ≤ C → ∀ (upper upper' : Bool) (r : Seed ρ δ) (xs : List Bool),
      xs.length < spent (stage ρ δ) (stageCount (B : ℝ)) →
      (controller ρ δ C upper').policy r xs = (controller ρ δ B upper).policy r xs) ∧
    (∀ B C : ℕ, B ≤ C → ∀ z : Seed ρ δ × Table,
      (interval ρ δ B z).1 ≤ (interval ρ δ C z).1 ∧
        (interval ρ δ C z).2 ≤ (interval ρ δ B z).2) ∧
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ], ∃ H : ℕ, 1 ≤ H ∧
      ∀ q : SignLaw, RarePrior μ ρ q →
        1 - ENNReal.ofReal δ ≤ streamLaw μ q ρ δ (successEvent μ q ρ δ H) := by
  refine ⟨controller_cap ρ δ, fun _ _ h => controller_compatible ρ δ h,
    fun _ _ h => interval_nested ρ δ h, ?_⟩
  intro μ hμ
  obtain ⟨H, hH, hw⟩ := eventual_oracle_width μ hρ hρ4 hd hu
  refine ⟨H, hH, fun q hq => (goodEvent_probability μ q hρ hρ4 hd hu hq).trans ?_⟩
  apply measure_mono
  intro z hz
  exact ⟨goodEvent_coverage μ q ρ δ hq hz, hw q z hz⟩

/-- On the same single event, every observation-dependent stopping budget
has coverage and, when it is past the onset, the oracle width. No restriction
on how the stopping budget depends on observations is needed. -/
theorem successEvent_stopping (μ : Measure Gap) (q : SignLaw) (ρ δ : ℝ) (H : ℕ)
    {z : Seed ρ δ × Table} (hz : z ∈ successEvent μ q ρ δ H)
    (τ : (Seed ρ δ × Table) → ℕ) :
    ((interval ρ δ (τ z) z).1 ≤ signMean μ q.val ∧
      signMean μ q.val ≤ (interval ρ δ (τ z) z).2) ∧
    (H ≤ τ z → Anytime.halfWidth (interval ρ δ (τ z) z) ≤
      2 ^ 32 * radiusCoefficient *
        (EntropyTail.selection μ ρ (((τ z : ℕ) : ℝ) / Anytime.inflation (τ z) δ)).toReal) :=
  ⟨hz.1 (τ z), hz.2 (τ z)⟩

end ThresholdHC.ArbitraryLawController
