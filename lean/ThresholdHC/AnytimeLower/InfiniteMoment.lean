
import ThresholdHC.AnytimeLower.TailSchedule
import ThresholdHC.AnytimeLower.TailRegion

noncomputable section
open MeasureTheory Real Set Filter
open scoped ENNReal Topology
namespace ThresholdHC.AnytimeLower
open ThresholdHC.Tier3 ThresholdHC.Tier6

/-- Every positive-gap law with infinite inverse moment supplies a single
explicit rare-prior family and arbitrarily late physical budgets at which
simultaneous accuracy forces the capped inverse-gap mass lower bound. -/
theorem infiniteMoment_unbounded {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ]
    (hI : ¬Integrable (fun d : Gap => (d:ℝ)⁻¹) μ)
    (A : AdaptiveEstimator R) (H : ∀ n, R × Prefix n → ℝ)
    (hH : ∀ n, Measurable (H n)) {ρ δ : ℝ} (hρ : 0 < ρ)
    (hd : 0 ≤ δ ∧ δ ≤ 1/2) (t : ℕ → ℝ) (hacc : OnlineAccuracy μ A H ρ δ t) :
    ∃ (τ : ℝ) (hτ : 0 < τ) (hμ : 0 < μ {d : Gap | (d:ℝ) ≤ τ}),
      τ ≤ 1/4 ∧ μ.real {d : Gap | (d:ℝ) ≤ τ} ≤ ρ/2 ∧
      ∀ M : ℕ, ∃ k, M ≤ testingBudget δ (selectedScale μ hτ hμ) k ∧
        profileMass μ τ (selectedScale μ hτ hμ k)/256 ≤
          t (testingBudget δ (selectedScale μ hτ hμ) k) := by
  obtain ⟨τ,hτ,hτq,hμ,hm⟩ := exists_smallGapRegion μ hI (show 0 < ρ/2 by positivity)
  refine ⟨τ,hτ,hμ,hτq,hm,?_⟩
  intro M
  exact tail_scheduled_unbounded μ A H hH hτ hτq hμ
    (hm.trans (by linarith)) hd t hacc M

end ThresholdHC.AnytimeLower
