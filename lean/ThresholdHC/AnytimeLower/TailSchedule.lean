
import ThresholdHC.AnytimeLower.TailFamily
import ThresholdHC.AnytimeLower.TestingSchedule

noncomputable section
open MeasureTheory Real Set Filter
open scoped ENNReal Topology
namespace ThresholdHC.AnytimeLower
open ThresholdHC.Tier3 ThresholdHC.Tier6

/-- An explicit monotone integer-budget schedule. The information and
nonsummability premises have both been discharged for the constructed priors. -/
theorem tail_scheduled_frequently {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    (H : ∀ n, R × Prefix n → ℝ) (hH : ∀ n, Measurable (H n))
    {τ ρ δ : ℝ} (hτ : 0 < τ) (hτq : τ ≤ 1/4)
    (hμ : 0 < μ {d : Gap | (d:ℝ) ≤ τ})
    (hrare : μ.real {d : Gap | (d:ℝ) ≤ τ} ≤ ρ)
    (hd : 0 ≤ δ ∧ δ ≤ 1/2) (t : ℕ → ℝ) (hacc : OnlineAccuracy μ A H ρ δ t) :
    ∃ᶠ k in atTop, profileMass μ τ (selectedScale μ hτ hμ k)/256 ≤
      t (testingBudget δ (selectedScale μ hτ hμ) k) := by
  apply tail_profile_frequently μ A H hH hτ hτq hμ hrare hd t hacc
    (testingBudget δ (selectedScale μ hτ hμ))
  · exact testingBudget_mono (by linarith) _ (fun k => geometricScale_pos hτ _)
      (selectedScale_antitone μ hτ hμ)
  · exact testingBudget_not_summable (by linarith) _ (fun k => geometricScale_pos hτ _)

theorem tail_scheduled_unbounded {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    (H : ∀ n, R × Prefix n → ℝ) (hH : ∀ n, Measurable (H n))
    {τ ρ δ : ℝ} (hτ : 0 < τ) (hτq : τ ≤ 1/4)
    (hμ : 0 < μ {d : Gap | (d:ℝ) ≤ τ})
    (hrare : μ.real {d : Gap | (d:ℝ) ≤ τ} ≤ ρ)
    (hd : 0 ≤ δ ∧ δ ≤ 1/2) (t : ℕ → ℝ) (hacc : OnlineAccuracy μ A H ρ δ t)
    (M : ℕ) :
    ∃ k, M ≤ testingBudget δ (selectedScale μ hτ hμ) k ∧
      profileMass μ τ (selectedScale μ hτ hμ k)/256 ≤
        t (testingBudget δ (selectedScale μ hτ hμ) k) := by
  have hf := tail_scheduled_frequently μ A H hH hτ hτq hμ hrare hd t hacc
  have ht := testingBudget_tendsto (by linarith : δ < 1) _
    (fun k => geometricScale_pos hτ (tailDropIndex μ hτ hμ k))
    (selectedScale_antitone μ hτ hμ)
  have he := ht.eventually (eventually_ge_atTop M)
  obtain ⟨k,hk,hM⟩ := (hf.and_eventually he).exists
  exact ⟨k,hM,hk⟩

end ThresholdHC.AnytimeLower
