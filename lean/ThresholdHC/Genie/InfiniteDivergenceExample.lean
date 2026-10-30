import ThresholdHC.Genie.InfiniteDivergence
import ThresholdHC.Genie.SingularFlowBound

/-! The paper's explicit counterexample: every finite-cap reveal ratio is
infinite although the ordinary infinite-cap ratio is at most three quarters. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace ThresholdHC.Genie
open ThresholdHC.Tier6 ThresholdHC.StoppingProgram

theorem singularExample_no_pointwise_convergence :
    ¬Tendsto (fun n : ℕ => genieInformationRatio uniformGapLaw (n+1) singularExamplePriors)
      atTop (𝓝 (infiniteInformationRatio uniformGapLaw singularExamplePriors)) := by
  intro h
  have he : (fun n : ℕ => genieInformationRatio uniformGapLaw (n+1) singularExamplePriors) =
      (fun _ : ℕ => (⊤ : ℝ≥0∞)) := funext (fun n => singularExample_genie_top (n+1) (by omega))
  rw [he] at h
  have ht : infiniteInformationRatio uniformGapLaw singularExamplePriors = ⊤ :=
    tendsto_nhds_unique h tendsto_const_nhds
  exact (ne_top_of_le_ne_top ENNReal.ofReal_ne_top singular_infiniteInformationRatio_bound) ht

theorem infinite_divergence_counterexample :
    Admissible uniformGapLaw (1/4) singularExamplePriors ∧
    latentDivergence uniformGapLaw singularExamplePriors = ⊤ ∧
    (∀ N : ℕ, 0 < N → genieInformationRatio uniformGapLaw N singularExamplePriors = ⊤) ∧
    infiniteInformationRatio uniformGapLaw singularExamplePriors ≤ ENNReal.ofReal (3/4) ∧
    ¬Tendsto (fun n : ℕ => genieInformationRatio uniformGapLaw (n+1) singularExamplePriors)
      atTop (𝓝 (infiniteInformationRatio uniformGapLaw singularExamplePriors)) :=
  ⟨singularExample_admissible,singularExample_latentDivergence,singularExample_genie_top,
    singular_infiniteInformationRatio_bound,singularExample_no_pointwise_convergence⟩

end ThresholdHC.Genie
