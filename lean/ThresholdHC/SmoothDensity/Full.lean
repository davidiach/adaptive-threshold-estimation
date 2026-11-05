import ThresholdHC.SmoothDensity.Upper
import ThresholdHC.SmoothDensity.Unbiased
import ThresholdHC.SmoothDensity.LatentLaw

noncomputable section
open MeasureTheory
namespace ThresholdHC.SmoothDensity
open ThresholdHC.Tier6

/-- The manuscript's smooth-density result in the original adaptive experiment.
The upper estimator family is chosen before the density, and the lower and
unbiased conclusions allow arbitrary measurable private randomness. -/
theorem smooth_density_robustness (s : ℕ) :
    ∃ M₀ c ε₀ : ℝ, 1 ≤ M₀ ∧ 0 < c ∧ 0 < ε₀ ∧
      (∀ M B ε δ : ℝ, M₀ ≤ M → 0 < ε → ε ≤ ε₀ → 0 < δ → δ ≤ 1 / 4 →
        ∀ (R : Type) [MeasurableSpace R] (A : AdaptiveEstimator R),
          FitsClass s M B ε δ A →
            c * (ε ^ 2)⁻¹ * Real.log (1 / ε) ^ 2 * Real.log (1 / δ) ≤ B) ∧
      (∃ (R : Type) (_ : MeasurableSpace R) (rule : ℝ → ℝ → ℝ → AdaptiveEstimator R),
        ∀ M ε δ : ℝ, M₀ ≤ M → 0 < ε → ε ≤ ε₀ → 0 < δ → δ ≤ 1 / 4 →
          FitsClass s M ((65536 * M) ^ 2 * (ε ^ 2)⁻¹ *
            Real.log (1 / ε) ^ 2 * Real.log (1 / δ)) ε δ (rule M ε δ)) ∧
      (∀ M : ℝ, M₀ ≤ M → ∀ (R : Type) [MeasurableSpace R] (A : AdaptiveEstimator R)
        (V W : ℝ), 0 ≤ V → 0 ≤ W → ¬ FiniteUnbiasedClass s M V W A) := by
  obtain ⟨Ml,c,e,_,hc,he,hl⟩ := smooth_confidence_lower s
  obtain ⟨Mu,_,hu⟩ := smooth_unbiased_impossible s
  obtain ⟨R,mR,rule,hr⟩ := smooth_confidence_upper s
  let M₀ := max 1 (max Ml Mu)
  let ε₀ := min e (Real.exp (-16))
  have hM₀ : 1 ≤ M₀ := le_max_left _ _
  have hMl : Ml ≤ M₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hMu : Mu ≤ M₀ := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨M₀,c,ε₀,hM₀,hc,lt_min he (Real.exp_pos _),?_,?_,?_⟩
  · intro M B ε δ hM hε he' hδ hd R _ A hA
    exact hl M B ε δ (hMl.trans hM) hε (he'.trans (min_le_left _ _)) hδ hd R A hA
  · refine ⟨R,mR,rule,?_⟩
    intro M ε δ hM hε he' hδ hd
    exact hr M ε δ (hM₀.trans hM) hε (he'.trans (min_le_right _ _)) hδ hd
  · intro M hM R _ A V W hV hW
    exact hu M (hMu.trans hM) R A V W hV hW

end ThresholdHC.SmoothDensity
