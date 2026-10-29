import ThresholdHC.RareAboveTwo.Realization

/-! The complete observable single-coin target, with no supplied moment or work assumptions. -/
noncomputable section
namespace ThresholdHC.RareAboveTwo
open MeasureTheory ThresholdHC.Tier6

theorem rare_single_coin : RareSingleCoinStatement := by
  refine ⟨28,by norm_num,observableEstimator,?_,?_⟩
  · intro a ρ j xs
    change policy a ρ j xs = none ∨ policy a ρ j xs = some 0
    unfold policy
    split_ifs <;> simp
  · intro α hα
    obtain ⟨W,hW,hwork⟩ := uniform_unbiased_work α hα
    refine ⟨W,hW,?_⟩
    intro a ρ ha ha' hρ hρ' μ _ hm q hq
    have hρ1 : ρ ≤ 1 := by linarith
    refine ⟨(output_memLp μ α a ρ hα ha ha' hρ hρ1 hm q hq).integrable (by norm_num),
      output_mean μ α a ρ hα ha ha' hρ hρ1 hm q hq,
      output_second_moment μ α a ρ hα ha ha' hρ hρ1 hm q hq,?_⟩
    rw [expectedWork_eq]
    exact hwork a ρ ha ha' hρ hρ1 μ hm q hq

end ThresholdHC.RareAboveTwo
