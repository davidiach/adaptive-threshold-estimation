import ThresholdHC.ExplicitConstants.Specification
import ThresholdHC.OracleLower.Confidence
import ThresholdHC.Confidence.Full
import ThresholdHC.RareAboveTwo.Single
import ThresholdHC.RareAboveTwo.LowerSeparation

/-! Explicit constants: the hidden-model confidence coefficient `15/(256√2)`,
the rare-event lower coefficient `1/256` and the single-coin second moment
`28ρ`. Each proof instantiates the constant the existing proof already uses. -/
noncomputable section
namespace ThresholdHC.ExplicitConstants
open MeasureTheory ThresholdHC.Tier6 ThresholdHC.Confidence ThresholdHC.RareAboveTwo
open scoped ENNReal

theorem hidden_confidence : HiddenConfidenceLowerStatement := by
  intro R _ μ _ A B δ r hB hδ hδle hr hb hc
  exact OracleLower.hidden_confidence_lower μ A B δ r hB hδ hδle hr hb hc

theorem hidden_confidence_minimax : HiddenConfidenceMinimaxStatement := by
  intro μ _ B δ hB hδ hδle
  refine ⟨?_, (confidence_characterization μ B δ hB hδ hδle).2⟩
  apply le_sInf
  rintro t ⟨R, _, A, r, hr, hb, hc, rfl⟩
  exact ENNReal.ofReal_le_ofReal (OracleLower.hidden_confidence_lower μ A B δ r hB hδ hδle hr hb hc)

theorem rare_lower_256 : RareSupportedLower256Statement := by
  intro a ρ B ha ha1 hρ hρ1 hB μ _ hsupp R _ A hbudget
  have hB0 : 0 < B := by linarith
  have hsB : 0 < Real.sqrt B := Real.sqrt_pos.mpr hB0
  have hsρ : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hρ
  have hden : 0 < a*Real.sqrt B := mul_pos ha hsB
  let δ := aboveTwoRate a ρ B/32
  have hrate : 0 < aboveTwoRate a ρ B := lt_min hρ (div_pos hsρ hden)
  have hδ : 0 < δ := div_pos hrate (by norm_num)
  have hδρ : δ ≤ ρ/2 := by
    have h := min_le_left ρ (Real.sqrt ρ/(a*Real.sqrt B))
    change aboveTwoRate a ρ B ≤ ρ at h
    dsimp [δ]; linarith
  have hsmall : δ*(a*Real.sqrt B) ≤ Real.sqrt ρ/32 := by
    have h := (le_div_iff₀ hden).1 (min_le_right ρ (Real.sqrt ρ/(a*Real.sqrt B)))
    change aboveTwoRate a ρ B*(a*Real.sqrt B) ≤ Real.sqrt ρ at h
    dsimp [δ]; nlinarith only [h]
  have hsq := (sq_le_sq₀ (mul_pos hδ hden).le (by positivity : 0 ≤ Real.sqrt ρ/32)).2 hsmall
  simp only [mul_pow,div_pow,Real.sq_sqrt hB0.le,Real.sq_sqrt hρ.le] at hsq
  have hinfo : 64*δ^2*a^2*B ≤ ρ/8 := by nlinarith only [hsq,hρ.le]
  have h := rare_lower_at_separation μ A a ρ B δ ha1 hsupp hρ hρ1 hB0.le hδ hδρ hinfo hbudget
  convert h using 1
  congr 1
  dsimp [δ]; ring

theorem rare_minimax_256 : RareSupportedMinimax256Statement := by
  intro a ρ B ha ha1 hρ hρ1 hB μ _ hsupp
  apply le_sInf
  rintro t ⟨R, _, A, hA, rfl⟩
  exact rare_lower_256 a ρ B ha ha1 hρ hρ1 hB μ hsupp R A hA

theorem rare_single_coin_28 : RareSingleCoin28Statement := by
  refine ⟨observableEstimator, ?_, ?_⟩
  · intro a ρ j xs
    change policy a ρ j xs = none ∨ policy a ρ j xs = some 0
    unfold policy
    split_ifs <;> simp
  · intro α hα
    obtain ⟨W, hW, hwork⟩ := uniform_unbiased_work α hα
    refine ⟨W, hW, ?_⟩
    intro a ρ ha ha' hρ hρ' μ _ hm q hq
    have hρ1 : ρ ≤ 1 := by linarith
    refine ⟨(output_memLp μ α a ρ hα ha ha' hρ hρ1 hm q hq).integrable (by norm_num),
      output_mean μ α a ρ hα ha ha' hρ hρ1 hm q hq,
      output_second_moment μ α a ρ hα ha ha' hρ hρ1 hm q hq, ?_⟩
    rw [expectedWork_eq]
    exact hwork a ρ ha ha' hρ hρ1 μ hm q hq

end ThresholdHC.ExplicitConstants
