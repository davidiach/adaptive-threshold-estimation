import ThresholdHC.PsiSharpness.TwoAtom
import ThresholdHC.PsiSharpness.OccupiedBands

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.PsiSharpness
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.PsiClosedForm

/-- A concrete sharp example: rarity `1/5`, gaps `1/8` and `1/4`, budget
`1024`. In particular the equality target has admissible instances. -/
theorem sharp_example :
    let d₁ : Gap := ⟨1/8, by norm_num, by norm_num⟩
    let d₂ : Gap := ⟨1/4, by norm_num, by norm_num⟩
    rarePsi (twoAtomLaw (1/5) d₁ d₂) (1/5) (1/32) = ENNReal.ofReal (Real.sqrt 2 / 20) ∧
    quantileZero (twoAtomLaw (1/5) d₁ d₂) (1/5) 1024 = ENNReal.ofReal (1/10) := by
  dsimp only
  have hs : Real.sqrt (1024 : ℝ) = 32 := by
    apply (Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)).2
    norm_num
  have h := two_atom_sharpness (1/5) 1024
    ⟨1/8, by norm_num, by norm_num⟩ ⟨1/4, by norm_num, by norm_num⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [hs])
  norm_num [twoAtomLaw, hs, div_eq_mul_inv, mul_assoc] at h ⊢
  exact ⟨h.1, h.2.1⟩

end ThresholdHC.PsiSharpness
