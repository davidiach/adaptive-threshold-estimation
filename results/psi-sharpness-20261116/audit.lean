import ThresholdHC.PsiSharpness.Full
open MeasureTheory ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.PsiSharpness
open ThresholdHC.EntropyTailQuantile
open scoped ENNReal
example : OccupiedBandEntropyStatement := occupied_band_entropy
example : TwoAtomSharpnessStatement := two_atom_sharpness
example (ρ B : ℝ) (d₁ d₂ : Gap) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B)
    (hd : (d₂ : ℝ) = (d₁ : ℝ) * Real.sqrt ((1 - ρ) / ρ))
    (hh : 1 / Real.sqrt B ≤ (d₁ : ℝ) / 2) :
    let μ := ENNReal.ofReal ρ • Measure.dirac d₁ +
      ENNReal.ofReal (1 - ρ) • Measure.dirac d₂
    rarePsi μ ρ (1 / Real.sqrt B) =
      ENNReal.ofReal (Real.sqrt 2 * (1 / Real.sqrt B) * ρ / (d₁ : ℝ)) ∧
    (min (ENNReal.ofReal ρ)
      (ThresholdHC.EntropyTail.tailCost (quantileTail μ ρ) (1 / Real.sqrt B) +
        ENNReal.ofReal (1 / Real.sqrt B) *
          (ENNReal.ofReal ρ * ∫⁻ d, ENNReal.ofReal (((d : ℝ)⁻¹)^2)
            ∂quantileCore μ ρ) ^ (1/2 : ℝ))) =
      ENNReal.ofReal (2 * (1 / Real.sqrt B) * ρ / (d₁ : ℝ)) ∧
    (min (ENNReal.ofReal ρ)
      (ThresholdHC.EntropyTail.tailCost (quantileTail μ ρ) (1 / Real.sqrt B) +
        ENNReal.ofReal (1 / Real.sqrt B) *
          (ENNReal.ofReal ρ * ∫⁻ d, ENNReal.ofReal (((d : ℝ)⁻¹)^2)
            ∂quantileCore μ ρ) ^ (1/2 : ℝ))) =
      ENNReal.ofReal (Real.sqrt 2) * rarePsi μ ρ (1 / Real.sqrt B) :=
  two_atom_sharpness ρ B d₁ d₂ hρ hρ4 hB hd hh

example (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ : ℝ)
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) :
    (Function.support (bandCost (quantileCore μ ρ))).Finite ∧
    0 < (Function.support (bandCost (quantileCore μ ρ))).ncard ∧
    (∑' j : ℕ, Real.negMulLog
      (bandCost (quantileCore μ ρ) j /
        (∫⁻ d, ENNReal.ofReal (((d : ℝ)⁻¹)^2) ∂quantileCore μ ρ).toReal)) ≤
      Real.log (Function.support (bandCost (quantileCore μ ρ))).ncard ∧
    Real.log (Function.support (bandCost (quantileCore μ ρ))).ncard ≤
      Real.log (Real.logb 2 (1 / quantileThreshold μ ρ)) :=
  occupied_band_entropy μ ρ hρ hρ4

example :
    let d₁ : Gap := ⟨1/8, by norm_num, by norm_num⟩
    let d₂ : Gap := ⟨1/4, by norm_num, by norm_num⟩
    let μ := ENNReal.ofReal (1/5) • Measure.dirac d₁ +
      ENNReal.ofReal (4/5) • Measure.dirac d₂
    rarePsi μ (1/5) (1/32) = ENNReal.ofReal (Real.sqrt 2 / 20) ∧
    ThresholdHC.PsiClosedForm.quantileZero μ (1/5) 1024 = ENNReal.ofReal (1/10) := by
  convert sharp_example using 1 <;> norm_num [twoAtomLaw]
#print axioms ThresholdHC.PsiSharpness.OccupiedBandEntropyStatement
#print axioms ThresholdHC.PsiSharpness.TwoAtomSharpnessStatement
#print axioms ThresholdHC.PsiSharpness.finite_support_entropy
#print axioms ThresholdHC.PsiSharpness.inverseSquareCost_atom
#print axioms ThresholdHC.PsiSharpness.occupiedBandCount
#print axioms ThresholdHC.PsiSharpness.occupied_band_entropy
#print axioms ThresholdHC.PsiSharpness.rarePsi_le_full_cost
#print axioms ThresholdHC.PsiSharpness.sharp_example
#print axioms ThresholdHC.PsiSharpness.twoAtomLaw
#print axioms ThresholdHC.PsiSharpness.twoAtom_core
#print axioms ThresholdHC.PsiSharpness.twoAtom_probability
#print axioms ThresholdHC.PsiSharpness.twoAtom_psi_upper
#print axioms ThresholdHC.PsiSharpness.twoAtom_quantile
#print axioms ThresholdHC.PsiSharpness.twoAtom_tail
#print axioms ThresholdHC.PsiSharpness.two_atom_sharpness
