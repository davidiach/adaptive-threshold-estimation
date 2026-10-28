import ThresholdHC.CriticalEntropy.FiniteObservation
import ThresholdHC.CriticalEntropy.CriticalLaw

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace ThresholdHC.CriticalEntropy

theorem wordLikelihood_le_one (p : unitInterval) (n k : ℕ) : wordLikelihood p n k ≤ 1 := by
  have hp := pow_le_one₀ p.property.1 p.property.2 (n := k)
  have hn := pow_le_one₀ (sub_nonneg.mpr p.property.2)
    (sub_le_self (1 : ℝ) p.property.1) (n := n-k)
  have hprod : (p : ℝ)^k*(1-(p : ℝ))^(n-k) ≤ 1 := by
    simpa using mul_le_mul hp hn (pow_nonneg (sub_nonneg.mpr p.property.2) _) (by norm_num : (0 : ℝ) ≤ 1)
  simpa [wordLikelihood] using ENNReal.ofReal_le_ofReal hprod

theorem wordLikelihood_pos (p : unitInterval) (hp : 0 < (p : ℝ)) (hp' : (p : ℝ) < 1)
    (n k : ℕ) : 0 < wordLikelihood p n k := by
  apply ENNReal.ofReal_pos.mpr
  exact mul_pos (pow_pos hp _) (pow_pos (sub_pos.mpr hp') _)

theorem prior_weights_sum (p : unitInterval) :
    ENNReal.ofReal (p : ℝ)+ENNReal.ofReal (1-(p : ℝ)) = 1 := by
  rw [← ENNReal.ofReal_add p.property.1 (sub_nonneg.mpr p.property.2)]
  simp

theorem populationWordLikelihood_le_one {D : Type} [MeasurableSpace D]
    (μ : Measure D) [IsProbabilityMeasure μ] (p₀ p₁ q : D → unitInterval) (n k : ℕ) :
    populationWordLikelihood μ p₀ p₁ q n k ≤ 1 := by
  unfold populationWordLikelihood
  calc
    _ ≤ ∫⁻ _d, (1 : ℝ≥0∞) ∂μ := by
      apply lintegral_mono
      intro d
      calc
        _ ≤ ENNReal.ofReal (q d : ℝ)*1+ENNReal.ofReal (1-(q d : ℝ))*1 :=
          add_le_add (mul_le_mul' le_rfl (wordLikelihood_le_one _ _ _))
            (mul_le_mul' le_rfl (wordLikelihood_le_one _ _ _))
        _ = 1 := by simpa using prior_weights_sum (q d)
    _ = 1 := by simp

theorem populationWordLikelihood_pos {D : Type} [MeasurableSpace D]
    (μ : Measure D) [IsProbabilityMeasure μ] (p₀ p₁ q : D → unitInterval)
    (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q)
    (hp : ∀ᵐ d ∂μ, 0 < (p₀ d : ℝ) ∧ (p₀ d : ℝ) < 1 ∧
      0 < (p₁ d : ℝ) ∧ (p₁ d : ℝ) < 1) (n k : ℕ) :
    0 < populationWordLikelihood μ p₀ p₁ q n k := by
  let f := fun d => ENNReal.ofReal (q d : ℝ)*wordLikelihood (p₁ d) n k +
    ENNReal.ofReal (1-(q d : ℝ))*wordLikelihood (p₀ d) n k
  have hm : Measurable f := by unfold f wordLikelihood; fun_prop
  have hpos : ∀ᵐ d ∂μ, 0 < f d := by
    filter_upwards [hp] with d hd
    have hminus := wordLikelihood_pos (p₀ d) hd.1 hd.2.1 n k
    have hplus := wordLikelihood_pos (p₁ d) hd.2.2.1 hd.2.2.2 n k
    by_cases hz : (q d : ℝ) = 0
    · simpa [f,hz] using hminus
    · have hweight := ENNReal.ofReal_pos.mpr (lt_of_le_of_ne (q d).property.1 (Ne.symm hz))
      have hmul := mul_ne_zero (ne_of_gt hweight) (ne_of_gt hplus)
      exact lt_of_lt_of_le (bot_lt_iff_ne_bot.mpr hmul) (le_add_right le_rfl)
  have he : Function.support f =ᵐ[μ] univ := by
    filter_upwards [hpos] with d hd
    simp [Function.mem_support,ne_of_gt hd]
  change 0 < ∫⁻ d, f d ∂μ
  rw [lintegral_pos_iff_support hm,measure_congr he,measure_univ]
  norm_num

theorem critical_parameters_interior : ∀ᵐ d ∂criticalGapLaw,
    0 < (criticalParameter d false : ℝ) ∧ (criticalParameter d false : ℝ) < 1 ∧
    0 < (criticalParameter d true : ℝ) ∧ (criticalParameter d true : ℝ) < 1 := by
  have hs := criticalGapLaw_supported
  filter_upwards [hs] with d hd
  rw [criticalParameter_coe_of_mem d hd false,criticalParameter_coe_of_mem d hd true]
  simp only [Bool.false_eq_true,↓reduceIte]
  constructor
  · linarith [hd.1,hd.2]
  constructor
  · linarith [hd.1,hd.2]
  constructor <;> linarith [hd.1,hd.2]

end ThresholdHC.CriticalEntropy
