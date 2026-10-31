import ThresholdHC.StoppingProgram.TruncatedPrefix
import ThresholdHC.Tier6.RiskReduction

/-! The finite-prefix estimate loses at most the midpoint loss times the
Markov tail probability. The estimate may have infinite original risk. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier3 ThresholdHC.Tier4 ThresholdHC.Tier6 ThresholdHC.RareAboveTwo

theorem prefixTruncation_ennreal_loss {R : Type} [MeasurableSpace R]
    (A : AdaptiveEstimator R) (ρ θ : ℝ) (hθ : 0 ≤ θ ∧ θ ≤ ρ)
    (N : ℕ) (r : R) (x : ProcessTape)
    (hv : ∀ k, (x k).isSome = (A.policy r (processHistory x k)).isSome) :
    ENNReal.ofReal ((prefixTruncation A ρ N (r,processPrefix N x)-θ)^2) ≤
      ENNReal.ofReal ((A.output (r,x)-θ)^2) +
        ENNReal.ofReal ((ρ/2)^2/((N:ℝ)+1))*totalProcessWork x := by
  have hl := ENNReal.ofReal_le_ofReal (prefixTruncation_loss A ρ θ hθ N r x hv)
  rw [ENNReal.ofReal_add (sq_nonneg _) (by positivity)] at hl
  apply hl.trans
  apply add_le_add le_rfl
  by_cases hN : A.policy r (processHistory x N) = none
  · simp [hN]
  · simp only [hN,ite_false,mul_one]
    have hw := mul_le_mul_right (valid_path_continuation_work (A.policy r) x hv N hN)
      (ENNReal.ofReal ((ρ/2)^2/((N:ℝ)+1)))
    rw [← ENNReal.ofReal_mul (by positivity)] at hw
    have he : ((ρ/2)^2/((N:ℝ)+1))*((N:ℝ)+1) = (ρ/2)^2 := by field_simp
    rwa [he] at hw

theorem prefixTruncation_squaredRisk {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (q : SignLaw)
    (ρ θ : ℝ) (hθ : 0 ≤ θ ∧ θ ≤ ρ) (N : ℕ) :
    squaredRisk (observablePrefixLaw μ A q N) (prefixTruncation A ρ N) θ ≤
      squaredRisk (experimentLaw μ A q) (populationOutput A) θ +
        ENNReal.ofReal ((ρ/2)^2/((N:ℝ)+1))*expectedWork μ A q := by
  have hm : Measurable (fun z : PopulationSeed R × ProcessTape => (z.1.1,processPrefix N z.2)) :=
    (measurable_fst.comp measurable_fst).prodMk
      (Measurable.of_eval (fun i : Fin N => (measurable_pi_apply i.val).comp measurable_snd))
  have hf : Measurable (fun z => ENNReal.ofReal ((prefixTruncation A ρ N z-θ)^2)) :=
    (((measurable_prefixTruncation A ρ N).sub_const θ).pow_const 2).ennreal_ofReal
  have hg : Measurable (fun z => ENNReal.ofReal ((populationOutput A z-θ)^2)) :=
    (((measurable_populationOutput A).sub_const θ).pow_const 2).ennreal_ofReal
  unfold squaredRisk observablePrefixLaw
  rw [lintegral_map hf hm]
  calc
    _ ≤ ∫⁻ z, ENNReal.ofReal ((populationOutput A z-θ)^2)+
        ENNReal.ofReal ((ρ/2)^2/((N:ℝ)+1))*totalProcessWork z.2 ∂experimentLaw μ A q := by
      apply lintegral_mono_ae
      filter_upwards [original_path_valid μ A q] with z hz
      exact prefixTruncation_ennreal_loss A ρ θ hθ N z.1.1 z.2 hz
    _ = _ := by
      rw [lintegral_add_left hg,lintegral_const_mul _
        (measurable_totalProcessWork Prod.snd observable_tape_measurable)]
      rfl

theorem prefixTruncation_rmsRisk {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (q : SignLaw)
    (ρ θ B : ℝ) (hρ : 0 ≤ ρ) (hθ : 0 ≤ θ ∧ θ ≤ ρ) (hB : 0 ≤ B)
    (N : ℕ) (hbudget : expectedWork μ A q ≤ ENNReal.ofReal B) :
    rootMeanRisk (observablePrefixLaw μ A q N) (prefixTruncation A ρ N) θ ≤
      rootMeanRisk (experimentLaw μ A q) (populationOutput A) θ +
        ENNReal.ofReal (ρ/2*Real.sqrt (B/((N:ℝ)+1))) := by
  have h := (prefixTruncation_squaredRisk μ A q ρ θ hθ N).trans
    (add_le_add le_rfl (mul_le_mul_right hbudget (ENNReal.ofReal ((ρ/2)^2/((N:ℝ)+1)))))
  rw [← ENNReal.ofReal_mul (by positivity)] at h
  have he : ((ρ/2)^2/((N:ℝ)+1))*B = (ρ/2*Real.sqrt (B/((N:ℝ)+1)))^2 := by
    rw [mul_pow,Real.sq_sqrt (by positivity)]
    ring
  rw [he] at h
  have hh := (ENNReal.rpow_le_rpow h (by norm_num : (0:ℝ) ≤ 1/2)).trans
    (ENNReal.rpow_add_le_add_rpow _ _ (by norm_num) (by norm_num))
  rw [ofReal_square_rpow_half _ (by positivity)] at hh
  exact hh

end ThresholdHC.StoppingProgram
