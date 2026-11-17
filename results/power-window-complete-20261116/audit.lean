import ThresholdHC.PowerWindow.Full
open MeasureTheory ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.PowerWindow
open ThresholdHC.EntropyTailQuantile
open scoped ENNReal
example : PowerConfidenceStatement := power_confidence
example : PowerCoreStatement := power_core
example : PowerPhiStatement := power_phi_closed
example : PowerQuantileStatement := power_quantile
example : PowerRiskStatement := power_risk
example (α ρ : ℝ) (hα : 0 < α) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    (α * ∫ s in (ρ ^ (1/α))..1, s ^ (α - 3)) =
      if α = 2 then Real.log (1/ρ) else α * (1 - ρ ^ (1 - 2/α)) / (α - 2) :=
  power_phi_closed α ρ hα hρ hρ1

example (μ : Measure Gap) [IsProbabilityMeasure μ] (α a ρ : ℝ)
    (hα : 0 < α) (ha : 0 < a) (ha2 : a ≤ 1/2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hm : ∀ x : ℝ, 0 < x → μ.real {d : Gap | (d : ℝ) ≤ x} = min 1 ((x/a)^α)) :
    quantileTail μ ρ =
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).restrict (Set.Iic ρ)).map
        (powerQuantile α a hα ha ha2) :=
  power_quantile_tail μ hα ha ha2 hρ hρ1 hm

example (μ : Measure Gap) [IsProbabilityMeasure μ] (α a ρ : ℝ)
    (hα : 0 < α) (ha : 0 < a) (ha2 : a ≤ 1/2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hm : ∀ x : ℝ, 0 < x → μ.real {d : Gap | (d : ℝ) ≤ x} = min 1 ((x/a)^α)) :
    quantileCore μ ρ = (volume.restrict (Set.Ioc ρ 1)).map
      (powerQuantile α a hα ha ha2) :=
  power_quantile_core μ hα ha ha2 hρ hρ1 hm

example (μ : Measure Gap) [IsProbabilityMeasure μ] (α a ρ : ℝ)
    (hα : 0 < α) (ha : 0 < a) (ha2 : a ≤ 1/2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hm : ∀ x : ℝ, 0 < x → μ.real {d : Gap | (d : ℝ) ≤ x} = min 1 ((x/a)^α)) :
    a^2 * (∫⁻ d : Gap, ENNReal.ofReal (((d : ℝ)⁻¹)^2) ∂quantileCore μ ρ).toReal =
      α * ∫ s in (ρ ^ (1/α))..1, s ^ (α - 3) :=
  power_core_cost μ hα ha ha2 hρ hρ1 hm

example (μ : Measure Gap) [IsProbabilityMeasure μ] (a ρ : ℝ)
    (ha : 0 < a) (ha2 : a ≤ 1/2) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hm : ∀ x : ℝ, 0 < x → μ.real {d : Gap | (d : ℝ) ≤ x} = min 1 ((x/a)^(2 : ℝ))) :
    a^2 * (∫⁻ d : Gap, ENNReal.ofReal (((d : ℝ)⁻¹)^2) ∂quantileCore μ ρ).toReal =
      Real.log (1/ρ) :=
  quadratic_core_cost μ ha ha2 hρ hρ1 hm

example (hQ : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (α a ρ B : ℝ),
    0 < α → α ≤ 4 → 0 < a → a ≤ 1/2 → 0 < ρ → ρ ≤ 1/4 → 0 < B → ExactPowerLaw μ α a →
    ENNReal.ofReal (uniformRate α (1 / (a * Real.sqrt B)) ρ / Real.sqrt 2) ≤
      closedQuantileValue μ ρ B ∧
    closedQuantileValue μ ρ B ≤ ENNReal.ofReal (2 * uniformRate α (1 / (a * Real.sqrt B)) ρ))
    (μ : Measure Gap) [IsProbabilityMeasure μ] (α a ρ B : ℝ)
    (hα : 0 < α) (hα4 : α ≤ 4) (ha : 0 < a) (ha2 : a ≤ 1/2)
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) (hm : ExactPowerLaw μ α a) :
    ENNReal.ofReal ((10 : ℝ)⁻¹^17 / Real.sqrt 2 * uniformRate α (1 / (a * Real.sqrt B)) ρ) ≤
      rareMinimaxRisk μ ρ B ∧
    rareMinimaxRisk μ ρ B ≤ ENNReal.ofReal (60002 * uniformRate α (1 / (a * Real.sqrt B)) ρ) :=
  power_risk_of_quantile hQ μ α a ρ B hα hα4 ha ha2 hρ hρ4 hB hm

example (hQ : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (α a ρ B : ℝ),
    0 < α → α ≤ 4 → 0 < a → a ≤ 1/2 → 0 < ρ → ρ ≤ 1/4 → 0 < B → ExactPowerLaw μ α a →
    ENNReal.ofReal (uniformRate α (1 / (a * Real.sqrt B)) ρ / Real.sqrt 2) ≤
      closedQuantileValue μ ρ B ∧
    closedQuantileValue μ ρ B ≤ ENNReal.ofReal (2 * uniformRate α (1 / (a * Real.sqrt B)) ρ))
    (μ : Measure Gap) [IsProbabilityMeasure μ] (α a ρ B δ : ℝ)
    (hα : 0 < α) (hα4 : α ≤ 4) (ha : 0 < a) (ha2 : a ≤ 1/2)
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) (hδ : 0 < δ) (hδ4 : δ ≤ 1/4)
    (hm : ExactPowerLaw μ α a) :
    let x := Real.sqrt (Real.log (1 / δ) / B) / a
    ENNReal.ofReal ((10 : ℝ)⁻¹^17 / Real.sqrt 2 * uniformRate α x ρ) ≤
      ThresholdHC.ConfidenceTransfer.rareConfidenceRadius μ ρ B δ ∧
    ThresholdHC.ConfidenceTransfer.rareConfidenceRadius μ ρ B δ ≤
      ThresholdHC.ConfidenceProgram.hardConfidenceRadius μ ρ B δ ∧
    ThresholdHC.ConfidenceProgram.hardConfidenceRadius μ ρ B δ ≤
      ENNReal.ofReal (1500000 * uniformRate α x ρ) :=
  power_confidence_of_quantile hQ μ α a ρ B δ hα hα4 ha ha2 hρ hρ4 hB hδ hδ4 hm

example (μ : Measure Gap) [IsProbabilityMeasure μ] (α a ρ : ℝ)
    (hα : 0 < α) (hα4 : α ≤ 4) (ha : 0 < a) (ha2 : a ≤ 1/2)
    (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hm : ∀ x : ℝ, 0 < x → μ.real {d : Gap | (d : ℝ) ≤ x} = min 1 ((x/a)^α)) :
    a^2 * (∫⁻ d : Gap, ENNReal.ofReal (((d : ℝ)⁻¹)^2) ∂quantileCore μ ρ).toReal =
        powerPhi α ρ ∧
    (1/2 : ℝ) * (1 + Real.log (effectiveScales α ρ)) ≤ 1 + ThresholdHC.PsiGap.coreEntropy μ ρ ∧
    1 + ThresholdHC.PsiGap.coreEntropy μ ρ ≤ (383/100 : ℝ) * (1 + Real.log (effectiveScales α ρ)) :=
  power_core μ α a ρ hα hα4 ha ha2 hρ hρ1 hm

example (μ : Measure Gap) [IsProbabilityMeasure μ] (α a ρ B : ℝ)
    (hα : 0 < α) (hα4 : α ≤ 4) (ha : 0 < a) (ha2 : a ≤ 1/2)
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B)
    (hm : ∀ x : ℝ, 0 < x → μ.real {d : Gap | (d : ℝ) ≤ x} = min 1 ((x/a)^α)) :
    ENNReal.ofReal (uniformRate α (1 / (a * Real.sqrt B)) ρ / Real.sqrt 2) ≤
      closedQuantileValue μ ρ B ∧
    closedQuantileValue μ ρ B ≤ ENNReal.ofReal (2 * uniformRate α (1 / (a * Real.sqrt B)) ρ) :=
  power_quantile μ α a ρ B hα hα4 ha ha2 hρ hρ4 hB hm

example (μ : Measure Gap) [IsProbabilityMeasure μ] (α a ρ B : ℝ)
    (hα : 0 < α) (hα4 : α ≤ 4) (ha : 0 < a) (ha2 : a ≤ 1/2)
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B)
    (hm : ∀ x : ℝ, 0 < x → μ.real {d : Gap | (d : ℝ) ≤ x} = min 1 ((x/a)^α)) :
    ENNReal.ofReal ((10 : ℝ)⁻¹^17 / Real.sqrt 2 * uniformRate α (1 / (a * Real.sqrt B)) ρ) ≤
      rareMinimaxRisk μ ρ B ∧
    rareMinimaxRisk μ ρ B ≤ ENNReal.ofReal (60002 * uniformRate α (1 / (a * Real.sqrt B)) ρ) :=
  power_risk μ α a ρ B hα hα4 ha ha2 hρ hρ4 hB hm

example (μ : Measure Gap) [IsProbabilityMeasure μ] (α a ρ B δ : ℝ)
    (hα : 0 < α) (hα4 : α ≤ 4) (ha : 0 < a) (ha2 : a ≤ 1/2)
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) (hδ : 0 < δ) (hδ4 : δ ≤ 1/4)
    (hm : ∀ x : ℝ, 0 < x → μ.real {d : Gap | (d : ℝ) ≤ x} = min 1 ((x/a)^α)) :
    let x := Real.sqrt (Real.log (1 / δ) / B) / a
    ENNReal.ofReal ((10 : ℝ)⁻¹^17 / Real.sqrt 2 * uniformRate α x ρ) ≤
      ThresholdHC.ConfidenceTransfer.rareConfidenceRadius μ ρ B δ ∧
    ThresholdHC.ConfidenceTransfer.rareConfidenceRadius μ ρ B δ ≤
      ThresholdHC.ConfidenceProgram.hardConfidenceRadius μ ρ B δ ∧
    ThresholdHC.ConfidenceProgram.hardConfidenceRadius μ ρ B δ ≤
      ENNReal.ofReal (1500000 * uniformRate α x ρ) :=
  power_confidence μ α a ρ B δ hα hα4 ha ha2 hρ hρ4 hB hδ hδ4 hm
#print axioms ThresholdHC.PowerWindow.PowerConfidenceStatement
#print axioms ThresholdHC.PowerWindow.PowerCoreStatement
#print axioms ThresholdHC.PowerWindow.PowerPhiStatement
#print axioms ThresholdHC.PowerWindow.PowerQuantileStatement
#print axioms ThresholdHC.PowerWindow.PowerRiskStatement
#print axioms ThresholdHC.PowerWindow.band_index_antitone
#print axioms ThresholdHC.PowerWindow.band_log_bounds
#print axioms ThresholdHC.PowerWindow.band_lower_label
#print axioms ThresholdHC.PowerWindow.band_upper_label
#print axioms ThresholdHC.PowerWindow.band_window_count
#print axioms ThresholdHC.PowerWindow.clipped_sum_comparison
#print axioms ThresholdHC.PowerWindow.core_root_comparison
#print axioms ThresholdHC.PowerWindow.effectiveScales
#print axioms ThresholdHC.PowerWindow.effective_scales_ge_one
#print axioms ThresholdHC.PowerWindow.effective_scales_window
#print axioms ThresholdHC.PowerWindow.entropy_window_lower
#print axioms ThresholdHC.PowerWindow.entropy_window_upper
#print axioms ThresholdHC.PowerWindow.exact_power_law_eq
#print axioms ThresholdHC.PowerWindow.finite_entropy_card_bound
#print axioms ThresholdHC.PowerWindow.finite_entropy_cross_entropy
#print axioms ThresholdHC.PowerWindow.finite_entropy_lower_bound
#print axioms ThresholdHC.PowerWindow.finite_entropy_mean_bound
#print axioms ThresholdHC.PowerWindow.finite_entropy_nonneg
#print axioms ThresholdHC.PowerWindow.gap_measure_ext
#print axioms ThresholdHC.PowerWindow.log_bandEdge
#print axioms ThresholdHC.PowerWindow.log_moment_to_band_mean
#print axioms ThresholdHC.PowerWindow.lower_log_moment_bound
#print axioms ThresholdHC.PowerWindow.ofReal_minimum
#print axioms ThresholdHC.PowerWindow.partialPowerLaw
#print axioms ThresholdHC.PowerWindow.partialPowerLaw_cdf
#print axioms ThresholdHC.PowerWindow.partialPowerLaw_finite
#print axioms ThresholdHC.PowerWindow.powerPhi
#print axioms ThresholdHC.PowerWindow.powerQuantileScale
#print axioms ThresholdHC.PowerWindow.powerTail
#print axioms ThresholdHC.PowerWindow.power_band_log_width
#print axioms ThresholdHC.PowerWindow.power_confidence
#print axioms ThresholdHC.PowerWindow.power_confidence_of_quantile
#print axioms ThresholdHC.PowerWindow.power_core
#print axioms ThresholdHC.PowerWindow.power_core_affine_log
#print axioms ThresholdHC.PowerWindow.power_core_band_bound
#print axioms ThresholdHC.PowerWindow.power_core_band_integral
#print axioms ThresholdHC.PowerWindow.power_core_band_peak
#print axioms ThresholdHC.PowerWindow.power_core_cost
#print axioms ThresholdHC.PowerWindow.power_core_cost_value
#print axioms ThresholdHC.PowerWindow.power_core_entropy_estimates
#print axioms ThresholdHC.PowerWindow.power_core_integral
#print axioms ThresholdHC.PowerWindow.power_core_lower_moment
#print axioms ThresholdHC.PowerWindow.power_core_oriented_log
#print axioms ThresholdHC.PowerWindow.power_core_term
#print axioms ThresholdHC.PowerWindow.power_core_upper_moment
#print axioms ThresholdHC.PowerWindow.power_core_window
#print axioms ThresholdHC.PowerWindow.power_density_balance
#print axioms ThresholdHC.PowerWindow.power_density_band_bound
#print axioms ThresholdHC.PowerWindow.power_density_peak
#print axioms ThresholdHC.PowerWindow.power_kernel_integral
#print axioms ThresholdHC.PowerWindow.power_phi_closed
#print axioms ThresholdHC.PowerWindow.power_phi_pos
#print axioms ThresholdHC.PowerWindow.power_quantile
#print axioms ThresholdHC.PowerWindow.power_quantile_core
#print axioms ThresholdHC.PowerWindow.power_quantile_formula
#print axioms ThresholdHC.PowerWindow.power_quantile_of_core
#print axioms ThresholdHC.PowerWindow.power_quantile_tail
#print axioms ThresholdHC.PowerWindow.power_risk
#print axioms ThresholdHC.PowerWindow.power_risk_of_quantile
#print axioms ThresholdHC.PowerWindow.power_tail_formula
#print axioms ThresholdHC.PowerWindow.power_tail_saturated
#print axioms ThresholdHC.PowerWindow.power_tail_uniform_integral
#print axioms ThresholdHC.PowerWindow.power_window_length
#print axioms ThresholdHC.PowerWindow.quadratic_core_cost
#print axioms ThresholdHC.PowerWindow.quantile_scale_lt_one
#print axioms ThresholdHC.PowerWindow.quantile_scale_pos
#print axioms ThresholdHC.PowerWindow.rpow_log_balance
#print axioms ThresholdHC.PowerWindow.uniformRate
#print axioms ThresholdHC.PowerWindow.uniform_power_integral
#print axioms ThresholdHC.PowerWindow.upper_log_moment_bound
#print axioms ThresholdHC.PowerWindow.window_band_decomposition
#print axioms ThresholdHC.PowerWindow.window_entropy_normalization
#print axioms ThresholdHC.PowerWindow.window_label_mean
