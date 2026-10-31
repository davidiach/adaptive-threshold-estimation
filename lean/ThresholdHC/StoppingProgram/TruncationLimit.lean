import ThresholdHC.StoppingProgram.TruncationRisk

/-! Uniform finite-prefix lower bounds pass to the original infinite-process
estimator because its expected-work truncation penalty tends to zero. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo

theorem truncation_error_tendsto (ρ B : ℝ) :
    Tendsto (fun N : ℕ => ENNReal.ofReal (ρ/2*Real.sqrt (B/((N:ℝ)+1)))) atTop (𝓝 0) := by
  have hdiv : Tendsto (fun N : ℕ => B/((N:ℝ)+1)) atTop (𝓝 0) := by
    simpa only [mul_one_div,mul_zero] using
      (tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) :
        Tendsto (fun N : ℕ => B*(1/((N:ℝ)+1))) atTop (𝓝 (B*0)))
  have hs := (Real.continuous_sqrt.tendsto 0).comp hdiv
  have hm : Tendsto (fun N : ℕ => ρ/2*Real.sqrt (B/((N:ℝ)+1))) atTop
      (𝓝 (ρ/2*Real.sqrt 0)) := tendsto_const_nhds.mul hs
  have he := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (show Tendsto (fun N : ℕ => ρ/2*Real.sqrt (B/((N:ℝ)+1))) atTop
      (𝓝 (ρ/2*Real.sqrt 0)) from hm)
  convert he using 1 <;> simp [Function.comp_def]

theorem prefix_lower_transfer {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    (ρ B : ℝ) (hρ : 0 ≤ ρ) (hB : 0 ≤ B) (hbudget : RareBudget μ A ρ B)
    (q r : SignLaw) (hq : RarePrior μ ρ q) (hr : RarePrior μ ρ r) (L : ℝ≥0∞)
    (hpre : ∀ N : ℕ, L ≤
      max (rootMeanRisk (observablePrefixLaw μ A q N) (prefixTruncation A ρ N) (signMean μ q.val))
        (rootMeanRisk (observablePrefixLaw μ A r N) (prefixTruncation A ρ N) (signMean μ r.val))) :
    L ≤ rareRisk μ A ρ := by
  have hbound (N : ℕ) : L ≤ rareRisk μ A ρ+
      ENNReal.ofReal (ρ/2*Real.sqrt (B/((N:ℝ)+1))) := by
    apply (hpre N).trans
    have hp (u : SignLaw) (hu : RarePrior μ ρ u) :
        rootMeanRisk (observablePrefixLaw μ A u N) (prefixTruncation A ρ N) (signMean μ u.val) ≤
          rareRisk μ A ρ+ENNReal.ofReal (ρ/2*Real.sqrt (B/((N:ℝ)+1))) := by
      exact (prefixTruncation_rmsRisk μ A u ρ (signMean μ u.val) B hρ
        ⟨integral_nonneg (fun d => (u.property.2 d).1),hu⟩ hB N (hbudget u hu)).trans
          (add_le_add (le_iSup_of_le u (le_iSup_of_le hu le_rfl)) le_rfl)
    exact max_le (hp q hq) (hp r hr)
  have ht : Tendsto (fun N : ℕ => rareRisk μ A ρ+
      ENNReal.ofReal (ρ/2*Real.sqrt (B/((N:ℝ)+1)))) atTop (𝓝 (rareRisk μ A ρ)) := by
    simpa only [add_zero] using tendsto_const_nhds.add (truncation_error_tendsto ρ B)
  exact ge_of_tendsto ht (Eventually.of_forall hbound)

end ThresholdHC.StoppingProgram
