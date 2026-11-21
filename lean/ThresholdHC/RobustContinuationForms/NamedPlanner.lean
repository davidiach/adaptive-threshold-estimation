import ThresholdHC.RobustContinuationForms.Specification

/-! The named robust planner.

The body of `RobustContinuation.robust_zero_atom_planner_rate` is restated
with the estimator named and split into the two branches of the planner's
decision, as `KnownLawPlanner.planner_output_of_rates` splits the known-law
planner. The CDF form constructs the coupling with
`exists_robust_coupling_of_cdf`, and the exact form applies the CDF form to
the named split, the exact zero-atom enclosure and the optimal weights. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace ThresholdHC.RobustContinuationForms
open ThresholdHC.Tier6 (Gap SignLaw AdaptiveEstimator signMean)
open ThresholdHC.EntropyTailUpper ThresholdHC.RareAboveTwo
open ThresholdHC.EntropyTailQuantile ThresholdHC.EntropyTailAssembly
open ThresholdHC.EntropyTailExecution ThresholdHC.KnownLawPlanner
open ThresholdHC.ArbitraryLawAdaptation ThresholdHC.RobustContinuation

/-- The constant `ρ/2` meets every bound that is at least `ρ/2`, under every
true law. -/
theorem constant_output_of_half_le {ρ B : ℝ} (hρ : 0 ≤ ρ) {C : ℝ≥0∞}
    (hC : ENNReal.ofReal (ρ/2) ≤ C) (μ : Measure Gap) [IsProbabilityMeasure μ] :
    RareBudget μ (constantEstimator (ρ/2)) ρ B ∧ rareRisk μ (constantEstimator (ρ/2)) ρ ≤ C :=
  ⟨constant_rare_budget μ ρ B (ρ/2), (half_rarity_risk μ ρ hρ).trans hC⟩

/-- The named robust planner under every coupled true law. -/
theorem robust_tight_planner_output_proof : RobustTightPlannerOutputStatement := by
  intro η _ σ τ ζ _ _ _ z₀ ρ B N hz0 hzρ hρ4 hB hcore htail hτs hζs hN E hE w hlow hup
  have hρ : 0 < ρ := hz0.trans_lt hzρ
  refine ⟨fun ⟨hz, hsmall⟩ => ?_, fun hnot => ?_⟩
  · intro π μ₀ μ _ _ _ hup' href hμ
    have hh := budgetScale_pos hB
    have hτ := inverse_integrable_of_support τ hh hτs
    have hζ0 : 0 ≤ ζ.real univ := measureReal_nonneg
    have hzE : z₀ + ζ.real univ ≤ E.unresolved := hE.2.2.1
    have hc : 0 < 1 - z₀ := by linarith
    have hρc : ρ ≤ 1 - z₀ := by linarith
    have hr : 0 < conditionalRarity ρ z₀ := div_pos (by linarith) hc
    have hr1 : conditionalRarity ρ z₀ ≤ 1 := (div_le_one hc).mpr (by linarith)
    have ht := (quantileThreshold_properties η hr hr1).1
    have hs : ∀ᵐ d : Gap ∂σ, quantileThreshold η (conditionalRarity ρ z₀) ≤ (d:ℝ) := by
      rw [hcore]
      exact Measure.ae_smul_measure (quantileCore_support η (conditionalRarity ρ z₀)) _
    have hlaw : σ+τ+ζ = ENNReal.ofReal (1 - z₀) • η := by
      rw [add_assoc, htail, hcore, ← smul_add, add_comm, quantileTail_add_core η hr hr1]
    have hzJ : E.unresolved ≤ levelAccuracy ρ (planTerminal hρ B E.unresolved)/8 := by
      have h := planTerminal_unresolved hρ B hz
      linarith [levelAccuracy_pos hρ (planTerminal hρ B E.unresolved)]
    have hrate := zero_atom_plan_rate_dyadic η σ τ ζ hz0 hρ hρ4 hB hcore htail hτs hζs hN E hE
      hz w hlow hup
    rw [min_eq_right hsmall] at hrate
    have hμ₀ := uncoupled_mass η (by linarith) π href μ₀ μ hμ
    have hE₀ : ζ.real univ + μ₀.real univ ≤ E.unresolved := by
      rw [hμ₀]
      linarith
    have hζρ : ζ.real univ ≤ ρ := by linarith
    have hk := robust_planCost_pos η σ τ ζ hc hlaw π hup' href μ₀ μ hμ ht hs hN hτ hρ hρc hζρ
      E hE₀ (searchCaps E.resolvedError hE.vanishes hρ) (planTerminal hρ B E.unresolved)
    have hw : ∀ i, 0 < w i := fun i =>
      lt_of_lt_of_le (Real.sqrt_pos.mpr (div_pos
        (mul_pos (by norm_num) (levelAccuracy_pos hρ i.val)) (hk i))) (hlow i)
    obtain ⟨hb, hrisk⟩ := robust_searched_plan_valid η σ τ ζ hc hlaw π hup' href μ₀ μ hμ ht hs
      hN hτ hρ hρc hB E hE₀ hE.vanishes hzJ w hw
    exact ⟨hb, hrisk.trans hrate⟩
  · intro μ _
    apply constant_output_of_half_le hρ.le
    by_cases hz : 2048 * E.unresolved ≤ ρ
    · have hc : ρ/2 < Real.sqrt (planCertificate ρ (planRates B
          (planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ)
            (planTerminal hρ B E.unresolved)) w)) :=
        not_le.mp fun h => hnot ⟨hz, h⟩
      have h := zero_atom_plan_rate_dyadic η σ τ ζ hz0 hρ hρ4 hB hcore htail hτs hζs hN E hE
        hz w hlow hup
      rwa [min_eq_left hc.le] at h
    · have hf := zero_atom_fallback_rate η σ τ ζ 2 hz0 hρ hρ4 hB hcore htail hτs hζs E hE
        (not_le.mp hz)
      rwa [plannedCoefficient_eq] at hf

/-- The named robust planner under every CDF-dominated true law. -/
theorem cdf_robust_tight_planner_output_proof : CDFRobustTightPlannerOutputStatement := by
  intro η _ σ τ ζ _ _ _ z₀ ρ B N hz0 hzρ hρ4 hB hcore htail hτs hζs hN E hE w hlow hup
  have h := robust_tight_planner_output_proof η σ τ ζ hz0 hzρ hρ4 hB hcore htail hτs hζs hN E hE
    w hlow hup
  refine ⟨fun hrun μ _ hdom => ?_, h.2⟩
  obtain ⟨π, μ₀, hπf, hμ₀f, hup', href, hμ, _⟩ :=
    exists_robust_coupling_of_cdf η μ hz0 (by linarith) hdom
  exact h.1 hrun π μ₀ μ hup' href hμ

/-- The named split is the zero-atom quantile split of the reference, cut at
the budget scale. -/
theorem robust_named_split (η : Measure Gap) (z₀ ρ B : ℝ) :
    robustUpperTail η z₀ ρ B + robustLowerTail η z₀ ρ B =
        ENNReal.ofReal (1 - z₀) • quantileTail η (conditionalRarity ρ z₀) ∧
      (∀ᵐ d : Gap ∂robustUpperTail η z₀ ρ B, budgetScale B ≤ (d:ℝ)) ∧
      (∀ᵐ d : Gap ∂robustLowerTail η z₀ ρ B, (d:ℝ) ≤ budgetScale B) := by
  have hS : MeasurableSet {d : Gap | budgetScale B ≤ (d:ℝ)} :=
    measurableSet_le measurable_const measurable_subtype_coe
  refine ⟨Measure.restrict_add_restrict_compl hS, ae_restrict_mem hS, ?_⟩
  filter_upwards [ae_restrict_mem hS.compl] with d hd
  exact (not_le.mp hd).le

/-- The named planner on the named reference design. -/
theorem robust_exact_planner_output_proof : RobustExactPlannerOutputStatement := by
  intro η _ z₀ ρ B hz0 hzρ hρ4 hB
  have hρ : 0 < ρ := hz0.trans_lt hzρ
  have hc : 0 < 1 - z₀ := by linarith
  have hr : 0 < conditionalRarity ρ z₀ := div_pos (by linarith) hc
  have hr1 : conditionalRarity ρ z₀ ≤ 1 := (div_le_one hc).mpr (by linarith)
  obtain ⟨htail, hτs, hζs⟩ := robust_named_split η z₀ ρ B
  have hN : bandEdge (robustSplitBands η hzρ hρ4) <
      quantileThreshold η (conditionalRarity ρ z₀) :=
    Nat.find_spec (exists_bandEdge_lt η hr hr1)
  exact cdf_robust_tight_planner_output_proof η (robustCore η z₀ ρ) (robustUpperTail η z₀ ρ B)
    (robustLowerTail η z₀ ρ B) hz0 hzρ hρ4 hB rfl htail hτs hζs hN
    (robustPlannerEnclosure η B hz0 hzρ hρ4)
    (SplitEnclosure.exactZero_tight (robustCore η z₀ ρ) (robustUpperTail η z₀ ρ B)
      (robustLowerTail η z₀ ρ B) (robustSplitBands η hzρ hρ4) hz0)
    (robustExactWeights (robustCore η z₀ ρ) (robustUpperTail η z₀ ρ B)
      (robustLowerTail η z₀ ρ B) hz0 hρ B (robustSplitBands η hzρ hρ4))
    (fun i => le_rfl) (fun i => le_mul_of_one_le_left (Real.sqrt_nonneg _) (by norm_num))

/-- With reference mass at least `ρ` at zero, the constant `ρ/2` meets the
planner's bound under every true law. -/
theorem robust_large_atom_output_proof : RobustLargeAtomOutputStatement := by
  intro η _ z₀ ρ B hρ hB hρz μ _
  apply constant_output_of_half_le hρ.le
  have hfl := min_zeroMass_le_zeroSelection (zeroAtomLaw z₀ η) hρ hB
  rw [zeroAtomLaw_zero_atom] at hfl
  have h1 : ENNReal.ofReal (ρ/2) ≤ zeroSelection (zeroAtomLaw z₀ η) ρ B :=
    le_trans (le_min (ENNReal.ofReal_le_ofReal (by linarith))
      (ENNReal.ofReal_le_ofReal (by linarith))) hfl
  have hC : (1:ℝ) ≤ plannedCoefficient 28000 := by
    unfold plannedCoefficient
    have := le_max_left (4096:ℝ) (8 * Real.sqrt 2 * 28000)
    linarith
  calc ENNReal.ofReal (ρ/2) ≤ 1 * zeroSelection (zeroAtomLaw z₀ η) ρ B := by rwa [one_mul]
    _ ≤ ENNReal.ofReal (plannedCoefficient 28000) * zeroSelection (zeroAtomLaw z₀ η) ρ B := by
      gcongr
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hC

end ThresholdHC.RobustContinuationForms
