import ThresholdHC.ArbitraryLawAdaptation.CDFSelection
import ThresholdHC.RobustContinuation.RobustPlannerOutput

/-! From CDF domination to the coupling used by the robust continuation.

The common-uniform CDF coupling includes the reference atom at zero. Its
positive-reference part is lifted by a bounded density and pulled back to
`Gap × Gap`; the remaining true-law mass is charged as unresolved mass.
No conditional sign allocation is assumed: the original measurable sign
law is integrated at the true gap, preserving its total positive fraction.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace ThresholdHC.RobustContinuation
open ThresholdHC.Tier6 (Gap SignLaw AdaptiveEstimator signMean)
open ThresholdHC.ArbitraryLawAdaptation ThresholdHC.RareAboveTwo
open ThresholdHC.EntropyTailQuantile ThresholdHC.EntropyTailAssembly ThresholdHC.KnownLawPlanner

theorem mappedGap_support (μ : Measure Gap) :
    ∀ᵐ d : ℝ ∂μ.map Subtype.val, d ∈ Ioc 0 (1/2) := by
  apply (ae_map_iff measurable_subtype_coe.aemeasurable measurableSet_Ioc).mpr
  exact Filter.Eventually.of_forall fun d => d.property

theorem mappedGap_below_zero (μ : Measure Gap) :
    μ.map Subtype.val (Iio 0) = 0 := by
  rw [Measure.map_apply measurable_subtype_coe measurableSet_Iio]
  have he : (Subtype.val : Gap → ℝ) ⁻¹' Iio 0 = ∅ := by
    ext d
    simp only [mem_preimage, mem_Iio, mem_empty_iff_false, iff_false]
    exact not_lt.mpr d.property.1.le
  rw [he, measure_empty]

theorem mappedGap_cdf_top (μ : Measure Gap) [IsProbabilityMeasure μ] :
    cdf (μ.map Subtype.val) (1/2) = 1 := by
  have : IsProbabilityMeasure (μ.map Subtype.val) :=
    (Measure.isProbabilityMeasure_map_iff measurable_subtype_coe.aemeasurable).mpr inferInstance
  rw [cdf_eq_real, map_measureReal_apply measurable_subtype_coe measurableSet_Iic]
  have he : (Subtype.val : Gap → ℝ) ⁻¹' Iic (1/2) = univ :=
    eq_univ_of_forall fun d => d.property.2
  rw [he, probReal_univ]

theorem zeroAtomLaw_probability (η : Measure Gap) [IsProbabilityMeasure η]
    {z₀ : ℝ} (hz0 : 0 ≤ z₀) (hz1 : z₀ ≤ 1) :
    IsProbabilityMeasure (zeroAtomLaw z₀ η) := by
  have : IsProbabilityMeasure (η.map Subtype.val) :=
    (Measure.isProbabilityMeasure_map_iff measurable_subtype_coe.aemeasurable).mpr inferInstance
  constructor
  simp only [zeroAtomLaw, Measure.add_apply, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add hz0 (sub_nonneg.mpr hz1)]
  norm_num

theorem zeroAtomLaw_below_zero (η : Measure Gap) (z₀ : ℝ) :
    zeroAtomLaw z₀ η (Iio 0) = 0 := by
  rw [zeroAtomLaw, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    mappedGap_below_zero]
  simp

theorem zeroAtomLaw_cdf_top (η : Measure Gap) [IsProbabilityMeasure η]
    {z₀ : ℝ} (hz0 : 0 ≤ z₀) (hz1 : z₀ ≤ 1) :
    cdf (zeroAtomLaw z₀ η) (1/2) = 1 := by
  have := zeroAtomLaw_probability η hz0 hz1
  rw [cdf_eq_real, measureReal_def, zeroAtomLaw, Measure.add_apply, Measure.smul_apply,
    Measure.smul_apply, Measure.dirac_apply_of_mem (by norm_num : (0:ℝ) ∈ Iic (1/2)),
    Measure.map_apply measurable_subtype_coe measurableSet_Iic]
  have he : (Subtype.val : Gap → ℝ) ⁻¹' Iic (1/2) = univ :=
    eq_univ_of_forall fun d => d.property.2
  rw [he, measure_univ, smul_eq_mul, smul_eq_mul, mul_one, mul_one,
    ← ENNReal.ofReal_add hz0 (sub_nonneg.mpr hz1)]
  norm_num

/-- CDF domination constructs exactly the positive-gap coupling and
unresolved true-law part required by the robust plan. The construction is
independent of the true sign law and applies to every reference law,
including finite learned laws. -/
theorem exists_robust_coupling_of_cdf (η μ : Measure Gap)
    [IsProbabilityMeasure η] [IsProbabilityMeasure μ] {z₀ : ℝ}
    (hz0 : 0 ≤ z₀) (hz1 : z₀ ≤ 1)
    (hdom : ∀ x, cdf (μ.map Subtype.val) x ≤ cdf (zeroAtomLaw z₀ η) x) :
    ∃ (π : Measure (Gap × Gap)) (μ₀ : Measure Gap),
      IsFiniteMeasure π ∧ IsFiniteMeasure μ₀ ∧
      (∀ᵐ z ∂π, (z.1:ℝ) ≤ z.2) ∧
      π.map Prod.fst = ENNReal.ofReal (1 - z₀) • η ∧
      μ = π.map Prod.snd + μ₀ ∧ μ₀.real univ = z₀ := by
  have := zeroAtomLaw_probability η hz0 hz1
  have : IsProbabilityMeasure (μ.map Subtype.val) :=
    (Measure.isProbabilityMeasure_map_iff measurable_subtype_coe.aemeasurable).mpr inferInstance
  obtain ⟨κ, hκprob, hκfst, hκsnd, hκup⟩ := exists_increasing_coupling_of_cdf
    (zeroAtomLaw z₀ η) (μ.map Subtype.val) (zeroAtomLaw_below_zero η z₀)
    (mappedGap_below_zero μ) (by norm_num : (0:ℝ) ≤ 1/2)
    (zeroAtomLaw_cdf_top η hz0 hz1) (mappedGap_cdf_top μ) hdom
  let ν : Measure Gap := ENNReal.ofReal (1 - z₀) • η
  have : IsFiniteMeasure ν := η.smul_finite ENNReal.ofReal_ne_top
  have hν : ν.map Subtype.val ≤ κ.map Prod.fst := by
    rw [hκfst, zeroAtomLaw]
    change (ENNReal.ofReal (1 - z₀) • η).map Subtype.val ≤ _
    rw [Measure.map_smul _ measurable_subtype_coe.aemeasurable]
    exact Measure.le_add_left le_rfl
  let ξ := realSelectionLift κ (ν.map Subtype.val)
  have hξle : ξ ≤ κ := realSelectionLift_le κ hν
  have : IsFiniteMeasure ξ := isFiniteMeasure_of_le κ hξle
  have hξfst : ξ.map Prod.fst = ν.map Subtype.val := realSelectionLift_first κ hν
  have hpos1 : ∀ᵐ z ∂ξ, z.1 ∈ Ioc 0 (1/2) := by
    apply ae_of_ae_map measurable_fst.aemeasurable
    rw [hξfst]
    exact mappedGap_support ν
  have hpos2 : ∀ᵐ z ∂κ, z.2 ∈ Ioc 0 (1/2) := by
    apply ae_of_ae_map measurable_snd.aemeasurable
    rw [hκsnd]
    exact mappedGap_support μ
  have hpos : ∀ᵐ z ∂ξ, z.1 ∈ Ioc 0 (1/2) ∧ z.2 ∈ Ioc 0 (1/2) :=
    hpos1.and ((Measure.absolutelyContinuous_of_le hξle).ae_le hpos2)
  let π := ξ.comap pairGapMap
  have hπfst : π.map Prod.fst = ν := by
    rw [(pairGap_comap_marginals ξ hpos).1, hξfst, positivePart_map]
  have hπle : π.map Prod.snd ≤ μ := by
    rw [(pairGap_comap_marginals ξ hpos).2]
    change (ξ.map Prod.snd).comap (Subtype.val : Gap → ℝ) ≤ μ
    have h := comap_mono_embedding gapEmbedding (Measure.map_mono hξle measurable_snd)
    simpa only [hκsnd, gapEmbedding.comap_map] using h
  have hπup : ∀ᵐ z ∂π, (z.1:ℝ) ≤ z.2 := by
    have h := (Measure.absolutelyContinuous_of_le hξle).ae_le hκup
    rw [← pairGap_comap_map ξ hpos] at h
    exact ae_of_ae_map pairGapEmbedding.measurable.aemeasurable h
  let μ₀ := μ - π.map Prod.snd
  have hμ : μ = π.map Prod.snd + μ₀ := by
    rw [add_comm, Measure.sub_add_cancel_of_le hπle]
  exact ⟨π, μ₀, inferInstance, inferInstance, hπup, hπfst, hμ,
    uncoupled_mass η hz1 π hπfst μ₀ μ hμ⟩

/-- The original sign law retains its total positive fraction after the
coupling is split. This identity includes the part paired with reference
mass at zero. -/
theorem coupling_sign_mass (π : Measure (Gap × Gap)) [IsFiniteMeasure π]
    (μ₀ μ : Measure Gap) [IsFiniteMeasure μ₀] (hμ : μ = π.map Prod.snd + μ₀)
    (q : SignLaw) :
    (∫ z, q.val z.2 ∂π) + (∫ d, q.val d ∂μ₀) = signMean μ q.val := by
  rw [hμ, signMean, integral_add_measure (integrable_signLaw _ q) (integrable_signLaw μ₀ q),
    integral_map measurable_snd.aemeasurable q.property.1.aestronglyMeasurable]

/-- The coupled part spends at most the original global rarity budget;
no pointwise restriction on the sign law is introduced. -/
theorem coupling_sign_budget (π : Measure (Gap × Gap)) [IsFiniteMeasure π]
    (μ₀ μ : Measure Gap) [IsFiniteMeasure μ₀] [IsFiniteMeasure μ]
    (hμ : μ = π.map Prod.snd + μ₀) (q : SignLaw) {ρ : ℝ} (hq : RarePrior μ ρ q) :
    (∫ z, q.val z.2 ∂π) ≤ ρ := by
  have hle : π.map Prod.snd ≤ μ := by rw [hμ]; exact Measure.le_add_right le_rfl
  have h := selected_signMean_le hle q hq
  rwa [integral_map measurable_snd.aemeasurable q.property.1.aestronglyMeasurable] at h

/-- An enclosed reference plan has its stated budget and risk under every
CDF-dominated true law. Only reference zero mass, not an unknown coupling
remainder, enters the unresolved-mass check. -/
theorem cdf_robust_enclosed_plan_valid (η μ : Measure Gap)
    [IsProbabilityMeasure η] [IsProbabilityMeasure μ]
    (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ]
    {z₀ : ℝ} (hz0 : 0 ≤ z₀) (hc : 0 < 1 - z₀)
    (hdesign : σ+τ+ζ = ENNReal.ofReal (1 - z₀) • η)
    (hdom : ∀ x, cdf (μ.map Subtype.val) x ≤ cdf (zeroAtomLaw z₀ η) x)
    {t ρ B : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ))
    (hN : bandEdge N < t) (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ)
    (hρ : 0 < ρ) (hρc : ρ ≤ 1 - z₀) (E : SplitEnclosure σ τ ζ N)
    (hE₀ : ζ.real univ + z₀ ≤ E.unresolved) (κ : ℕ → ℕ) {J : ℕ}
    (hκ : ∀ l, l ≤ J → E.resolvedError (4 ^ κ l) ≤ levelAccuracy ρ l/8)
    (hzJ : E.unresolved ≤ levelAccuracy ρ J/8)
    (r : Fin (J+1) → ℝ≥0) (hr : ∀ i, 0 < (r i:ℝ))
    (hwork : ∑ i : Fin (J+1), (r i:ℝ) * adjacentCost (fun l => E.price ρ l (κ l)) i.val ≤ B) :
    RareBudget μ (robustPlanEstimator η σ ht hs hN hc hρc κ r) ρ B ∧
      rareRisk μ (robustPlanEstimator η σ ht hs hN hc hρc κ r) ρ ≤
        ENNReal.ofReal (Real.sqrt (planCertificate ρ r)) := by
  obtain ⟨π, μ₀, hπf, hμ₀f, hup, href, hμ, hmass⟩ :=
    exists_robust_coupling_of_cdf η μ hz0 (by linarith) hdom
  exact robust_enclosed_plan_valid η σ τ ζ hc hdesign π hup href μ₀ μ hμ ht hs hN hτ hρ hρc E
    (by simpa only [hmass] using hE₀) κ hκ hzJ r hr hwork

/-- The planner's searched caps and allocated counts are valid under CDF
domination, for the named reference-dependent estimator. -/
theorem cdf_robust_searched_plan_valid (η μ : Measure Gap)
    [IsProbabilityMeasure η] [IsProbabilityMeasure μ]
    (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ]
    {z₀ : ℝ} (hz0 : 0 ≤ z₀) (hc : 0 < 1 - z₀)
    (hdesign : σ+τ+ζ = ENNReal.ofReal (1 - z₀) • η)
    (hdom : ∀ x, cdf (μ.map Subtype.val) x ≤ cdf (zeroAtomLaw z₀ η) x)
    {t ρ B : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ))
    (hN : bandEdge N < t) (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ)
    (hρ : 0 < ρ) (hρc : ρ ≤ 1 - z₀) (hB : 0 < B) (E : SplitEnclosure σ τ ζ N)
    (hE₀ : ζ.real univ + z₀ ≤ E.unresolved) (hvan : EnvelopeVanishes E.resolvedError)
    {J : ℕ} (hzJ : E.unresolved ≤ levelAccuracy ρ J/8)
    (w : Fin (J+1) → ℝ) (hw : ∀ i, 0 < w i) :
    RareBudget μ (robustPlanEstimator η σ ht hs hN hc hρc
        (searchCaps E.resolvedError hvan hρ)
        (planRates B (planCost E ρ (searchCaps E.resolvedError hvan hρ) J) w)) ρ B ∧
      rareRisk μ (robustPlanEstimator η σ ht hs hN hc hρc
        (searchCaps E.resolvedError hvan hρ)
        (planRates B (planCost E ρ (searchCaps E.resolvedError hvan hρ) J) w)) ρ ≤
        ENNReal.ofReal (Real.sqrt (planCertificate ρ
          (planRates B (planCost E ρ (searchCaps E.resolvedError hvan hρ) J) w))) := by
  obtain ⟨π, μ₀, hπf, hμ₀f, hup, href, hμ, hmass⟩ :=
    exists_robust_coupling_of_cdf η μ hz0 (by linarith) hdom
  exact robust_searched_plan_valid η σ τ ζ hc hdesign π hup href μ₀ μ hμ ht hs hN hτ hρ hρc
    hB E (by simpa only [hmass] using hE₀) hvan hzJ w hw

/-- One estimator fixed by the reference works under every true law whose
CDF is dominated by the reference CDF. The coupling is constructed, not
an input to this statement. -/
theorem cdf_robust_planner_rate (η : Measure Gap) [IsProbabilityMeasure η] {z₀ ρ B : ℝ}
    (hz0 : 0 ≤ z₀) (hzρ : z₀ < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) :
    ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R),
      ∀ (μ : Measure Gap) [IsProbabilityMeasure μ],
        (∀ x, cdf (μ.map Subtype.val) x ≤ cdf (zeroAtomLaw z₀ η) x) →
        RareBudget μ A ρ B ∧ rareRisk μ A ρ ≤
          ENNReal.ofReal (plannedCoefficient 28000) * zeroSelection (zeroAtomLaw z₀ η) ρ B := by
  obtain ⟨R, mR, A, hA⟩ := robust_planner_rate η hz0 hzρ hρ4 hB
  refine ⟨R, mR, A, ?_⟩
  intro μ hμprob hdom
  obtain ⟨π, μ₀, hπf, hμ₀f, hup, href, hμ, _⟩ :=
    exists_robust_coupling_of_cdf η μ hz0 (by linarith) hdom
  exact hA π μ₀ μ hup href hμ

end ThresholdHC.RobustContinuation
