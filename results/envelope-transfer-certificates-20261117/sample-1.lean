import ThresholdHC.EnvelopeTransferCertificates.Transfer
open MeasureTheory
open scoped ENNReal BigOperators
open ThresholdHC.Tier6 ThresholdHC.FiniteLawCertificates ThresholdHC.EnvelopeTransferCertificates
open ThresholdHC.DeterministicCertificates ThresholdHC.ArbitraryLawAdaptation
set_option maxRecDepth 8192
set_option maxHeartbeats 12000000
private def cdf := (![(1/1:ℚ), (1/1:ℚ), (1/1:ℚ)] : Fin 3 → ℚ)
private def gaps := (![] : Fin 0 → ℚ)
private def weights := (![] : Fin 0 → ℚ)
private theorem hg : ∀ i, 0 < gaps i ∧ gaps i ≤ 1/2 := by norm_num [gaps, Fin.forall_fin_succ]
private theorem hw : ∀ i, 0 ≤ weights i := by norm_num [weights, Fin.forall_fin_succ]
private noncomputable def law := envelopeLaw (extendCDF cdf) 2
private theorem construction : law = extendedAtomic (1/1:ℚ) (points gaps hg) weights := by
  simp only [law, envelopeLaw, extendedAtomic, map_atomic _ _ Subtype.val measurable_subtype_coe]
  norm_num [extendCDF, cdf, gridPoint, gaps, weights, points, Fin.sum_univ_succ]
  <;> simp only [add_comm, add_left_comm, add_assoc]
private theorem probability : IsProbabilityMeasure law := by
  rw [construction]
  exact extendedAtomic_probability (1/1:ℚ) _ weights (by norm_num) hw
    (by norm_num [weights, Fin.sum_univ_succ])
private theorem prefix_bound : Contains ⟨(1/32:ℚ), (1/32:ℚ)⟩
    (∫ x : ℝ, (1/2-x)^2*(1/2+x)^3 ∂law) := by
  rw [construction, extended_integral (1/1:ℚ) _ weights (by norm_num) hw]
  norm_num [Contains, points, gaps, weights, Fin.sum_univ_succ]
private theorem cdf_mono : Antitone cdf := by
  norm_num [Antitone, cdf, Fin.forall_fin_succ]
private theorem domination (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hs : μ (Set.Iio 0)=0)
    (hb : ∀ j ≤ 2, μ.real (Set.Iic (gridPoint j)) ≤ extendCDF cdf j) (x : ℝ) :
    μ (Set.Iic x) ≤ law (Set.Iic x) :=
  envelopeLaw_dominates μ (extendCDF_nonneg cdf (by norm_num [cdf, Fin.forall_fin_succ]))
    (extendCDF_antitone cdf cdf_mono) (by norm_num [extendCDF, cdf]) hs 2 hb x
theorem certified_value : IsProbabilityMeasure law ∧ law = extendedAtomic (1/1:ℚ) (points gaps hg) weights ∧
    law {0} = ENNReal.ofReal ((1/1:ℚ):ℝ) ∧
    Contains ⟨(1/32:ℚ), (1/32:ℚ)⟩ (∫ x : ℝ, (1/2-x)^2*(1/2+x)^3 ∂law) ∧
    ((1/32:ℚ):ℝ)-((1/32:ℚ):ℝ) ≤ ((1/65536:ℚ):ℝ) ∧
    (∀ (μ : Measure ℝ) [IsProbabilityMeasure μ], μ (Set.Iio 0)=0 →
      (∀ j ≤ 2, μ.real (Set.Iic (gridPoint j)) ≤ extendCDF cdf j) →
      ∀ x, μ (Set.Iic x) ≤ law (Set.Iic x)) ∧

    ((1/4:ℚ):ℝ) ≤ ((1/1:ℚ):ℝ) ∧ (1/1:ℚ) = (1/1:ℚ) ∧ (0/1:ℚ) = 0 ∧ (0/1:ℚ) = 0 ∧ (0/1:ℚ) = 0 ∧
    zeroSelection law ((1/4:ℚ):ℝ) ((256/1:ℚ):ℝ) = ENNReal.ofReal ((1/4:ℚ):ℝ) := by
  refine ⟨probability, construction, ?_, prefix_bound, by norm_num, domination, ?_⟩
  · rw [construction, extendedAtomic_zero]
  · refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
    rw [construction]
    exact fallback_selection (1/1:ℚ) _ weights (by norm_num) (by norm_num) (by norm_num)
#print axioms certified_value
