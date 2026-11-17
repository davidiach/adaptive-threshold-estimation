import ThresholdHC.EnvelopeTransferCertificates.Transfer
open MeasureTheory
open scoped ENNReal BigOperators
open ThresholdHC.Tier6 ThresholdHC.FiniteLawCertificates ThresholdHC.EnvelopeTransferCertificates
open ThresholdHC.DeterministicCertificates ThresholdHC.ArbitraryLawAdaptation
set_option maxRecDepth 8192
set_option maxHeartbeats 12000000
private def cdf := (![(1/1:ℚ), (1/2:ℚ), (1/8:ℚ)] : Fin 3 → ℚ)
private def gaps := (![(1/8:ℚ), (1/4:ℚ)] : Fin 2 → ℚ)
private def weights := (![(3/8:ℚ), (1/2:ℚ)] : Fin 2 → ℚ)
private theorem hg : ∀ i, 0 < gaps i ∧ gaps i ≤ 1/2 := by norm_num [gaps, Fin.forall_fin_succ]
private theorem hw : ∀ i, 0 ≤ weights i := by norm_num [weights, Fin.forall_fin_succ]
private noncomputable def law := envelopeLaw (extendCDF cdf) 2
private theorem construction : law = extendedAtomic (1/8:ℚ) (points gaps hg) weights := by
  simp only [law, envelopeLaw, extendedAtomic, map_atomic _ _ Subtype.val measurable_subtype_coe]
  norm_num [extendCDF, cdf, gridPoint, gaps, weights, points, Fin.sum_univ_succ]
  <;> simp only [add_comm, add_left_comm, add_assoc]
private theorem probability : IsProbabilityMeasure law := by
  rw [construction]
  exact extendedAtomic_probability (1/8:ℚ) _ weights (by norm_num) hw
    (by norm_num [weights, Fin.sum_univ_succ])
private theorem prefix_bound : Contains ⟨(7855/262144:ℚ), (7855/262144:ℚ)⟩
    (∫ x : ℝ, (1/2-x)^2*(1/2+x)^3 ∂law) := by
  rw [construction, extended_integral (1/8:ℚ) _ weights (by norm_num) hw]
  norm_num [Contains, points, gaps, weights, Fin.sum_univ_succ]
private theorem cdf_mono : Antitone cdf := by
  norm_num [Antitone, cdf, Fin.forall_fin_succ]
private theorem domination (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hs : μ (Set.Iio 0)=0)
    (hb : ∀ j ≤ 2, μ.real (Set.Iic (gridPoint j)) ≤ extendCDF cdf j) (x : ℝ) :
    μ (Set.Iic x) ≤ law (Set.Iic x) :=
  envelopeLaw_dominates μ (extendCDF_nonneg cdf (by norm_num [cdf, Fin.forall_fin_succ]))
    (extendCDF_antitone cdf cdf_mono) (by norm_num [extendCDF, cdf]) hs 2 hb x
private def normalizedWeights := (![(3/7:ℚ), (4/7:ℚ)] : Fin 2 → ℚ)
private def selected := (![(1/1:ℚ), (1/1:ℚ)] : Fin 2 → ℚ)
private def labels := (![1, 2] : Fin 2 → ℕ)
private theorem bands_cover : ∀ i, ∃ j, inBand (gaps i) (labels j) = true := by
  norm_num [gaps, labels, inBand, Fin.forall_fin_succ, Fin.exists_fin_succ]
private theorem hs : ∀ i, 0 ≤ selected i ∧ selected i ≤ 1 := by norm_num [selected, Fin.forall_fin_succ]
private theorem hws (i) : 0 ≤ weights i*selected i := mul_nonneg (hw i) (hs i).1
private theorem hn : ∀ i, 0 ≤ normalizedWeights i := by norm_num [normalizedWeights, Fin.forall_fin_succ]
private theorem normalization : normalizedWeights = (fun i => weights i/(1-(1/8:ℚ))) := by
  funext i
  fin_cases i <;> norm_num [weights, normalizedWeights]
private noncomputable def positivePartLaw := atomicMeasure (points gaps hg) weights
private noncomputable def conditionalLaw := atomicMeasure (points gaps hg) normalizedWeights
private theorem conditional_probability : IsProbabilityMeasure conditionalLaw :=
  atomicMeasure_probability _ _ hn (by norm_num [normalizedWeights, Fin.sum_univ_succ])
private theorem split_rarity : conditionalRarity ((1/4:ℚ):ℝ) ((1/8:ℚ):ℝ) = ((1/7:ℚ):ℝ) := by
  norm_num [conditionalRarity]
private noncomputable def core := ENNReal.ofReal (1-((1/8:ℚ):ℝ)) •
  ThresholdHC.EntropyTailQuantile.quantileCore conditionalLaw (conditionalRarity ((1/4:ℚ):ℝ) ((1/8:ℚ):ℝ))
private noncomputable def tail := (positivePartLaw-core).restrict {x : Gap | 1 ≤ ((64/1:ℚ):ℝ)*(x:ℝ)^2}
private noncomputable def unresolved := (positivePartLaw-core).restrict {x : Gap | ((64/1:ℚ):ℝ)*(x:ℝ)^2 < 1}
private theorem core_eq : core = atomicMeasure (points gaps hg) (fun i => weights i*selected i) := by
  rw [core, conditionalLaw, normalization, split_rarity]
  apply scaled_core (1/8:ℚ) _ weights selected (by norm_num)
  apply quantileCore_atomic (points gaps hg) (fun i => weights i/(1-(1/8:ℚ))) selected
    (by norm_num [gaps, weights, selected, normalizedWeights, points, Fin.sum_univ_succ, Fin.forall_fin_succ]) (by norm_num [gaps, weights, selected, normalizedWeights, points, Fin.sum_univ_succ, Fin.forall_fin_succ])
    (ρ := ((1/7:ℚ):ℝ)) (t := ((1/8:ℚ):ℝ)) (by norm_num) (by norm_num)
    (1/3:ℚ) (by norm_num)
  all_goals norm_num [gaps, weights, selected, normalizedWeights, points, Fin.sum_univ_succ, Fin.forall_fin_succ]
private theorem tail_eq : tail = atomicMeasure (points gaps hg) (tailWeights gaps weights selected (64/1:ℚ)) := by
  rw [tail, core_eq]
  exact tailMeasure_eq gaps weights selected (64/1:ℚ) hg hw hs
private theorem unresolved_eq : unresolved = atomicMeasure (points gaps hg) (unresolvedWeights gaps weights selected (64/1:ℚ)) := by
  rw [unresolved, core_eq]
  exact unresolvedMeasure_eq gaps weights selected (64/1:ℚ) hg hw hs
private theorem resolved_eq : core+tail = atomicMeasure (points gaps hg) (resolvedWeights gaps weights selected (64/1:ℚ)) := by
  rw [tail, core_eq]
  exact resolvedMeasure_eq gaps weights selected (64/1:ℚ) hg hw hs
theorem certified_value : IsProbabilityMeasure law ∧ law = extendedAtomic (1/8:ℚ) (points gaps hg) weights ∧
    law {0} = ENNReal.ofReal ((1/8:ℚ):ℝ) ∧
    Contains ⟨(7855/262144:ℚ), (7855/262144:ℚ)⟩ (∫ x : ℝ, (1/2-x)^2*(1/2+x)^3 ∂law) ∧
    ((7855/262144:ℚ):ℝ)-((7855/262144:ℚ):ℝ) ≤ ((1/65536:ℚ):ℝ) ∧
    (∀ (μ : Measure ℝ) [IsProbabilityMeasure μ], μ (Set.Iio 0)=0 →
      (∀ j ≤ 2, μ.real (Set.Iic (gridPoint j)) ≤ extendCDF cdf j) →
      ∀ x, μ (Set.Iic x) ≤ law (Set.Iic x)) ∧

    ((1/8:ℚ):ℝ) < ((1/4:ℚ):ℝ) ∧ IsProbabilityMeasure conditionalLaw ∧
    law = zeroAtomLaw ((1/8:ℚ):ℝ) conditionalLaw ∧
    conditionalRarity ((1/4:ℚ):ℝ) ((1/8:ℚ):ℝ) = ((1/7:ℚ):ℝ) ∧
    ThresholdHC.EntropyTailQuantile.quantileThreshold conditionalLaw ((1/7:ℚ):ℝ) = ((1/8:ℚ):ℝ) ∧
    core = atomicMeasure (points gaps hg) (fun i => weights i*selected i) ∧
    (∀ i, ∃ j, inBand (gaps i) (labels j) = true) ∧
    (∀ j, ThresholdHC.EntropyTail.bandCost core (labels j) = ENNReal.ofReal ((![(8/1:ℚ), (16/1:ℚ)] : Fin 2 → ℚ) j:ℝ)) ∧
    ((1/8:ℚ):ℝ)+unresolved.real Set.univ = ((1/8:ℚ):ℝ) ∧
    (∫ x : Gap, (x:ℝ)⁻¹ ∂tail) = ((1/1:ℚ):ℝ) ∧
    (∫ x : Gap, min 1 (1/(((1024/1:ℚ):ℝ)*(x:ℝ)^2)^2) ∂(core+tail)) = ((13/8192:ℚ):ℝ) ∧
    Contains ⟨(0/1:ℚ), (128/1:ℚ)⟩ (tailWorkIntegral tail ((1024/1:ℚ):ℝ)) := by
  refine ⟨probability, construction, ?_, prefix_bound, by norm_num, domination, ?_⟩
  · rw [construction, extendedAtomic_zero]
  · refine ⟨by norm_num, conditional_probability, ?_, split_rarity, ?_, core_eq, bands_cover, ?_, ?_, ?_, ?_, ?_⟩
    · rw [construction, normalized_identity (1/8:ℚ) _ weights (by norm_num), conditionalLaw, normalization]
    · let : IsProbabilityMeasure conditionalLaw := conditional_probability
      apply quantileThreshold_eq_of_mass conditionalLaw (ρ := ((1/7:ℚ):ℝ)) (by norm_num) (by norm_num)
      all_goals rw [conditionalLaw, atomicMeasure_real _ _ hn]
      all_goals norm_num [gaps, weights, selected, normalizedWeights, points, Fin.sum_univ_succ, Fin.forall_fin_succ]
    · intro j
      rw [core_eq, bandCost_atomic _ _ hws]
      fin_cases j <;> norm_num [labels, ThresholdHC.EntropyTail.band, gaps, weights, selected, normalizedWeights, points, Fin.sum_univ_succ, Fin.forall_fin_succ]
    · rw [unresolved_eq, atomicMeasure_real _ _ (by norm_num [unresolvedWeights, gaps, weights, selected, normalizedWeights, points, Fin.sum_univ_succ, Fin.forall_fin_succ])]
      norm_num [unresolvedWeights, gaps, weights, selected, normalizedWeights, points, Fin.sum_univ_succ, Fin.forall_fin_succ]
    · rw [tail_eq, inverseIntegral_eq gaps _ hg (tailWeights_nonneg gaps weights selected (64/1:ℚ) hw hs)]
      norm_num [inverseValue, tailWeights, gaps, weights, selected, normalizedWeights, points, Fin.sum_univ_succ, Fin.forall_fin_succ]
    · rw [resolved_eq, errorIntegral_eq gaps _ (1024/1:ℚ) hg (by intro i; exact add_nonneg (hws i) (tailWeights_nonneg gaps weights selected (64/1:ℚ) hw hs i))]
      norm_num [errorValue, resolvedWeights, tailWeights, gaps, weights, selected, normalizedWeights, points, Fin.sum_univ_succ, Fin.forall_fin_succ]
    · rw [tail_eq]
      apply tailWork_accepted_sound gaps _ (1024/1:ℚ) hg (tailWeights_nonneg gaps weights selected (64/1:ℚ) hw hs) (c := (.binary ⟨(0/1:ℚ), (128/1:ℚ)⟩ (.unary ⟨(0/1:ℚ), (0/1:ℚ)⟩ (.binary ⟨(1024/1:ℚ), (1024/1:ℚ)⟩ (.leaf ⟨(1024/1:ℚ), (1024/1:ℚ)⟩) (.unary ⟨(314180672/76545:ℚ), (2827664128/688905:ℚ)⟩ (.binary ⟨(288769/76545:ℚ), (2598956/688905:ℚ)⟩ (.leaf ⟨(1/1:ℚ), (1/1:ℚ)⟩) (.binary ⟨(212224/76545:ℚ), (1910051/688905:ℚ)⟩ (.leaf ⟨(0/1:ℚ), (0/1:ℚ)⟩) (.logarithm ⟨(212224/76545:ℚ), (1910051/688905:ℚ)⟩ ⟨4, 12⟩ ⟨4, 12⟩ (.leaf ⟨(16/1:ℚ), (16/1:ℚ)⟩))))))) (.binary ⟨(0/1:ℚ), (0/1:ℚ)⟩ (.unary ⟨(0/1:ℚ), (0/1:ℚ)⟩ (.binary ⟨(1024/1:ℚ), (1024/1:ℚ)⟩ (.leaf ⟨(1024/1:ℚ), (1024/1:ℚ)⟩) (.unary ⟨(35802544/25515:ℚ), (322227656/229635:ℚ)⟩ (.binary ⟨(131627/25515:ℚ), (2369321/459270:ℚ)⟩ (.leaf ⟨(1/1:ℚ), (1/1:ℚ)⟩) (.binary ⟨(106112/25515:ℚ), (1910051/459270:ℚ)⟩ (.leaf ⟨(0/1:ℚ), (0/1:ℚ)⟩) (.logarithm ⟨(106112/25515:ℚ), (1910051/459270:ℚ)⟩ ⟨6, 12⟩ ⟨6, 12⟩ (.leaf ⟨(64/1:ℚ), (64/1:ℚ)⟩))))))) (.leaf ⟨(0/1:ℚ), (0/1:ℚ)⟩))))
      norm_num [gaps, weights, selected, normalizedWeights, points, Fin.sum_univ_succ, Fin.forall_fin_succ, accepted, check, Evidence.bounds, encloses, point, sqrtCheck,
  logCheck, logRange, logBounds, add, scale, unitLog, Finset.sum_range_succ,
  entropyExpr, sumExpr, List.ofFn_succ, Fin.sum_univ_succ, objectiveExpr, costs, inBand, imin, imax, tailWorkExpr, tailWeights]
#print axioms certified_value
