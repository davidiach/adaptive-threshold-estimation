import ThresholdHC.FiniteLawCertificates.Oracles
open MeasureTheory
open scoped ENNReal BigOperators
open ThresholdHC.FiniteLawCertificates ThresholdHC.DeterministicCertificates
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
private def gaps := (![(1/8:ℚ), (1/2:ℚ)] : Fin 2 → ℚ)
private def weights := (![(1/3:ℚ), (2/3:ℚ)] : Fin 2 → ℚ)
private def labels := (![0, 2] : Fin 2 → ℕ)
private theorem gaps_valid : ∀ i, 0 < gaps i ∧ gaps i ≤ 1/2 := by norm_num [gaps, Fin.forall_fin_succ]
private theorem weights_valid : ∀ i, 0 ≤ weights i := by norm_num [weights, Fin.forall_fin_succ]
private theorem weights_sum : ∑ i, weights i = 1 := by norm_num [weights, Fin.sum_univ_succ]
private noncomputable def law := atomicMeasure (points gaps gaps_valid) weights
private def selected := (![(1/2:ℚ), (1/4:ℚ)] : Fin 2 → ℚ)
private theorem selected_valid : ∀ i, 0 ≤ selected i ∧ selected i ≤ 1 := by
  norm_num [selected, Fin.forall_fin_succ]
private theorem labels_injective : Function.Injective labels := by
  intro i j h
  fin_cases i <;> fin_cases j <;> norm_num [labels] at *
private theorem bands_cover : ∀ i, ∃ j, inBand (gaps i) (labels j) = true := by
  norm_num [gaps, labels, inBand, Fin.forall_fin_succ, Fin.exists_fin_succ]
theorem certified_value : IsProbabilityMeasure law ∧
    atomicMeasure (points gaps gaps_valid) (fun i => weights i*selected i) ≤ law ∧
    Contains ⟨(1/4:ℚ), (1/4:ℚ)⟩ (min (ENNReal.ofReal ((1/4:ℚ):ℝ))
      (ThresholdHC.EntropyTail.selectionObjective law ((1/4:ℚ):ℝ) ((256/1:ℚ):ℝ)
        (atomicMeasure (points gaps gaps_valid) (fun i => weights i*selected i)))).toReal ∧
    (ThresholdHC.EntropyTail.selection law ((1/4:ℚ):ℝ) ((256/1:ℚ):ℝ)).toReal ≤ ((1/4:ℚ):ℝ) := by
  have hc : accepted (objectiveExpr gaps weights selected labels (1/4:ℚ) (256/1:ℚ)) ⟨(1/4:ℚ), (1/4:ℚ)⟩
      (.binary ⟨(1/4:ℚ), (1/4:ℚ)⟩ (.leaf ⟨(1/4:ℚ), (1/4:ℚ)⟩) (.binary ⟨(412421/1572864:ℚ), (824845/3145728:ℚ)⟩ (.unary ⟨(61015/524288:ℚ), (122031/1048576:ℚ)⟩ (.unary ⟨(31030936507411/2291167494443520:ℚ), (8936931539765923/659856238399733760:ℚ)⟩ (.binary ⟨(62061873014822/4474936512585:ℚ), (8936931539765923/644390857812240:ℚ)⟩ (.leaf ⟨(34/3:ℚ), (34/3:ℚ)⟩) (.binary ⟨(11345925872192/4474936512585:ℚ), (1633835151227203/644390857812240:ℚ)⟩ (.unary ⟨(187825592128/99443033613:ℚ), (459805294767919/243436546284624:ℚ)⟩ (.logarithm ⟨(93912796064/33147677871:ℚ), (459805294767919/162291030856416:ℚ)⟩ ⟨4, 12⟩ ⟨4, 12⟩ (.leaf ⟨(17/1:ℚ), (17/1:ℚ)⟩))) (.binary ⟨(2893774226432/4474936512585:ℚ), (442747456644131/684665286425505:ℚ)⟩ (.unary ⟨(2893774226432/4474936512585:ℚ), (442747456644131/684665286425505:ℚ)⟩ (.logarithm ⟨(90430444576/1491645504195:ℚ), (442747456644131/7303096388538720:ℚ)⟩ ⟨0, 12⟩ ⟨0, 12⟩ (.leaf ⟨(17/16:ℚ), (17/16:ℚ)⟩))) (.leaf ⟨(0/1:ℚ), (0/1:ℚ)⟩)))))) (.binary ⟨(7/48:ℚ), (7/48:ℚ)⟩ (.unary ⟨(1/12:ℚ), (1/12:ℚ)⟩ (.binary ⟨(1/2:ℚ), (1/2:ℚ)⟩ (.leaf ⟨(1/1:ℚ), (1/1:ℚ)⟩) (.unary ⟨(1/2:ℚ), (1/2:ℚ)⟩ (.leaf ⟨(1/4:ℚ), (1/4:ℚ)⟩)))) (.binary ⟨(1/16:ℚ), (1/16:ℚ)⟩ (.unary ⟨(1/16:ℚ), (1/16:ℚ)⟩ (.binary ⟨(1/8:ℚ), (1/8:ℚ)⟩ (.leaf ⟨(1/1:ℚ), (1/1:ℚ)⟩) (.unary ⟨(1/8:ℚ), (1/8:ℚ)⟩ (.leaf ⟨(1/64:ℚ), (1/64:ℚ)⟩)))) (.leaf ⟨(0/1:ℚ), (0/1:ℚ)⟩))))) = true := by
    norm_num [gaps, weights, selected, labels, accepted, check, Evidence.bounds, encloses, point, sqrtCheck,
  logCheck, logRange, logBounds, add, scale, unitLog, Finset.sum_range_succ,
  entropyExpr, sumExpr, List.ofFn_succ, Fin.sum_univ_succ, objectiveExpr, costs, inBand, imin, imax, tailWorkExpr, tailWeights]
  exact ⟨atomicMeasure_probability _ _ weights_valid weights_sum,
    selected_le _ weights selected weights_valid selected_valid,
    objective_accepted_sound gaps weights selected labels (1/4:ℚ) (256/1:ℚ) gaps_valid weights_valid
      selected_valid (by norm_num) (by norm_num) labels_injective bands_cover hc,
    selection_upper gaps weights selected labels (1/4:ℚ) (256/1:ℚ) gaps_valid weights_valid
      selected_valid (by norm_num) (by norm_num) labels_injective bands_cover hc⟩
#print axioms certified_value
