import ThresholdHC.EnvelopeTransferCertificates.Transfer
open MeasureTheory
open scoped ENNReal BigOperators
open ThresholdHC.Tier6 ThresholdHC.FiniteLawCertificates ThresholdHC.EnvelopeTransferCertificates
open ThresholdHC.DeterministicCertificates ThresholdHC.ArbitraryLawAdaptation
set_option maxRecDepth 8192
set_option maxHeartbeats 12000000
private def gaps := (![(1/4:ℚ)] : Fin 1 → ℚ)
private def weights := (![(1/1:ℚ)] : Fin 1 → ℚ)
private def destinations := (![(5/16:ℚ)] : Fin 1 → ℚ)
private def roundedGaps := (![(5/16:ℚ)] : Fin 1 → ℚ)
private def roundedWeights := (![(1/1:ℚ)] : Fin 1 → ℚ)
private theorem hg : ∀ i, 0 < gaps i ∧ gaps i ≤ 1/2 := by norm_num [gaps, Fin.forall_fin_succ]
private theorem hd : ∀ i, 0 < destinations i ∧ destinations i ≤ 1/2 := by norm_num [destinations, Fin.forall_fin_succ]
private theorem hn : ∀ i, 0 < roundedGaps i ∧ roundedGaps i ≤ 1/2 := by norm_num [roundedGaps, Fin.forall_fin_succ]
private theorem hw : ∀ i, 0 ≤ weights i := by norm_num [weights, Fin.forall_fin_succ]
private noncomputable def pairs : List (Gap × Gap) := [(points gaps hg 0, points destinations hd 0)]
private noncomputable def transport := pointMap pairs
private noncomputable def law := atomicMeasure (points gaps hg) weights
private noncomputable def rounded := atomicMeasure (points roundedGaps hn) roundedWeights
private theorem bounds : ∀ x : Gap, (x:ℝ) ≤ (transport x:ℝ) ∧ (transport x:ℝ) ≤ ((5/4:ℚ):ℝ)*(x:ℝ) := by
  apply pointMap_bounds pairs (by norm_num)
  intro p hp
  simp only [pairs, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl
  all_goals norm_num [points, gaps, destinations]
private theorem bands : ∀ j, transport ⁻¹' ThresholdHC.EntropyTail.band j = ThresholdHC.EntropyTail.band j := by
  apply pointMap_bands pairs
  intro p hp
  simp only [pairs, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl
  · exact ⟨1, by norm_num [ThresholdHC.EntropyTail.band, points, gaps, destinations], by norm_num [ThresholdHC.EntropyTail.band, points, gaps, destinations]⟩
private theorem pushforward : law.map transport = rounded := by
  rw [law, map_atomic_gap _ _ transport (pointMap_measurable pairs)]
  have he : (fun i => transport (points gaps hg i)) = (fun i => points roundedGaps hn ((![0] : Fin 1 → Fin 1) i)) := by
    funext i
    fin_cases i <;> norm_num [transport, pairs, pointMap, points, gaps, destinations, roundedGaps]
  rw [he, atomic_group _ weights hw]
  congr 1
  funext j
  fin_cases j <;> norm_num [weights, roundedWeights, Fin.sum_univ_succ]
theorem certified_value : IsProbabilityMeasure law ∧ IsProbabilityMeasure rounded ∧
    (5/4:ℚ) = max ((1/1:ℚ)) ((5/4:ℚ)) ∧ (5/4:ℚ) ≤ 1+1/(1:ℚ) ∧
    (∀ i, transport (points gaps hg i) = points destinations hd i) ∧
    law.map transport = rounded ∧
    ThresholdHC.EntropyTail.selection rounded ((1/4:ℚ):ℝ) ((256/1:ℚ):ℝ) ≤
      ThresholdHC.EntropyTail.selection law ((1/4:ℚ):ℝ) ((256/1:ℚ):ℝ) ∧
    ThresholdHC.EntropyTail.selection law ((1/4:ℚ):ℝ) ((256/1:ℚ):ℝ) ≤ ENNReal.ofReal ((5/4:ℚ):ℝ)*
      ThresholdHC.EntropyTail.selection rounded ((1/4:ℚ):ℝ) ((256/1:ℚ):ℝ) := by
  have hp : IsProbabilityMeasure law := atomicMeasure_probability _ _ hw (by norm_num [weights, Fin.sum_univ_succ])
  refine ⟨hp, atomicMeasure_probability _ _ (by norm_num [roundedWeights, Fin.forall_fin_succ])
    (by norm_num [roundedWeights, Fin.sum_univ_succ]), by norm_num, by norm_num, ?_, pushforward, ?_⟩
  · intro i
    fin_cases i <;> norm_num [transport, pairs, pointMap, points, gaps, destinations]
  · let : IsProbabilityMeasure law := hp
    rw [← pushforward]
    exact ThresholdHC.SelectionStability.band_preserving_rounding law transport (pointMap_measurable pairs)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) bounds bands
#print axioms certified_value
