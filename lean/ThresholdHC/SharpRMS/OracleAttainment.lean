import ThresholdHC.SharpRMS.OracleBounds
import ThresholdHC.SharpRMS.FreshLabels

/-! Four fresh endpoint coins attain the sharp coefficient in both magnitude oracles. -/
noncomputable section
namespace ThresholdHC.SharpRMS
open MeasureTheory Tier3 Tier5 Tier6 OracleLower ObservableSimulation
open scoped ENNReal

private def revealedFour : RevealedEstimator Unit where
  randomLaw := fourFlips.randomLaw
  probability := inferInstance
  policy := populationPolicy fourFlips
  policy_measurable := measurable_populationPolicy fourFlips
  output := populationOutput fourFlips
  output_measurable := measurable_populationOutput fourFlips

private def selectedFour : SelectedEstimator Unit where
  randomLaw := Measure.dirac ()
  probability := inferInstance
  request := fun _ xs => if xs.length < 4 then some none else none
  request_measurable := fun _ => measurable_const
  newGap := fun _ _ => endpointGap
  newGap_measurable := fun _ => measurable_const
  reuse_valid := by intro r xs j h; split at h <;> simp at h
  output := fourFlips.output
  output_measurable := fourFlips.output_measurable

private theorem selected_policy (r : Unit) (xs : List Bool) :
    (selectedOracle selectedFour).policy r xs = fourPolicy Encodable.encode xs := by
  by_cases h : xs.length < 4 <;> simp [selectedOracle,selectedFour,selectedLabel,fourPolicy,h]

private theorem selected_joint (q : SignLaw) :
    oracleLaw (selectedOracle selectedFour) q =
    (experimentLaw (Measure.dirac endpointGap) fourFlips q).map (fun z => (z.1.1,z.2)) := by
  let P := experimentLaw (Measure.dirac endpointGap) fourFlips q
  let A := selectedOracle selectedFour
  have hp := (oracle_realization Unit A q).2
  have hseed : populationSeedLaw (Measure.dirac endpointGap) fourFlips =
      Measure.dirac ((),fun _ => endpointGap) := by
    simp [populationSeedLaw,fourFlips,Measure.infinitePi_dirac,Measure.dirac_prod_dirac]
  have hreal : RealizesCreationPrefixes A.randomLaw P (fun z => z.1.1) Prod.snd
      A.policy (fun r i => (A.gap r i).val) (fun r i => q.val (A.gap r i)) := by
    intro n f mf bound
    have h := (population_realization Unit (Measure.dirac endpointGap) fourFlips q).2 n
      (fun z w => f z.1 w) (fun w => (mf w).comp measurable_fst)
      (by obtain ⟨C,hC⟩ := bound; exact ⟨C,fun z w => hC z.1 w⟩)
    rw [hseed,integral_dirac] at h
    change (∫ z, f z.1.1 (processPrefix n z.2) ∂P) = ∫ r, _ ∂Measure.dirac ()
    rw [integral_dirac]
    apply h.trans
    apply Finset.sum_congr rfl
    intro w _
    apply congrArg (fun x : ℝ => x*f () w)
    change creationLaw (freshPolicy 3) (fun _ => 1/2) (fun _ => q.val endpointGap) w =
      creationLaw ((selectedOracle selectedFour).policy ()) (fun _ => 1/2) (fun _ => q.val endpointGap) w
    rw [show (selectedOracle selectedFour).policy () = fourPolicy Encodable.encode by funext xs; exact selected_policy () xs]
    exact (fresh_labels_word w _ (q.property.2 endpointGap)).symm
  have eq := realizes_creation_joint_law_unique A.randomLaw (oracleLaw A q) P
    Prod.fst Prod.snd (fun z => z.1.1) Prod.snd A.policy _ _ measurable_fst measurable_snd
    (measurable_fst.comp measurable_fst) measurable_snd hp hreal
  change (oracleLaw A q).map id = _ at eq
  simpa only [Measure.map_id] using eq

private theorem four_rms :
    maximalRMSRisk (Measure.dirac endpointGap) fourFlips ≤ ENNReal.ofReal (1/6:ℝ) := by
  apply iSup_le
  intro q
  apply HardBudget.rms_from_square _ _ _ _ (by norm_num)
  rw [four_flips_squared_risk]
  norm_num

private theorem selected_budget : OracleBudget (selectedOracle selectedFour) 4 := by
  intro q
  unfold oracleWork
  rw [selected_joint,lintegral_map]
  · exact four_flips_budget (Measure.dirac endpointGap) q
  · exact measurable_totalProcessWork Prod.snd (fun n b => measurableSet_eq_fun
      ((measurable_pi_apply n).comp measurable_snd) measurable_const)
  · exact (measurable_fst.comp measurable_fst).prodMk measurable_snd

private theorem selected_rms : oracleRisk (Measure.dirac endpointGap) (selectedOracle selectedFour) ≤
    ENNReal.ofReal (1/6:ℝ) := by
  apply le_trans _ four_rms
  apply iSup_le
  intro q
  apply le_iSup_of_le q
  apply le_of_eq
  unfold rootMeanRisk
  congr 1
  unfold squaredRisk
  rw [selected_joint,lintegral_map]
  · rfl
  · exact ENNReal.measurable_ofReal.comp (((selectedOracle selectedFour).output_measurable.sub measurable_const).pow_const 2)
  · exact (measurable_fst.comp measurable_fst).prodMk measurable_snd

theorem oracle_endpoint_eq :
    revealedMinimaxRisk (Measure.dirac endpointGap) 4 = ENNReal.ofReal (1/6:ℝ) ∧
    selectedMinimaxRisk (Measure.dirac endpointGap) 4 = ENNReal.ofReal (1/6:ℝ) := by
  have m : modulus (Measure.dirac endpointGap) (1/Real.sqrt 4) = 1 := by
    norm_num [modulus,clippedGap,endpointGap,Real.sqrt_eq_iff_mul_self_eq]
  have low := oracle_minimax_lower (Measure.dirac endpointGap) 4 (by norm_num)
  rw [m] at low
  constructor
  · refine le_antisymm (le_trans (sInf_le ?_) four_rms) low.1
    exact ⟨Unit,inferInstance,revealedFour,four_flips_budget (Measure.dirac endpointGap),rfl⟩
  · refine le_antisymm (le_trans (sInf_le ?_) selected_rms) low.2
    exact ⟨Unit,inferInstance,selectedFour,selected_budget,rfl⟩

end ThresholdHC.SharpRMS
