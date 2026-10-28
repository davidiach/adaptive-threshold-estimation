import ThresholdHC.OracleLower.Realization
import ThresholdHC.Tier6.AlgorithmNonempty

noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace ThresholdHC.OracleLower
open ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.Tier6

theorem oracle_stops_of_budget {R : Type} [MeasurableSpace R]
    (A : OracleEstimator R) (B : ℝ) (hb : OracleBudget A B) (q : SignLaw) :
    ∀ᵐ z ∂oracleLaw A q, ∃ n, A.policy z.1 (processHistory z.2 n) = none :=
  creation_stops R (R × ProcessTape) A.randomLaw (oracleLaw A q) Prod.fst Prod.snd
    A.policy (fun r i => A.gap r i) (fun r i => q.val (A.gap r i))
    measurable_fst (fun n _ => measurableSet_eq_fun
      ((measurable_pi_apply n).comp measurable_snd) measurable_const)
    A.policy_measurable (oracle_realization R A q).2
    (lt_of_le_of_lt (hb q) ENNReal.ofReal_lt_top)

theorem oracle_work_zero {R : Type} [MeasurableSpace R]
    (A : OracleEstimator R) (hstop : ∀ r xs, A.policy r xs = none) (q : SignLaw) :
    oracleWork A q = 0 := by
  have hv : ∀ᵐ z ∂oracleLaw A q, ∀ n,
      (z.2 n).isSome = (A.policy z.1 (processHistory z.2 n)).isSome := by
    apply ae_all_iff.mpr
    intro n
    exact realized_creation_valid_step A.randomLaw (oracleLaw A q) Prod.fst Prod.snd
      A.policy (fun r i => A.gap r i) (fun r i => q.val (A.gap r i))
      measurable_fst (fun k b => measurableSet_eq_fun
        ((measurable_pi_apply k).comp measurable_snd) measurable_const)
      A.policy_measurable (oracle_realization R A q).2 n
  have hz : ∀ᵐ z ∂oracleLaw A q, totalProcessWork z.2 = 0 := by
    filter_upwards [hv] with z hz
    have hzero (n : ℕ) : (z.2 n).isSome = false := by simpa only [hstop,Option.isSome_none] using hz n
    simp [totalProcessWork,ThresholdHC.workOf,processPrefix,hzero]
  unfold oracleWork
  calc
    _ = ∫⁻ _z, (0 : ℝ≥0∞) ∂oracleLaw A q := lintegral_congr_ae hz
    _ = 0 := by simp

theorem oracle_zero_output_bounds {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : OracleEstimator R)
    (hout : ∀ z, A.output z = 0) (δ : ℝ) :
    oracleRisk μ A ≤ 1 ∧ OracleConfidence μ A 1 δ := by
  constructor
  · apply iSup_le
    intro q
    have hm := signMean_bounds μ q
    unfold rootMeanRisk
    apply ENNReal.rpow_le_one ?_ (by norm_num)
    have he : squaredRisk (oracleLaw A q) A.output (signMean μ q.val) =
        ENNReal.ofReal ((signMean μ q.val)^2) := by simp [squaredRisk,hout]
    rw [he]
    have hs : (signMean μ q.val)^2 ≤ 1 := by nlinarith [hm.1,hm.2]
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hs
  · intro q
    have hm := signMean_bounds μ q
    have he : {z | (1 : ℝ) < |A.output z-signMean μ q.val|} = ∅ := by
      ext z
      simp only [hout,zero_sub,abs_neg,abs_of_nonneg hm.1,Set.mem_ofPred_eq,
        Set.mem_empty_iff_false,iff_false]
      exact not_lt_of_ge hm.2
    rw [he,measure_empty]
    exact bot_le

def idleRevealed : RevealedEstimator Unit where
  randomLaw := Measure.dirac ()
  probability := inferInstance
  policy := fun _ _ => none
  policy_measurable := fun _ _ => measurableSet_eq_fun measurable_const measurable_const
  output := fun _ => 0
  output_measurable := measurable_const

def idleSelected : SelectedEstimator Unit where
  randomLaw := Measure.dirac ()
  probability := inferInstance
  request := fun _ _ => none
  request_measurable := fun _ => measurable_const
  newGap := fun _ _ => ⟨1/2,by norm_num,le_rfl⟩
  newGap_measurable := fun _ => measurable_const
  reuse_valid := by intro _ _ _ h; simp at h
  output := fun _ => 0
  output_measurable := measurable_const

theorem oracle_nonvacuity : OracleNonvacuityStatement := by
  intro μ _ B δ hB hδ
  have hbr : OracleBudget (revealedOracle μ idleRevealed) B := by
    intro q
    rw [oracle_work_zero _ (fun _ _ => rfl)]
    exact bot_le
  have hbs : OracleBudget (selectedOracle idleSelected) B := by
    intro q
    rw [oracle_work_zero _ (fun _ _ => rfl)]
    exact bot_le
  have hr := oracle_zero_output_bounds μ (revealedOracle μ idleRevealed) (fun _ => rfl) δ
  have hs := oracle_zero_output_bounds μ (selectedOracle idleSelected) (fun _ => rfl) δ
  refine ⟨⟨idleRevealed,hbr,hr⟩,⟨idleSelected,hbs,hs⟩,?_,?_,?_,?_⟩
  · apply le_trans ?_ hr.1
    exact sInf_le ⟨Unit,inferInstance,idleRevealed,hbr,rfl⟩
  · apply le_trans ?_ hs.1
    exact sInf_le ⟨Unit,inferInstance,idleSelected,hbs,rfl⟩
  · apply sInf_le
    exact ⟨Unit,inferInstance,idleRevealed,1,by norm_num,hbr,hr.2,by simp⟩
  · apply sInf_le
    exact ⟨Unit,inferInstance,idleSelected,1,by norm_num,hbs,hs.2,by simp⟩

end ThresholdHC.OracleLower
