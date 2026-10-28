import ThresholdHC.CriticalEntropy.CriticalAlgorithmLower
import ThresholdHC.CriticalEntropy.CriticalRate

noncomputable section

namespace ThresholdHC.CriticalEntropy
open MeasureTheory Set ThresholdHC.Tier3
open scoped ENNReal
set_option maxHeartbeats 2000000

/-- The critical lower rate for every admissible observable adaptive estimator,
allowing arbitrary independent random seeds and unrestricted creation/stopping. -/
theorem critical_algorithm_lower_bound : ∃ c : ℝ, 0 < c ∧
    ∀ (ρ : unitInterval), 0 < (ρ : ℝ) → (ρ : ℝ) ≤ 1/4 →
    ∀ B : ℝ, 1 ≤ B → ∀ (R : Type) [MeasurableSpace R]
      (A : Tier6.AdaptiveEstimator R), CriticalUniformBudget A (ρ : ℝ) B →
      ENNReal.ofReal (c*min (ρ : ℝ)
        (Real.sqrt ((ρ : ℝ)*criticalLogFactor (ρ : ℝ)/B))) ≤
          criticalMaximalRMSRisk A (ρ : ℝ) := by
  obtain ⟨C,hC,halg⟩ := critical_algorithm_lower_at_separation
  obtain ⟨c,hc,hrate⟩ := critical_rate_separation C hC
  refine ⟨c,hc,?_⟩
  intro ρ hρ hρ' B hB R _ A hbudget
  obtain ⟨δ,hδ,hδρ,hinfo,hscale⟩ := hrate (ρ : ℝ)
    ((ρ : ℝ)*criticalLogFactor (ρ : ℝ)) B hρ
    (mul_pos hρ (criticalLogFactor_pos (ρ : ℝ) hρ ρ.property.2)) (by linarith)
  exact (ENNReal.ofReal_le_ofReal hscale).trans
    (halg ρ hρ hρ' δ B hδ hδρ (by linarith) hinfo R A hbudget)

/-- The full critical minimax lower bound, including the saturated regime.
The supremum ranges over all measurable [0,1]-valued rare priors. -/
theorem critical_minimax_lower_bound : ∃ c : ℝ, 0 < c ∧
    ∀ (ρ : unitInterval), 0 < (ρ : ℝ) → (ρ : ℝ) ≤ 1/4 →
    ∀ B : ℝ, 1 ≤ B →
      ENNReal.ofReal (c*min (ρ : ℝ)
        (Real.sqrt ((ρ : ℝ)*criticalLogFactor (ρ : ℝ)/B))) ≤
          criticalMinimaxRisk (ρ : ℝ) B := by
  obtain ⟨c,hc,halg⟩ := critical_algorithm_lower_bound
  refine ⟨c,hc,?_⟩
  intro ρ hρ hρ' B hB
  apply le_sInf
  rintro r ⟨R,hR,A,hbudget,rfl⟩
  exact halg ρ hρ hρ' B hB R A hbudget

def criticalZeroEstimator : Tier6.AdaptiveEstimator Unit where
  randomLaw := Measure.dirac ()
  probability := inferInstance
  policy := fun _ _ => none
  policy_measurable := by
    intro xs a
    exact measurableSet_eq_fun measurable_const measurable_const
  output := fun _ => 0
  output_measurable := measurable_const

theorem criticalZeroEstimator_work (q : ℝ → unitInterval) (hq : Measurable q) :
    criticalExpectedWork criticalZeroEstimator q hq = 0 := by
  have hv : ∀ᵐ z ∂criticalExperimentLaw criticalZeroEstimator q hq, ∀ n,
      (z.2 n).isSome = false := by
    apply ae_all_iff.mpr
    intro n
    have hv := Tier5.realized_creation_valid_step
      (criticalZeroEstimator.randomLaw.prod (Measure.infinitePi (fun _ : ℕ => criticalGapLaw)))
      (criticalExperimentLaw criticalZeroEstimator q hq) Prod.fst Prod.snd
      (fun z : Unit × (ℕ → ℝ) => criticalZeroEstimator.policy z.1)
      (fun z i => criticalClippedGap (z.2 i)) (fun z i => (q (z.2 i) : ℝ))
      measurable_fst critical_tape_measurable
      (fun xs a => measurable_fst (criticalZeroEstimator.policy_measurable xs a))
      (criticalExperimentLaw_realizes criticalZeroEstimator q hq) n
    simpa only [criticalZeroEstimator,Option.isSome_none] using hv
  have hz : ∀ᵐ z ∂criticalExperimentLaw criticalZeroEstimator q hq, totalProcessWork z.2 = 0 := by
    filter_upwards [hv] with z hz
    simp [totalProcessWork,ThresholdHC.workOf,processPrefix,hz]
  unfold criticalExpectedWork
  rw [lintegral_congr_ae hz]
  simp

theorem critical_budget_class_nonempty (ρ B : ℝ) :
    ∃ A : Tier6.AdaptiveEstimator Unit, CriticalUniformBudget A ρ B := by
  refine ⟨criticalZeroEstimator,?_⟩
  intro q hq _
  rw [criticalZeroEstimator_work]
  exact bot_le

theorem criticalZeroEstimator_risk (ρ : ℝ) :
    criticalMaximalRMSRisk criticalZeroEstimator ρ ≤ ENNReal.ofReal ρ := by
  apply iSup_le
  intro q
  apply iSup_le
  intro hq
  apply iSup_le
  intro hmass
  let a := ∫ d, (q d : ℝ) ∂criticalGapLaw
  have ha : 0 ≤ a := integral_nonneg (fun d => (q d).property.1)
  have heq : Tier6.squaredRisk (criticalExperimentLaw criticalZeroEstimator q hq)
      (fun z => criticalZeroEstimator.output (z.1.1,z.2)) a = ENNReal.ofReal (a^2) := by
    simp [Tier6.squaredRisk,criticalZeroEstimator]
  unfold Tier6.rootMeanRisk
  change Tier6.squaredRisk _ _ a ^ (1/2 : ℝ) ≤ _
  rw [heq,ENNReal.ofReal_pow ha]
  have hr : ((ENNReal.ofReal a)^2) ^ (1/2 : ℝ) = ENNReal.ofReal a := by
    simpa only [Nat.cast_ofNat,one_div] using
      ENNReal.pow_rpow_inv_natCast (n := 2) (by norm_num) (ENNReal.ofReal a)
  rw [hr]
  exact ENNReal.ofReal_le_ofReal hmass

/-- Nonvacuity: a zero-work estimator has risk at most the rarity. -/
theorem critical_minimax_le_rarity (ρ B : ℝ) :
    criticalMinimaxRisk ρ B ≤ ENNReal.ofReal ρ := by
  apply le_trans _ (criticalZeroEstimator_risk ρ)
  apply sInf_le
  refine ⟨Unit,inferInstance,criticalZeroEstimator,?_,rfl⟩
  intro q hq _
  rw [criticalZeroEstimator_work]
  exact bot_le

end ThresholdHC.CriticalEntropy
