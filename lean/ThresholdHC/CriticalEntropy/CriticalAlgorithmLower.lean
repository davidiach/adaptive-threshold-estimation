import ThresholdHC.CriticalEntropy.CriticalRareModel
import ThresholdHC.CriticalEntropy.AffinityTesting

noncomputable section

namespace ThresholdHC.CriticalEntropy
open MeasureTheory Set ThresholdHC.Tier3
open scoped ENNReal
set_option maxHeartbeats 2000000

theorem critical_rms_pair_lower {Ω : Type} [MeasurableSpace Ω]
    (P Q : Measure Ω) (f : Ω → ℝ) (a b δ : ℝ) (hδ : 0 ≤ δ) (hsep : δ ≤ b-a)
    (hsq : ENNReal.ofReal ((b-a)^2/64) ≤
      max (Tier6.squaredRisk P f a) (Tier6.squaredRisk Q f b)) :
    ENNReal.ofReal (δ/8) ≤ max (Tier6.rootMeanRisk P f a) (Tier6.rootMeanRisk Q f b) := by
  have hsqδ : ENNReal.ofReal ((δ/8)^2) ≤
      max (Tier6.squaredRisk P f a) (Tier6.squaredRisk Q f b) := by
    apply le_trans _ hsq
    apply ENNReal.ofReal_le_ofReal
    have := (sq_le_sq₀ hδ (hδ.trans hsep)).2 hsep
    nlinarith
  have hh := ENNReal.rpow_le_rpow hsqδ (by norm_num : (0 : ℝ) ≤ 1/2)
  rw [ENNReal.max_rpow (by norm_num : (0 : ℝ) ≤ 1/2),
    ENNReal.ofReal_pow (by positivity : 0 ≤ δ/8)] at hh
  have heq : ((ENNReal.ofReal (δ/8))^2) ^ (1/2 : ℝ) = ENNReal.ofReal (δ/8) := by
    simpa only [Nat.cast_ofNat,one_div] using
      ENNReal.pow_rpow_inv_natCast (n := 2) (by norm_num) (ENNReal.ofReal (δ/8))
  rw [heq] at hh
  exact hh

/-- Actual algorithm-level error lower bound at every separation whose
information budget is small. The supremum is over the full rare class. -/
theorem critical_algorithm_lower_at_separation : ∃ C : ℝ, 0 < C ∧
    ∀ (ρ : unitInterval), 0 < (ρ : ℝ) → (ρ : ℝ) ≤ 1/4 →
    ∀ (δ B : ℝ), 0 < δ → δ ≤ (ρ : ℝ)/96 → 0 ≤ B →
    C*δ^2*B ≤ (ρ : ℝ)*criticalLogFactor (ρ : ℝ)/4 →
    ∀ (R : Type) [MeasurableSpace R] (A : Tier6.AdaptiveEstimator R),
      CriticalUniformBudget A (ρ : ℝ) B →
      ENNReal.ofReal (δ/8) ≤ criticalMaximalRMSRisk A (ρ : ℝ) := by
  obtain ⟨C,hC,hcommon⟩ := critical_common_terminal_pair
  refine ⟨C,hC,?_⟩
  intro ρ hρ hρ' δ B hδ hδρ hB hinfo R _ A hbudget
  obtain ⟨q,r,hq,hr,hsep,hpair⟩ := hcommon ρ hρ hρ' δ hδ.le hδρ
  let a := ∫ d, (q d : ℝ) ∂criticalGapLaw
  let b := ∫ d, (r d : ℝ) ∂criticalGapLaw
  let f : ((R × (ℕ → ℝ)) × ProcessTape) → ℝ := fun z => A.output (z.1.1,z.2)
  have hf : Measurable f :=
    A.output_measurable.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  let d := thresholdDecision A.output ((a+b)/2)
  have hd : Measurable d := measurable_thresholdDecision A.output A.output_measurable _
  have hi := (hpair R Bool A B hB hbudget d hd).trans hinfo
  have hk : 0 < (ρ : ℝ)*criticalLogFactor (ρ : ℝ) :=
    mul_pos hρ (criticalLogFactor_pos (ρ : ℝ) hρ ρ.property.2)
  have haff : (3/4 : ℝ) ≤ (hellingerAffinity (criticalObservationLaw A q hq.1 d)
      (criticalObservationLaw A r hr.1 d)).toReal := by nlinarith
  have hsq := two_point_risk_lower_of_decision_affinity
    (criticalExperimentLaw A q hq.1) (criticalExperimentLaw A r hr.1) f a b hf
    (by change a < b; change δ ≤ b-a at hsep; linarith) haff
  have hrms := critical_rms_pair_lower
    (criticalExperimentLaw A q hq.1) (criticalExperimentLaw A r hr.1) f a b δ hδ.le hsep hsq
  apply hrms.trans
  apply max_le
  · exact le_iSup_of_le q (le_iSup_of_le hq.1 (le_iSup_of_le hq.2.2 le_rfl))
  · exact le_iSup_of_le r (le_iSup_of_le hr.1 (le_iSup_of_le hr.2.2 le_rfl))

end ThresholdHC.CriticalEntropy
