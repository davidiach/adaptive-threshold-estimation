import ThresholdHC.ConfidenceTransfer.CriticalRate
noncomputable section
open MeasureTheory ThresholdHC.ConfidenceTransfer ThresholdHC.CriticalEntropy
open ThresholdHC.Tier6
open scoped ENNReal
example : criticalPositiveLaw.map (Subtype.val : Gap → ℝ) =
    (volume.restrict (Set.Ioc (0 : ℝ) (1/4))).withDensity (fun d => ENNReal.ofReal (32*d)) :=
  criticalPositiveLaw_map
example : ∃ a : ℝ, 0 < a ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1/4 →
    CommonPairBound criticalPositiveLaw ρ (ρ/32) (a*(ρ*criticalLogFactor ρ)) :=
  critical_common_pair_bound
example : ∃ c : ℝ, 0 < c ∧ ∀ ρ B δ : ℝ, 0 < ρ → ρ ≤ 1/4 → 0 < B → 0 < δ → δ ≤ 1/4 →
    ENNReal.ofReal (c * min ρ (Real.sqrt
      (ρ*((1+Real.log (1/ρ))*(1+Real.log (1+Real.log (1/ρ))))*Real.log (1/δ)/B))) ≤
      rareConfidenceRadius criticalPositiveLaw ρ B δ := critical_confidence_lower
#print axioms ThresholdHC.ConfidenceTransfer.CriticalConfidenceLowerStatement
#print axioms ThresholdHC.ConfidenceTransfer.criticalPositiveLaw
#print axioms ThresholdHC.ConfidenceTransfer.criticalPositiveLaw_map
#print axioms ThresholdHC.ConfidenceTransfer.criticalPositiveLaw_probability
#print axioms ThresholdHC.ConfidenceTransfer.criticalSign
#print axioms ThresholdHC.ConfidenceTransfer.critical_common_pair_bound
#print axioms ThresholdHC.ConfidenceTransfer.critical_confidence_lower
#print axioms ThresholdHC.ConfidenceTransfer.critical_local_transfer
#print axioms ThresholdHC.ConfidenceTransfer.critical_parameter_law
#print axioms ThresholdHC.ConfidenceTransfer.critical_sign_mean
#print axioms ThresholdHC.ConfidenceTransfer.minimax_confidence_rate_of_common_pair
#print axioms ThresholdHC.CriticalEntropy.critical_common_capped_pair
