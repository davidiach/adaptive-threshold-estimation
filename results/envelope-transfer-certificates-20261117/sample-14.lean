import ThresholdHC.EnvelopeTransferCertificates.Transfer
open MeasureTheory
open scoped ENNReal BigOperators
open ThresholdHC.Tier6 ThresholdHC.FiniteLawCertificates ThresholdHC.EnvelopeTransferCertificates
open ThresholdHC.DeterministicCertificates ThresholdHC.ArbitraryLawAdaptation
set_option maxRecDepth 8192
set_option maxHeartbeats 12000000
theorem certified_value :
    (0/1:ℚ) = max 0 ((0/1:ℚ)-(0/1:ℚ)) ∧
    (0/1:ℚ) = min (1/4:ℚ) ((1/1:ℚ)*(0/1:ℚ)+(0/1:ℚ)) ∧
    ∀ (μ μ₀ : Measure Gap) [IsProbabilityMeasure μ] [IsProbabilityMeasure μ₀]
      (T : Gap → Gap), Measurable T → tvDist μ μ₀/2 ≤ ((0/1:ℚ):ℝ) →
      (∀ d : Gap, (d:ℝ) ≤ (T d:ℝ) ∧ (T d:ℝ) ≤ ((1/1:ℚ):ℝ)*(d:ℝ)) →
      (∀ j, T ⁻¹' ThresholdHC.EntropyTail.band j = ThresholdHC.EntropyTail.band j) →
      Contains ⟨(0/1:ℚ), (0/1:ℚ)⟩ (ThresholdHC.EntropyTail.selection (μ₀.map T) ((1/4:ℚ):ℝ) ((256/1:ℚ):ℝ)).toReal →
      Contains ⟨(0/1:ℚ), (0/1:ℚ)⟩ (ThresholdHC.EntropyTail.selection μ ((1/4:ℚ):ℝ) ((256/1:ℚ):ℝ)).toReal := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro μ μ₀ _ _ T hm htv hd hb hi
  exact transfer_original μ μ₀ T hm (1/1:ℚ) (0/1:ℚ) (1/4:ℚ) (256/1:ℚ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) htv hd hb ⟨(0/1:ℚ), (0/1:ℚ)⟩ ⟨(0/1:ℚ), (0/1:ℚ)⟩ hi
    (by norm_num [transferCheck])
#print axioms certified_value
