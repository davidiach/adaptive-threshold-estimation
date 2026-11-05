import ThresholdHC.RMSLocalization.PairRisk

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.RMSLocalization
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.CriticalEntropy
open ThresholdHC.ObservableSimulation ThresholdHC.ConfidenceTransfer ThresholdHC.ConfidenceLocalization

theorem rms_rate_of_common_pair {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    {ρ b J B : ℝ} (hb : 0 < b) (hJ : 0 < J) (hB : 0 < B)
    (cp : CommonPairBound μ ρ b J) (hw : RareBudget μ A ρ B) :
    ENNReal.ofReal (min b (Real.sqrt (J/B))/128) ≤ rareRisk μ A ρ := by
  have hp := AdditiveConfidence.component_pair_uniform μ hb hJ hB (by norm_num : (0 : ℝ) < 1) cp
  simp only [mul_one] at hp
  obtain ⟨q,r,hq,hr,hqh,hrh,hsep,hloc⟩ := hp
  have hinfo : 2*(42/(1024*B))*B ≤ (1/10 : ℝ) := by
    have he : 2*(42/(1024*B))*B = (21/256 : ℝ) := by
      field_simp [ne_of_gt hB]
      norm_num
    rw [he]
    norm_num
  have h := pair_rms_risk μ A q r (by positivity : 0 < min b (Real.sqrt (J/B))/32)
    hB.le (by positivity : 0 ≤ 42/(1024*B)) hq hr hqh hrh hloc hw hinfo hsep
  convert h using 1
  congr 1
  ring

theorem rms_rate_of_obstruction {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    {ρ b J B : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (hb : 0 < b) (hJ : 0 < J) (hB : 0 < B)
    (hobs : NullVarianceObstruction μ (gapParameter false) (gapParameter true) ρ b J)
    (hw : RareBudget μ A ρ B) :
    ENNReal.ofReal (min b (Real.sqrt (J/B))/128) ≤ rareRisk μ A ρ :=
  rms_rate_of_common_pair μ A hb hJ hB (common_pair_bound hρ hρ4 hJ hobs) hw

theorem minimax_rms_of_obstruction (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ b J B : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (hb : 0 < b) (hJ : 0 < J) (hB : 0 < B)
    (hobs : NullVarianceObstruction μ (gapParameter false) (gapParameter true) ρ b J) :
    ENNReal.ofReal (min b (Real.sqrt (J/B))/128) ≤ rareMinimaxRisk μ ρ B := by
  apply le_sInf
  rintro t ⟨R,mR,A,hw,rfl⟩
  exact rms_rate_of_obstruction μ A hρ hρ4 hb hJ hB hobs hw

end ThresholdHC.RMSLocalization
