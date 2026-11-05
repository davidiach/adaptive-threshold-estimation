import ThresholdHC.RMSLocalization.Additive

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace ThresholdHC.RMSLocalization
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.CriticalEntropy
open ThresholdHC.ObservableSimulation ThresholdHC.ConfidenceTransfer ThresholdHC.ConfidenceLocalization
open ThresholdHC.AdditiveConfidence

theorem rms_rate_of_obstructions {I R : Type} [Fintype I] [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (M : GapMixture I μ) (A : AdaptiveEstimator R)
    (ρ b J : I → ℝ) {ρtotal B : ℝ}
    (hρpos : ∀ i, 0 < ρ i) (hρquarter : ∀ i, ρ i ≤ 1/4)
    (hb : ∀ i, 0 < b i) (hJ : ∀ i, 0 < J i) (hB : 0 < B)
    (hρ : ∑ i, (M.weight i : ℝ)*ρ i ≤ ρtotal)
    (hobs : ∀ i, NullVarianceObstruction (M.law i)
      (gapParameter false) (gapParameter true) (ρ i) (b i) (J i))
    (hw : RareBudget μ A ρtotal B) :
    ENNReal.ofReal ((∑ i, (M.weight i : ℝ)*min (b i) (Real.sqrt (J i/B)))/128) ≤ rareRisk μ A ρtotal :=
  rms_rate_of_mixture μ M A ρ b J hb hJ hB hρ
    (fun i => common_pair_bound (hρpos i) (hρquarter i) (hJ i) (hobs i)) hw

theorem rms_rate_of_submeasures {I R : Type} [Fintype I] [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (σ : I → Measure Gap)
    (hs : (∑ i, σ i) ≤ μ) (hn : ∀ i, σ i Set.univ ≠ 0)
    (A : AdaptiveEstimator R) (ρ b J : I → ℝ) {ρtotal B : ℝ}
    (hρpos : ∀ i, 0 < ρ i) (hρquarter : ∀ i, ρ i ≤ 1/4)
    (hb : ∀ i, 0 < b i) (hJ : ∀ i, 0 < J i) (hB : 0 < B)
    (hρ : ∑ i, (σ i).real Set.univ*ρ i ≤ ρtotal)
    (hobs : ∀ i, NullVarianceObstruction (normalizedGapLaw (σ i))
      (gapParameter false) (gapParameter true) (ρ i) (b i) (J i))
    (hw : RareBudget μ A ρtotal B) :
    ENNReal.ofReal ((∑ i, (σ i).real Set.univ*min (b i) (Real.sqrt (J i/B)))/128) ≤ rareRisk μ A ρtotal :=
  rms_rate_of_obstructions μ (submeasureMixture μ σ hs hn) A ρ b J
    hρpos hρquarter hb hJ hB hρ hobs hw

theorem minimax_rms_of_submeasures {I : Type} [Fintype I]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (σ : I → Measure Gap)
    (hs : (∑ i, σ i) ≤ μ) (hn : ∀ i, σ i Set.univ ≠ 0)
    (ρ b J : I → ℝ) {ρtotal B : ℝ}
    (hρpos : ∀ i, 0 < ρ i) (hρquarter : ∀ i, ρ i ≤ 1/4)
    (hb : ∀ i, 0 < b i) (hJ : ∀ i, 0 < J i) (hB : 0 < B)
    (hρ : ∑ i, (σ i).real Set.univ*ρ i ≤ ρtotal)
    (hobs : ∀ i, NullVarianceObstruction (normalizedGapLaw (σ i))
      (gapParameter false) (gapParameter true) (ρ i) (b i) (J i)) :
    ENNReal.ofReal ((∑ i, (σ i).real Set.univ*min (b i) (Real.sqrt (J i/B)))/128) ≤ rareMinimaxRisk μ ρtotal B := by
  apply le_sInf
  rintro t ⟨R,mR,A,hw,rfl⟩
  exact rms_rate_of_submeasures μ σ hs hn A ρ b J hρpos hρquarter hb hJ hB hρ hobs hw

end ThresholdHC.RMSLocalization
