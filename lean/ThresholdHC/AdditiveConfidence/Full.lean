import ThresholdHC.AdditiveConfidence.ConfidenceRate

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace ThresholdHC.AdditiveConfidence
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.CriticalEntropy
open ThresholdHC.ObservableSimulation ThresholdHC.ConfidenceLocalization ThresholdHC.ConfidenceTransfer

theorem confidence_rate_of_obstructions {I R : Type} [Fintype I] [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (M : GapMixture I μ) (A : AdaptiveEstimator R)
    (ρ b J : I → ℝ) {ρtotal B ε δ : ℝ}
    (hρpos : ∀ i, 0 < ρ i) (hρquarter : ∀ i, ρ i ≤ 1/4)
    (hb : ∀ i, 0 < b i) (hJ : ∀ i, 0 < J i) (hB : 0 < B)
    (hδ : 0 < δ) (hδ' : δ ≤ 1/4)
    (hρ : ∑ i, (M.weight i : ℝ)*ρ i ≤ ρtotal)
    (hobs : ∀ i, NullVarianceObstruction (M.law i)
      (gapParameter false) (gapParameter true) (ρ i) (b i) (J i))
    (hw : RareBudget μ A ρtotal B)
    (hconf : ∀ u : SignLaw, RarePrior μ ρtotal u →
      ThresholdHC.Confidence.failureProbability μ A u ε ≤ ENNReal.ofReal δ) :
    (∑ i, (M.weight i : ℝ)*min (b i) (Real.sqrt (J i*Real.log (1/δ)/B)))/128 ≤ ε :=
  confidence_rate_of_mixture μ M A ρ b J hb hJ hB hδ hδ' hρ
    (fun i => common_pair_bound (hρpos i) (hρquarter i) (hJ i) (hobs i)) hw hconf

/-- Fractional submeasures may overlap. The exact normalized component laws
supply the variance/null-work premises. -/
theorem confidence_rate_of_submeasures {I R : Type} [Fintype I] [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (σ : I → Measure Gap)
    (hs : (∑ i, σ i) ≤ μ) (hn : ∀ i, σ i Set.univ ≠ 0)
    (A : AdaptiveEstimator R) (ρ b J : I → ℝ) {ρtotal B ε δ : ℝ}
    (hρpos : ∀ i, 0 < ρ i) (hρquarter : ∀ i, ρ i ≤ 1/4)
    (hb : ∀ i, 0 < b i) (hJ : ∀ i, 0 < J i) (hB : 0 < B)
    (hδ : 0 < δ) (hδ' : δ ≤ 1/4)
    (hρ : ∑ i, (σ i).real Set.univ*ρ i ≤ ρtotal)
    (hobs : ∀ i, NullVarianceObstruction (normalizedGapLaw (σ i))
      (gapParameter false) (gapParameter true) (ρ i) (b i) (J i))
    (hw : RareBudget μ A ρtotal B)
    (hconf : ∀ u : SignLaw, RarePrior μ ρtotal u →
      ThresholdHC.Confidence.failureProbability μ A u ε ≤ ENNReal.ofReal δ) :
    (∑ i, (σ i).real Set.univ*min (b i) (Real.sqrt (J i*Real.log (1/δ)/B)))/128 ≤ ε :=
  confidence_rate_of_obstructions μ (submeasureMixture μ σ hs hn) A ρ b J
    hρpos hρquarter hb hJ hB hδ hδ' hρ hobs hw hconf

theorem minimax_confidence_of_submeasures {I : Type} [Fintype I]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (σ : I → Measure Gap)
    (hs : (∑ i, σ i) ≤ μ) (hn : ∀ i, σ i Set.univ ≠ 0)
    (ρ b J : I → ℝ) {ρtotal B δ : ℝ}
    (hρpos : ∀ i, 0 < ρ i) (hρquarter : ∀ i, ρ i ≤ 1/4)
    (hb : ∀ i, 0 < b i) (hJ : ∀ i, 0 < J i) (hB : 0 < B)
    (hδ : 0 < δ) (hδ' : δ ≤ 1/4)
    (hρ : ∑ i, (σ i).real Set.univ*ρ i ≤ ρtotal)
    (hobs : ∀ i, NullVarianceObstruction (normalizedGapLaw (σ i))
      (gapParameter false) (gapParameter true) (ρ i) (b i) (J i)) :
    ENNReal.ofReal ((∑ i, (σ i).real Set.univ*min (b i)
      (Real.sqrt (J i*Real.log (1/δ)/B)))/128) ≤ rareConfidenceRadius μ ρtotal B δ := by
  apply le_sInf
  rintro t ⟨R,mR,A,ε,hε,hw,hconf,rfl⟩
  exact ENNReal.ofReal_le_ofReal (confidence_rate_of_submeasures μ σ hs hn A ρ b J
    hρpos hρquarter hb hJ hB hδ hδ' hρ hobs hw hconf)

end ThresholdHC.AdditiveConfidence
