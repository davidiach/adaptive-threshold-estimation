import ThresholdHC.ArbitraryLawAdaptation.ZeroSelection

/-! Monotonicity and homogeneity of the zero-atom functional's two costs. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThresholdHC.ArbitraryLawAdaptation
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTail

theorem canonicalGamma_smul (σ : Measure Gap) [IsFiniteMeasure σ] {c : ℝ} (hc : 0 ≤ c) :
    gamma (ENNReal.ofReal c • σ) = ENNReal.ofReal c*gamma σ := by
  have : IsFiniteMeasure (ENNReal.ofReal c • σ) := σ.smul_finite ENNReal.ofReal_ne_top
  rw [← countableEntropy_bandCosts_eq_gamma, ← countableEntropy_bandCosts_eq_gamma σ]
  have hb (j : ℕ) : bandCost (ENNReal.ofReal c • σ) j = ENNReal.ofReal c*bandCost σ j := by
    simp only [bandCost, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]
  simp_rw [countableEntropy, hb, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc]
  rw [ENNReal.mul_iSup]
  apply iSup_congr
  intro n
  rw [ThresholdHC.EntropyTailQuantile.costEntropy_smul,
    ENNReal.ofReal_mul hc]

theorem zeroGamma_mono {σ τ : Measure ℝ} [IsFiniteMeasure τ] (h : σ ≤ τ) :
    zeroGamma σ ≤ zeroGamma τ := by
  by_cases ht : τ {0} = 0
  · have hs : σ {0} = 0 := le_zero_iff.mp ((h {0}).trans_eq ht)
    have : IsFiniteMeasure (positivePart τ) := by unfold positivePart; infer_instance
    simp only [zeroGamma, hs, ht, ite_true]
    exact gamma_mono (comap_mono_embedding gapEmbedding h)
  · rw [zeroGamma_of_atom ht]
    exact le_top

theorem zeroGamma_smul (σ : Measure ℝ) [IsFiniteMeasure σ] {c : ℝ} (hc : 0 ≤ c) :
    zeroGamma (ENNReal.ofReal c • σ) = ENNReal.ofReal c*zeroGamma σ := by
  rcases hc.eq_or_lt with hc0 | hcpos
  · simp [← hc0, zeroGamma, positivePart, gamma_zero]
  have hcne : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.mpr hcpos).ne'
  by_cases hs : σ {0} = 0
  · have hsc : (ENNReal.ofReal c • σ) {0} = 0 := by simp [hs]
    have : IsFiniteMeasure (positivePart σ) := by unfold positivePart; infer_instance
    rw [zeroGamma, ite_eq_left hsc, zeroGamma, ite_eq_left hs]
    rw [positivePart, Measure.comap_smul, canonicalGamma_smul _ hcpos.le]
    rfl
  · have hsc : (ENNReal.ofReal c • σ) {0} ≠ 0 := by simpa using mul_ne_zero hcne hs
    rw [zeroGamma_of_atom hsc, zeroGamma_of_atom hs, ENNReal.mul_top hcne]

theorem zeroTailCost_mono {μ ν : Measure ℝ} (h : μ ≤ ν) (t : ℝ) :
    zeroTailCost μ t ≤ zeroTailCost ν t := lintegral_mono' h le_rfl

theorem zeroTailCost_add (μ ν : Measure ℝ) (t : ℝ) :
    zeroTailCost (μ+ν) t = zeroTailCost μ t+zeroTailCost ν t := lintegral_add_measure _ _ _

theorem zeroTailCost_smul (c : ℝ≥0∞) (μ : Measure ℝ) (t : ℝ) :
    zeroTailCost (c • μ) t = c*zeroTailCost μ t := lintegral_smul_measure _ _

theorem zeroTailCost_dirac_zero (t : ℝ) : zeroTailCost (Measure.dirac 0) t = 1 := by
  rw [zeroTailCost, lintegral_dirac]
  exact zeroTailWeight_zero t

end ThresholdHC.ArbitraryLawAdaptation
