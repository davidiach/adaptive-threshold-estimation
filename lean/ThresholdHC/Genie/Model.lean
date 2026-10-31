import ThresholdHC.StoppingProgram.Model

/-! Infinite-cap values and the latent reveal at a finite cap. Definitions
alone do not assert duality, convergence, or a statistical lower bound. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.Genie
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.StoppingProgram

def infiniteProgramValue (μ : Measure Gap) (ρ B : ℝ) : ℝ≥0∞ :=
  ⨅ N : ℕ, programValue μ ρ B (N+1)

def infiniteInformationRatio (μ : Measure Gap) (Q : FourPriors) : ℝ≥0∞ :=
  ⨆ N : ℕ, informationRatio μ (N+1) Q

def infiniteDualRatio (μ : Measure Gap) (B : ℝ) (Q : FourPriors) : ℝ≥0∞ :=
  (ENNReal.ofReal (signMean μ Q.high.val-signMean μ Q.low.val))^2/
    (4+ENNReal.ofReal B*infiniteInformationRatio μ Q)

def revealReward (μ : Measure Gap) (Q : FourPriors) (n k : ℕ) : ℝ≥0∞ :=
  ∫⁻ d : Gap,
    ENNReal.ofReal (prefixLikelihood true n k d)*perspective (Q.high.val d-Q.low.val d) (Q.variance.val d)+
    ENNReal.ofReal (prefixLikelihood false n k d)*perspective (Q.high.val d-Q.low.val d) (1-Q.variance.val d) ∂μ

def latentDivergence (μ : Measure Gap) (Q : FourPriors) : ℝ≥0∞ :=
  ∫⁻ d : Gap, perspective (Q.high.val d-Q.low.val d) (Q.variance.val d)+
    perspective (Q.high.val d-Q.low.val d) (1-Q.variance.val d) ∂μ

end ThresholdHC.Genie
