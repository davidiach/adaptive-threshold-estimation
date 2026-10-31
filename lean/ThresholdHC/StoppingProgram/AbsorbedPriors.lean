import ThresholdHC.StoppingProgram.PriorMixtures
import ThresholdHC.StoppingProgram.PerspectiveMonotonic

/-! Absorbing both reference priors into the endpoints preserves global rarity
and loses exactly a factor three in the target gap. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 (Gap SignLaw signMean)
open ThresholdHC.RareAboveTwo

def midpointFourPriors (q r : SignLaw) : FourPriors :=
  ⟨q,r,midpointPrior q r,midpointPrior q r⟩

def absorbedLow (Q : FourPriors) : SignLaw :=
  mixPrior Q.low (midpointPrior Q.variance Q.work) (1/3) (by norm_num)

def absorbedHigh (Q : FourPriors) : SignLaw :=
  mixPrior Q.high (midpointPrior Q.variance Q.work) (1/3) (by norm_num)

def absorbedPriors (Q : FourPriors) : FourPriors :=
  midpointFourPriors (absorbedLow Q) (absorbedHigh Q)

theorem midpointFourPriors_admissible (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ : ℝ} (q r : SignLaw) (hq : RarePrior μ ρ q) (hr : RarePrior μ ρ r) :
    Admissible μ ρ (midpointFourPriors q r) :=
  ⟨hq,hr,mixPrior_rare μ q r hq hr (1/2) (by norm_num),
    mixPrior_rare μ q r hq hr (1/2) (by norm_num)⟩

theorem absorbedPriors_admissible (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ : ℝ} (Q : FourPriors) (hQ : Admissible μ ρ Q) : Admissible μ ρ (absorbedPriors Q) := by
  have hm := mixPrior_rare μ Q.variance Q.work hQ.2.2.1 hQ.2.2.2 (1/2) (by norm_num)
  exact midpointFourPriors_admissible μ _ _
    (mixPrior_rare μ _ _ hQ.1 hm (1/3) (by norm_num))
    (mixPrior_rare μ _ _ hQ.2.1 hm (1/3) (by norm_num))

theorem absorbedPriors_gap (μ : Measure Gap) [IsProbabilityMeasure μ] (Q : FourPriors) :
    signMean μ (absorbedPriors Q).high.val-signMean μ (absorbedPriors Q).low.val =
      (1/3)*(signMean μ Q.high.val-signMean μ Q.low.val) := by
  simp only [absorbedPriors,midpointFourPriors,absorbedLow,absorbedHigh,mixPrior_mean]
  ring

theorem absorbedPriors_contrast {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (Q : FourPriors) (s : CountState N) :
    countCoefficient μ (absorbedPriors Q).high s-countCoefficient μ (absorbedPriors Q).low s =
      (1/3)*(countCoefficient μ Q.high s-countCoefficient μ Q.low s) := by
  simp only [absorbedPriors,midpointFourPriors,absorbedLow,absorbedHigh,mixPrior_countCoefficient]
  ring

theorem absorbedPriors_reference {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (Q : FourPriors) (s : CountState N) :
    countCoefficient μ (absorbedPriors Q).variance s =
      (countCoefficient μ Q.low s+countCoefficient μ Q.high s)/6+
        (countCoefficient μ Q.variance s+countCoefficient μ Q.work s)/3 := by
  simp only [absorbedPriors,midpointFourPriors,absorbedLow,absorbedHigh,
    midpointPrior_countCoefficient,mixPrior_countCoefficient]
  ring

theorem absorbedPriors_variance_ge {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (Q : FourPriors) (s : CountState N) :
    (1/3)*countCoefficient μ Q.variance s ≤ countCoefficient μ (absorbedPriors Q).variance s := by
  rw [absorbedPriors_reference]
  linarith [countCoefficient_nonneg μ Q.low s,countCoefficient_nonneg μ Q.high s,
    countCoefficient_nonneg μ Q.work s]

theorem absorbedPriors_work_ge {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (Q : FourPriors) (s : CountState N) :
    (1/3)*countCoefficient μ Q.work s ≤ countCoefficient μ (absorbedPriors Q).work s := by
  change (1/3)*countCoefficient μ Q.work s ≤ countCoefficient μ (absorbedPriors Q).variance s
  rw [absorbedPriors_reference]
  linarith [countCoefficient_nonneg μ Q.low s,countCoefficient_nonneg μ Q.high s,
    countCoefficient_nonneg μ Q.variance s]

theorem absorbedPriors_perspective_le {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (Q : FourPriors) (s : CountState N) :
    perspective (countCoefficient μ (absorbedPriors Q).high s-countCoefficient μ (absorbedPriors Q).low s)
      (countCoefficient μ (absorbedPriors Q).variance s) ≤
      ENNReal.ofReal (1/3)*perspective (countCoefficient μ Q.high s-countCoefficient μ Q.low s)
        (countCoefficient μ Q.variance s) := by
  rw [absorbedPriors_contrast,← perspective_scale _ _ (show (0:ℝ) ≤ 1/3 by norm_num)]
  exact perspective_antitone_reference _ (mul_nonneg (by norm_num) (countCoefficient_nonneg μ _ _))
    (absorbedPriors_variance_ge μ Q s)

end ThresholdHC.StoppingProgram
