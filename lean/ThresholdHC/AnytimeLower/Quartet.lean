import ThresholdHC.AnytimeLower.Embedding

noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal
namespace ThresholdHC.AnytimeLower
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.StoppingProgram
open ThresholdHC.ConfidenceTransfer ThresholdHC.ObservableSimulation ThresholdHC.Genie

/-- A central segment after absorbing the certificate's variance and work references. -/
def centralPrior (Q : FourPriors) (x : ℝ) (hx : 3/8 ≤ x ∧ x ≤ 5/8) : SignLaw :=
  mixPrior (absorbedLow Q) (absorbedHigh Q) x ⟨by linarith,by linarith⟩

theorem centralPrior_rare (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ : ℝ} (Q : FourPriors) (hQ : Admissible μ ρ Q)
    (x : ℝ) (hx : 3/8 ≤ x ∧ x ≤ 5/8) : RarePrior μ ρ (centralPrior Q x hx) := by
  have h := absorbedPriors_admissible μ Q hQ
  exact mixPrior_rare μ _ _ h.1 h.2.1 x _

theorem centralPrior_mean_difference (μ : Measure Gap) [IsProbabilityMeasure μ]
    (Q : FourPriors) (x y : ℝ) (hx : 3/8 ≤ x ∧ x ≤ 5/8) (hy : 3/8 ≤ y ∧ y ≤ 5/8) :
    signMean μ (centralPrior Q x hx).val-signMean μ (centralPrior Q y hy).val =
      (y-x)*(signMean μ Q.high.val-signMean μ Q.low.val)/3 := by
  have h := absorbedPriors_gap μ Q
  change signMean μ (absorbedHigh Q).val-signMean μ (absorbedLow Q).val =
    (1/3)*(signMean μ Q.high.val-signMean μ Q.low.val) at h
  dsimp only [centralPrior]
  rw [mixPrior_mean,mixPrior_mean]
  calc
    _ = (y-x)*(signMean μ (absorbedHigh Q).val-signMean μ (absorbedLow Q).val) := by ring
    _ = _ := by rw [h]; ring

/-- Every finite-information certificate supplies one common family whose
prefix KL bound holds for every physical budget and adaptive controller. -/
theorem quartet_prefix_kl {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    (Q : FourPriors) (J : ℝ) (hJ : 0 ≤ J)
    (hI : infiniteInformationRatio μ Q ≤ ENNReal.ofReal J)
    (x y : ℝ) (hx : 3/8 ≤ x ∧ x ≤ 5/8) (hy : 3/8 ≤ y ∧ y ≤ 5/8) (n : ℕ) :
    klDiv (observablePrefixLaw μ A (centralPrior Q x hx) n)
      (observablePrefixLaw μ A (centralPrior Q y hy) n) ≤
        ENNReal.ofReal ((64/3)*J*(x-y)^2*n) := by
  apply segment_prefix_kl μ A (absorbedLow Q) (absorbedHigh Q) J hJ _ x y hx hy n
  intro m
  exact (absorbedPriors_informationRatio_le μ m Q).trans
    (((informationRatio_mono μ Q (Nat.le_succ m)).trans
      (le_iSup (fun k => informationRatio μ (k+1) Q) m)).trans hI)

end ThresholdHC.AnytimeLower
