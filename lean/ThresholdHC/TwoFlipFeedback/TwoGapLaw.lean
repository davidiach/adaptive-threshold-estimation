import ThresholdHC.TwoFlipFeedback.Specification
import ThresholdHC.TwoFlipFeedback.TwoStep

/-! Integrals against `μ = (δ_{1/4} + δ_{1/8})/2`. With `q₁ = q(1/4)`,
`q₂ = q(1/8)` and `A = q₁/8 + q₂/16`, one fresh coin shows a head with
probability `5/16 + 2A`, and two flips of one coin give the words
`TT, TH, HT, HH` with probabilities `61/128 - 2A, 27/128, 27/128, 13/128 + 2A`
(`full_class-body.tex`, proof of Theorem `feedback:full-class`). -/

noncomputable section
namespace ThresholdHC.TwoFlipFeedback
open MeasureTheory
open scoped ENNReal
open ThresholdHC.Proofs ThresholdHC.Tier6

theorem integral_twoGapLaw (f : Gap → ℝ) :
    ∫ x, f x ∂twoGapLaw = (f quarterGap + f eighthGap)/2 := by
  have h1 : Integrable f ((2⁻¹ : ℝ≥0∞) • Measure.dirac quarterGap) :=
    (integrable_dirac (by simp)).smul_measure (by simp)
  have h2 : Integrable f ((2⁻¹ : ℝ≥0∞) • Measure.dirac eighthGap) :=
    (integrable_dirac (by simp)).smul_measure (by simp)
  rw [twoGapLaw, integral_add_measure h1 h2, integral_smul_measure, integral_smul_measure,
    integral_dirac, integral_dirac]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat, smul_eq_mul]
  ring

/-- Twice the mean `∫ d q(d) dμ(d)`, the drift of the head probability. -/
def drift (q : Gap → ℝ) : ℝ := q quarterGap/4 + q eighthGap/8

theorem signMean_twoGapLaw (q : Gap → ℝ) :
    signMean twoGapLaw q = (q quarterGap + q eighthGap)/2 := by
  rw [signMean, integral_twoGapLaw]

abbrev gapValue : Gap → ℝ := fun d => (d : ℝ)

theorem oneBit_true (q : Gap → ℝ) : oneBit twoGapLaw gapValue q true = 5/16 + drift q := by
  rw [oneBit, integral_twoGapLaw]
  simp only [obsProb, quarterGap, eighthGap, drift]
  ring

theorem oneBit_false (q : Gap → ℝ) : oneBit twoGapLaw gapValue q false = 11/16 - drift q := by
  rw [oneBit, integral_twoGapLaw]
  simp only [obsProb, quarterGap, eighthGap, drift]
  ring

theorem twoBit_ff (q : Gap → ℝ) : twoBit twoGapLaw gapValue q false false = 61/128 - drift q := by
  rw [twoBit, integral_twoGapLaw]
  simp only [obsProb, quarterGap, eighthGap, drift]
  ring

theorem twoBit_ft (q : Gap → ℝ) : twoBit twoGapLaw gapValue q false true = 27/128 := by
  rw [twoBit, integral_twoGapLaw]
  simp only [obsProb, quarterGap, eighthGap]
  ring

theorem twoBit_tf (q : Gap → ℝ) : twoBit twoGapLaw gapValue q true false = 27/128 := by
  rw [twoBit, integral_twoGapLaw]
  simp only [obsProb, quarterGap, eighthGap]
  ring

theorem twoBit_tt (q : Gap → ℝ) : twoBit twoGapLaw gapValue q true true = 13/128 + drift q := by
  rw [twoBit, integral_twoGapLaw]
  simp only [obsProb, quarterGap, eighthGap, drift]
  ring

/-- The null sign law `q ≡ 0`. -/
def nullLaw : SignLaw := ⟨fun _ => 0, measurable_const, fun _ => ⟨le_rfl, zero_le_one⟩⟩

/-- The hard alternative `(q(1/4), q(1/8)) = (0, 1/2)`. -/
def hardLaw : SignLaw :=
  ⟨fun d => max 0 (1 - 4 * (d : ℝ)),
    measurable_const.max (measurable_const.sub (measurable_const.mul measurable_subtype_coe)),
    fun d => ⟨le_max_left _ _, max_le zero_le_one (by linarith [d.property.1])⟩⟩

theorem hardLaw_quarter : hardLaw.val quarterGap = 0 := by
  simp [hardLaw, quarterGap]

theorem hardLaw_eighth : hardLaw.val eighthGap = 1/2 := by
  simp [hardLaw, eighthGap]
  norm_num

theorem nullLaw_rare : ThresholdHC.RareAboveTwo.RarePrior twoGapLaw (1/4) nullLaw := by
  simp [ThresholdHC.RareAboveTwo.RarePrior, signMean_twoGapLaw, nullLaw]

theorem hardLaw_rare : ThresholdHC.RareAboveTwo.RarePrior twoGapLaw (1/4) hardLaw := by
  rw [ThresholdHC.RareAboveTwo.RarePrior, signMean_twoGapLaw, hardLaw_quarter, hardLaw_eighth]
  norm_num

theorem nullLaw_mean : signMean twoGapLaw nullLaw.val = 0 := by
  simp [signMean_twoGapLaw, nullLaw]

theorem hardLaw_mean : signMean twoGapLaw hardLaw.val = 1/4 := by
  rw [signMean_twoGapLaw, hardLaw_quarter, hardLaw_eighth]
  norm_num

theorem nullLaw_drift : drift nullLaw.val = 0 := by
  simp [drift, nullLaw]

theorem hardLaw_drift : drift hardLaw.val = 1/16 := by
  rw [drift, hardLaw_quarter, hardLaw_eighth]
  norm_num

end ThresholdHC.TwoFlipFeedback
