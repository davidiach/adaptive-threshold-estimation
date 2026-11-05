import ThresholdHC.Anytime.Spending
import ThresholdHC.ConfidenceProgram.Upper
import ThresholdHC.Confidence.Full

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.Anytime
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.HardBudget ThresholdHC.EntropyTail
open ThresholdHC.Confidence ThresholdHC.ConfidenceProgram ThresholdHC.ConfidenceTransfer ThresholdHC.StoppingProgram

/-- Strict slack above the proved infimum supplies an actual capped rule
at the stated radius, before the rare sign prior is given. -/
theorem known_rule (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ B δ : ℝ}
    (hr : 0 < ρ) (hu : ρ ≤ 1/4) (hB : 0 < B) (hd : 0 < δ) (hd' : δ ≤ 1/4) :
    ∃ (R : Type) (_ : MeasurableSpace R) (A : AdaptiveEstimator R), PathwiseCap A ⌊B⌋₊ ∧
    ∀ q : SignLaw, RarePrior μ ρ q →
      failureProbability μ A q (750001*(selection μ ρ (B/Real.log (1/δ))).toReal) ≤ ENNReal.ofReal δ := by
  let β := B/Real.log (1/δ)
  have hβ : 0 < β := div_pos hB (confidence_log_pos hd hd')
  have hfloor := bernoulli_label_minimax_floor μ ρ β hr hu hβ
  have hmin : 0 < min ρ (Real.sqrt (ρ/β)) := lt_min hr (Real.sqrt_pos.mpr (div_pos hr hβ))
  have hp : 0 < rareMinimaxRisk μ ρ β := (ENNReal.ofReal_pos.mpr (mul_pos (by norm_num) hmin)).trans_le hfloor
  have hk : selection μ ρ β ≠ 0 := by
    intro h
    have hupper := entropy_tail_upper_explicit μ hr hu hβ
    rw [h,mul_zero] at hupper
    exact hp.not_ge hupper
  have hk' := ENNReal.toReal_pos hk (finite_selection μ ρ β)
  have hstrict : hardConfidenceRadius μ ρ B δ < ENNReal.ofReal (750001*(selection μ ρ β).toReal) := by
    apply (general_hard_confidence_upper μ hr hu hB hd hd').trans_lt
    have he : (750000:ℝ≥0∞)*selection μ ρ β = ENNReal.ofReal (750000*(selection μ ρ β).toReal) := by
      rw [ENNReal.ofReal_mul (by norm_num : 0 ≤ (750000:ℝ)),ENNReal.ofReal_toReal (finite_selection μ ρ β)]
      norm_num
    rw [he]
    apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mpr
    linarith
  obtain ⟨t,⟨R,mR,A,r,hrr,hcap,hf,rfl⟩,ht⟩ := sInf_lt_iff.mp hstrict
  refine ⟨R,mR,A,hcap,?_⟩
  have hradius : r ≤ 750001*(selection μ ρ β).toReal := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hrr).mp ht |>.le
  exact fun q hq => (failureProbability_mono μ A q hradius).trans (hf q hq)

def radius (μ : Measure Gap) (ρ δ : ℝ) (j : ℕ) : ℝ :=
  750001*(selection μ ρ ((stageCap j:ℝ)/Real.log (1/stageFailure δ j))).toReal

theorem radius_nonneg (μ : Measure Gap) (ρ δ : ℝ) (j : ℕ) : 0 ≤ radius μ ρ δ j :=
  mul_nonneg (by norm_num) ENNReal.toReal_nonneg

theorem known_stages (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ δ : ℝ}
    (hr : 0 < ρ) (hu : ρ ≤ 1/4) (hd : 0 < δ) (hd' : δ ≤ 1/4) :
    ∃ (R : ℕ → Type) (_ : ∀ j, MeasurableSpace (R j)) (base : ∀ j, AdaptiveEstimator (R j)),
    ∀ j, PathwiseCap (base j) (stageCap j) ∧ ∀ q : SignLaw, RarePrior μ ρ q →
      failureProbability μ (base j) q (radius μ ρ δ j) ≤ ENNReal.ofReal (stageFailure δ j) := by
  have hstage (j : ℕ) := known_rule μ hr hu (by dsimp [stageCap,stageAllowance]; positivity : 0 < (stageCap j:ℝ))
    (stageFailure_pos hd j) ((stageFailure_le hd.le j).trans hd')
  choose R mR base hcap hfail using hstage
  let (j : ℕ) := mR j
  refine ⟨R,mR,base,fun j => ⟨?_,hfail j⟩⟩
  simpa only [Nat.floor_natCast] using hcap j

end ThresholdHC.Anytime
