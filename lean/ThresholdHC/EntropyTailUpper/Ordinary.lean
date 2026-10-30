import ThresholdHC.BlindUpper.ClassifierProcedure
import ThresholdHC.ObservableSimulation.OriginalExperiment

/-! The paper's capped ordinary classifier, reusing the actual observable
procedure and its existing Hoeffding proofs. Both error and work constants
match the entropy-tail construction's single-coin certificates. -/

noncomputable section
open MeasureTheory Set Real

namespace ThresholdHC.EntropyTailUpper
open ThresholdHC.Tier6 ThresholdHC.Uniform713 ThresholdHC.BlindUpper
open ThresholdHC.ObservableSimulation

def ordinaryErrorKernel (M d : ℝ) : ℝ := min 1 ((M*d^2)⁻¹^2)

def ordinaryWorkKernel (M d : ℝ) : ℝ :=
  min M (17*d⁻¹^2*(1+max 0 (log (M*d^2))))

theorem ordinary_conditional_error (L : ℕ) (d : Gap) (s : Bool) :
    (ThresholdHC.Tier2.tapeMeasure (gapParameter s d)).real
      {ω | classifierValue L ω ≠ ThresholdHC.Tier2.bit s} ≤
        ordinaryErrorKernel (cap L) (d:ℝ) := by
  have ht := ThresholdHC.Tier2.tape_mean_tails (gapParameter s d)
  unfold ordinaryErrorKernel
  apply le_min measureReal_le_one
  have hb : (ThresholdHC.Tier2.tapeMeasure (gapParameter s d)).real
      {ω | classifierValue L ω ≠ ThresholdHC.Tier2.bit s} ≤
        ThresholdHC.Tier2.Model.errorPrefactor / (cap L * (d:ℝ)^2)^2 := by
    cases s with
    | false =>
      simp only [gapParameter, Bool.false_eq_true, ite_false, ← sub_eq_add_neg] at ht
      simpa only [classifierValue, ThresholdHC.Tier2.bit, gapParameter,
        Bool.false_eq_true, ite_false, ← sub_eq_add_neg] using
        ThresholdHC.Tier2.Model.error_negative_bound L d.property.1 ht
    | true =>
      simp only [gapParameter, ite_true] at ht
      simpa only [classifierValue, ThresholdHC.Tier2.bit, gapParameter, ite_true] using
        ThresholdHC.Tier2.Model.error_positive_bound L d.property.1 ht
  apply hb.trans
  have hp : ThresholdHC.Tier2.Model.errorPrefactor ≤ 1 := by
    linarith [ThresholdHC.Tier2.Model.errorPrefactor_le]
  simpa only [one_div, inv_pow] using div_le_div_of_nonneg_right hp
    (sq_nonneg (cap L * (d:ℝ)^2))

theorem ordinary_conditional_work (L : ℕ) (d : Gap) (s : Bool) :
    (∫ ω, (classifierStop L ω : ℝ) ∂ThresholdHC.Tier2.tapeMeasure (gapParameter s d)) ≤
      ordinaryWorkKernel (cap L) (d:ℝ) := by
  unfold ordinaryWorkKernel
  have ht := ThresholdHC.Tier2.tape_mean_tails (gapParameter s d)
  have he : (fun ω => (classifierStop L ω : ℝ)) =
      fun ω => ThresholdHC.Tier2.Model.work
        (fun k => dyadicMean ThresholdHC.Tier2.observations k ω) L := by
    funext ω
    simp only [classifierStop, ThresholdHC.Tier2.Model.work, cap, Nat.cast_pow, Nat.cast_ofNat]
  rw [he]
  have hb : (∫ ω, ThresholdHC.Tier2.Model.work
      (fun k => dyadicMean ThresholdHC.Tier2.observations k ω) L
        ∂ThresholdHC.Tier2.tapeMeasure (gapParameter s d)) ≤ 17*workEnvelope L (d:ℝ) := by
    cases s with
    | false =>
      simp only [gapParameter, Bool.false_eq_true, ite_false, ← sub_eq_add_neg] at ht
      exact ThresholdHC.Tier2.Model.expected_work_negative_bound L d.property.1 d.property.2 ht
    | true =>
      simp only [gapParameter, ite_true] at ht
      exact ThresholdHC.Tier2.Model.expected_work_positive_bound L d.property.1 d.property.2 ht
  apply le_min (ThresholdHC.Tier2.Model.expected_work_le_cap ht.measurable L)
  calc
    _ ≤ 17 * workEnvelope L (d:ℝ) := hb
    _ ≤ 17 * ((d:ℝ)⁻¹^2*(1+max 0 (log (cap L*(d:ℝ)^2)))) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)
    _ = _ := by ring

end ThresholdHC.EntropyTailUpper
