import ThresholdHC.QuantileSharpLaw.Coarsening
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section
open Real
open scoped BigOperators
namespace ThresholdHC.QuantileSharpLaw
open ThresholdHC.EntropyTailQuantile

def costInteraction (A B : ℝ) : ℝ := negMulLog A+negMulLog B-negMulLog (A+B)

theorem costInteraction_nonneg {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ costInteraction A B := sub_nonneg.mpr (negMulLog_add_le hA hB)

theorem costInteraction_symm (A B : ℝ) : costInteraction A B=costInteraction B A := by
  unfold costInteraction
  ring

theorem costInteraction_continuous (A : ℝ) : Continuous (costInteraction A) := by
  unfold costInteraction
  fun_prop

theorem costInteraction_hasDerivAt {A x : ℝ} (hA : 0 ≤ A) (hx : 0 < x) :
    HasDerivAt (costInteraction A) (log ((A+x)/x)) x := by
  have hAx : 0 < A+x := add_pos_of_nonneg_of_pos hA hx
  have h := ((hasDerivAt_negMulLog hx.ne').const_add (negMulLog A)).sub
    ((hasDerivAt_negMulLog hAx.ne').comp x ((hasDerivAt_id x).const_add A))
  rw [log_div hAx.ne' hx.ne']
  convert h using 1
  · funext z
    rfl
  · ring

theorem costInteraction_monotoneOn {A : ℝ} (hA : 0 ≤ A) :
    MonotoneOn (costInteraction A) (Set.Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici _)
  · exact (costInteraction_continuous A).continuousOn
  · rw [interior_Ici]
    exact fun x hx => (costInteraction_hasDerivAt hA hx).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    rw [(costInteraction_hasDerivAt hA hx).deriv]
    apply log_nonneg
    exact (le_div_iff₀ hx).mpr (by linarith)

theorem costInteraction_mono_left {A B C : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B) (hC : 0 ≤ C) :
    costInteraction A C ≤ costInteraction B C := by
  rw [costInteraction_symm A C,costInteraction_symm B C]
  exact costInteraction_monotoneOn hC hA (hA.trans hAB) hAB

theorem costEntropy_add_interaction {ι : Type*} [Fintype ι] {v b : ι → ℝ}
    (hv : ∀ i, 0 ≤ v i) (hb : ∀ i, 0 ≤ b i) :
    costEntropy (fun i => v i+b i) ≤
      costEntropy v+costEntropy b+costInteraction (costTotal v) (costTotal b) := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => negMulLog_add_le (hv i) (hb i))
  rw [Finset.sum_add_distrib] at h
  unfold costEntropy costInteraction
  rw [costTotal_add]
  linarith only [h]

end ThresholdHC.QuantileSharpLaw
