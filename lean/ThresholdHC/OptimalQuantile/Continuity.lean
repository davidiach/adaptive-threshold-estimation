import ThresholdHC.OptimalQuantile.Monotonic
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Topology.Order.Compact

noncomputable section
open Real
open scoped BigOperators
namespace ThresholdHC.OptimalQuantile

def scalarDomain : Set (ℝ × ℝ) := Set.Ici (sqrt 2) ×ˢ Set.Ici 1

theorem dualPrice_continuousOn :
    ContinuousOn (fun z : ℝ × ℝ => dualPrice z.1 z.2) scalarDomain := by
  have hn : ∀ z ∈ scalarDomain, z.2 ≠ 0 := by
    intro z hz
    have h : 1 ≤ z.2 := hz.2
    linarith
  unfold dualPrice
  exact ((continuousOn_const.mul (continuous_fst.continuousOn.pow 2)).mul
    (continuous_snd.continuousOn.add (continuousOn_const.div continuous_snd.continuousOn hn))).sub
    (continuousOn_const.mul continuous_fst.continuousOn)

theorem partitionSeries_continuousOn :
    ContinuousOn (fun z : ℝ × ℝ => partitionSeries z.1 z.2) scalarDomain := by
  have hn : ∀ z ∈ scalarDomain, 2*z.2 ≠ 0 := by
    intro z hz
    have h : 1 ≤ z.2 := hz.2
    nlinarith
  have hfirst : ContinuousOn (fun z : ℝ × ℝ => exp (1-dualPrice z.1 z.2/(2*z.2)))
      scalarDomain :=
    continuous_exp.comp_continuousOn (continuousOn_const.sub
      (dualPrice_continuousOn.div (continuousOn_const.mul continuous_snd.continuousOn) hn))
  have htail : ContinuousOn (fun z : ℝ × ℝ =>
      ∑' j : ℕ, exp (1-dualPrice z.1 z.2*(2 : ℝ)^j)) scalarDomain := by
    apply continuousOn_tsum (u := fun j : ℕ => exp (1-2*(2 : ℝ)^j))
    · intro j
      exact continuous_exp.comp_continuousOn
        (continuousOn_const.sub (dualPrice_continuousOn.mul continuousOn_const))
    · exact exponentialTail_summable (by norm_num)
    · intro j z hz
      rw [Real.norm_eq_abs,abs_of_pos (exp_pos _)]
      apply exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_right (dualPrice_ge_two hz.1 hz.2)
        (show 0 ≤ (2 : ℝ)^j by positivity)
      linarith
  exact hfirst.add htail

theorem partitionSeries_continuousOn_tangent {k : ℝ} (hk : sqrt 2 ≤ k) :
    ContinuousOn (partitionSeries k) (Set.Ici 1) := by
  have hc : ContinuousOn (fun u : ℝ => (k,u)) (Set.Ici 1) :=
    (continuous_const.prodMk continuous_id).continuousOn
  have hm : Set.MapsTo (fun u : ℝ => (k,u)) (Set.Ici 1) scalarDomain :=
    fun u hu => ⟨hk,hu⟩
  simpa only [Function.comp_def] using
    (partitionSeries_continuousOn.comp hc hm)

end ThresholdHC.OptimalQuantile
