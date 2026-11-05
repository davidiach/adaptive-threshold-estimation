import ThresholdHC.QuantileSharpLaw.RootDerivative

noncomputable section
open Real
namespace ThresholdHC.QuantileSharpLaw
open ThresholdHC.EntropyTailQuantile

theorem bumpedRoot_continuous {ι : Type*} [Fintype ι] (a : ℝ) (v : ι → ℝ) :
    Continuous (fun y : ℝ => sqrt (costEntropy (bumpedCost a v y))) := by
  apply continuous_sqrt.comp
  apply continuous_costEntropy.comp
  apply continuous_pi
  intro i
  cases i with
  | none => change Continuous (fun y : ℝ => a+y^2); fun_prop
  | some i => exact continuous_const

theorem bumpedRoot_increment {ι : Type*} [Fintype ι] {a x y : ℝ} {v : ι → ℝ}
    (ha : 0 ≤ a) (hv : ∀ i, 0 ≤ v i) (hx : 0 ≤ x) (hxy : x ≤ y) :
    sqrt (costEntropy (bumpedCost a v y))-sqrt (costEntropy (bumpedCost a v x)) ≤ y-x := by
  have hd : DifferentiableOn ℝ (fun z : ℝ => sqrt (costEntropy (bumpedCost a v z)))
      (interior (Set.Ici 0)) := by
    rw [interior_Ici]
    exact fun z hz => (bumpedRoot_hasDerivAt ha hv hz).differentiableAt.differentiableWithinAt
  have hb : ∀ z ∈ interior (Set.Ici (0 : ℝ)),
      deriv (fun w : ℝ => sqrt (costEntropy (bumpedCost a v w))) z ≤ 1 := by
    intro z hz
    rw [interior_Ici] at hz
    rw [(bumpedRoot_hasDerivAt ha hv hz).deriv]
    exact bumpedRoot_slope_le_one ha hv hz
  have h := (convex_Ici (0 : ℝ)).image_sub_le_mul_sub_of_deriv_le
    (bumpedRoot_continuous a v).continuousOn hd hb x hx y (hx.trans hxy) hxy
  simpa only [one_mul] using h

theorem bumpedRoot_monotoneOn {ι : Type*} [Fintype ι] {a : ℝ} {v : ι → ℝ}
    (ha : 0 ≤ a) (hv : ∀ i, 0 ≤ v i) :
    MonotoneOn (fun y : ℝ => sqrt (costEntropy (bumpedCost a v y))) (Set.Ici 0) := by
  intro x hx y hy hxy
  apply sqrt_le_sqrt
  apply costEntropy_mono (bumpedCost_nonneg ha hv x)
  intro i
  cases i with
  | none =>
    change a+x^2 ≤ a+y^2
    exact add_le_add le_rfl ((sq_le_sq₀ hx hy).mpr hxy)
  | some i => exact le_rfl

theorem bumpedRoot_abs_increment {ι : Type*} [Fintype ι] {a x y : ℝ} {v : ι → ℝ}
    (ha : 0 ≤ a) (hv : ∀ i, 0 ≤ v i) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |sqrt (costEntropy (bumpedCost a v y))-sqrt (costEntropy (bumpedCost a v x))| ≤ |y-x| := by
  rcases le_total x y with hxy | hyx
  · rw [abs_of_nonneg (sub_nonneg.mpr (bumpedRoot_monotoneOn ha hv hx hy hxy)),
      abs_of_nonneg (sub_nonneg.mpr hxy)]
    exact bumpedRoot_increment ha hv hx hxy
  · rw [abs_sub_comm (sqrt _),abs_sub_comm y]
    rw [abs_of_nonneg (sub_nonneg.mpr (bumpedRoot_monotoneOn ha hv hy hx hyx)),
      abs_of_nonneg (sub_nonneg.mpr hyx)]
    exact bumpedRoot_increment ha hv hy hyx

theorem skipped_tail_absorption {ι : Type*} [Fintype ι] {a e : ℝ} {v : ι → ℝ}
    (ha : 0 ≤ a) (hv : ∀ i, 0 ≤ v i) (he : 0 ≤ e) (he1 : e ≤ 1) :
    sqrt (costEntropy (bumpedCost a v 1)) ≤
      e+sqrt (costEntropy (bumpedCost a v (1-e))) := by
  have h := bumpedRoot_increment ha hv (x := 1-e) (y := 1) (by linarith) (by linarith)
  linarith only [h]

end ThresholdHC.QuantileSharpLaw
