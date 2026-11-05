import ThresholdHC.QuantileSharpLaw.Coarsening
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section
open Real
open scoped BigOperators
namespace ThresholdHC.QuantileSharpLaw
open ThresholdHC.EntropyTailQuantile

theorem bumpedCost_positive {ι : Type*} [Fintype ι] {a y : ℝ} {v : ι → ℝ}
    (ha : 0 ≤ a) (hv : ∀ i, 0 ≤ v i) (hy : 0 < y) :
    0 < costEntropy (bumpedCost a v y) := by
  have h := costTotal_le_costEntropy (bumpedCost_nonneg ha hv y)
  rw [bumpedCost_total] at h
  have hV := costTotal_nonneg hv
  nlinarith only [h,ha,hV,hy]

theorem bumpedCost_hasDerivAt {ι : Type*} [Fintype ι] {a y : ℝ} {v : ι → ℝ}
    (ha : 0 ≤ a) (hv : ∀ i, 0 ≤ v i) (hy : 0 < y) :
    HasDerivAt (fun z : ℝ => costEntropy (bumpedCost a v z))
      (2*y*(1-log ((a+y^2)/(a+y^2+costTotal v)))) y := by
  have hq : 0 < a+y^2 := by nlinarith only [ha,hy]
  have hM : 0 < a+y^2+costTotal v := add_pos_of_pos_of_nonneg hq (costTotal_nonneg hv)
  have hdq : HasDerivAt (fun z : ℝ => a+z^2) (2*y) y := by
    simpa using (hasDerivAt_pow 2 y).const_add a
  have hdM := hdq.add_const (costTotal v)
  have h := ((hdM.add ((hasDerivAt_negMulLog hq.ne').comp y hdq)).add_const
    (∑ i, negMulLog (v i))).sub ((hasDerivAt_negMulLog hM.ne').comp y hdM)
  simp only [bumpedCost_entropy]
  rw [log_div hq.ne' hM.ne']
  convert h using 1
  · funext z
    rfl
  · ring

theorem bumpedRoot_hasDerivAt {ι : Type*} [Fintype ι] {a y : ℝ} {v : ι → ℝ}
    (ha : 0 ≤ a) (hv : ∀ i, 0 ≤ v i) (hy : 0 < y) :
    HasDerivAt (fun z : ℝ => sqrt (costEntropy (bumpedCost a v z)))
      (y*(1-log ((a+y^2)/(a+y^2+costTotal v)))/sqrt (costEntropy (bumpedCost a v y))) y := by
  have h := (bumpedCost_hasDerivAt ha hv hy).sqrt (bumpedCost_positive ha hv hy).ne'
  convert h using 1
  ring

theorem bumpedRoot_slope_le_one {ι : Type*} [Fintype ι] {a y : ℝ} {v : ι → ℝ}
    (ha : 0 ≤ a) (hv : ∀ i, 0 ≤ v i) (hy : 0 < y) :
    y*(1-log ((a+y^2)/(a+y^2+costTotal v)))/sqrt (costEntropy (bumpedCost a v y)) ≤ 1 := by
  let q := a+y^2
  let M := q+costTotal v
  let p := q/M
  let G := costEntropy (bumpedCost a v y)
  have hq : 0 < q := by dsimp [q]; nlinarith only [ha,hy]
  have hM : 0 < M := add_pos_of_pos_of_nonneg hq (costTotal_nonneg hv)
  have hp : 0 < p := div_pos hq hM
  have hp1 : p ≤ 1 := (div_le_one hM).mpr (le_add_of_nonneg_right (costTotal_nonneg hv))
  have hs := binary_entropy_slope_bound hp hp1
  have hm := mul_le_mul_of_nonneg_left hs hM.le
  have hMp : M*p=q := by dsimp [p]; field_simp
  have he : M*(p*(1-log p)^2) = q*(1-log p)^2 := by rw [← mul_assoc,hMp]
  rw [he] at hm
  have hb := bumpedCost_binary_lower ha hv hy
  change M*(1+binEntropy p) ≤ G at hb
  have hyq : y^2*(1-log p)^2 ≤ q*(1-log p)^2 := by
    exact mul_le_mul_of_nonneg_right (by dsimp [q]; linarith) (sq_nonneg _)
  have hG : 0 < G := bumpedCost_positive ha hv hy
  have hr : 0 < sqrt G := sqrt_pos.mpr hG
  change y*(1-log p)/sqrt G ≤ 1
  apply (div_le_one hr).mpr
  have hsquare : (y*(1-log p))^2 ≤ (sqrt G)^2 := by
    rw [sq_sqrt hG.le,mul_pow]
    exact hyq.trans (hm.trans hb)
  exact (sq_le_sq₀ (mul_nonneg hy.le (by linarith [log_nonpos hp.le hp1])) hr.le).mp hsquare

end ThresholdHC.QuantileSharpLaw
