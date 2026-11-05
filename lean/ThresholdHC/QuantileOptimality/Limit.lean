import ThresholdHC.QuantileOptimality.PriceAlgebra
import ThresholdHC.QuantileOptimality.Masses

noncomputable section
open Real Filter
open scoped Topology
namespace ThresholdHC.QuantileOptimality
open ThresholdHC.EntropyTailQuantile ThresholdHC.OptimalQuantile

theorem bandEdge_tendsto_zero :
    Tendsto bandEdge atTop (𝓝 (0 : ℝ)) := by
  change Tendsto (fun N : ℕ => ((2 : ℝ)⁻¹)^(N+1)) atTop (𝓝 (0 : ℝ))
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹) (by norm_num : (2 : ℝ)⁻¹ < 1)
  simpa only [pow_succ,zero_mul] using hp.mul_const ((2 : ℝ)⁻¹)

theorem shifted_bandEdge_tendsto_zero (m : ℕ) :
    Tendsto (fun N : ℕ => bandEdge (m+N+2)) atTop (𝓝 (0 : ℝ)) := by
  have h := bandEdge_tendsto_zero.mul_const ((2 : ℝ)⁻¹^(m+2))
  convert h using 1
  · funext N
    unfold bandEdge
    rw [← pow_add]
    congr 1
    omega
  · simp

theorem finite_price_tendsto {m : ℕ} (x : Option (Fin m) → ℝ) :
    Tendsto (fun N : ℕ =>
      sqrt (finiteEnvelope (chosenRarity m x) (1+x none) (bandEdge (m+N+2)))+
        (1+bandEdge N)*dyadicCost m x) atTop (𝓝 (sqrt (1+x none)+dyadicCost m x)) := by
  have henv := (finiteEnvelope_continuous (chosenRarity m x) (1+x none)).continuousAt.tendsto.comp
    (shifted_bandEdge_tendsto_zero m)
  rw [finiteEnvelope_zero] at henv
  have hroot := continuous_sqrt.continuousAt.tendsto.comp henv
  have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hcost := (hconst.add bandEdge_tendsto_zero).mul_const (dyadicCost m x)
  simpa only [Function.comp_apply,add_zero,one_mul] using hroot.add hcost

theorem exists_finite_price_witness {m : ℕ} (x : Option (Fin m) → ℝ) {k C : ℝ}
    (hprice : k*(sqrt (1+x none)+dyadicCost m x) < C) :
    ∃ N : ℕ, k*(sqrt (finiteEnvelope (chosenRarity m x) (1+x none) (bandEdge (m+N+2)))+
      (1+bandEdge N)*dyadicCost m x) < C := by
  have hlim := (finite_price_tendsto x).const_mul k
  exact ((tendsto_order.mp hlim).2 C hprice).exists

end ThresholdHC.QuantileOptimality
