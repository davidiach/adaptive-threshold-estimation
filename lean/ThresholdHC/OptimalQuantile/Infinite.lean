import ThresholdHC.OptimalQuantile.Series

noncomputable section
open Real Filter
open scoped BigOperators Topology
namespace ThresholdHC.OptimalQuantile

theorem finitePartition_eq_range (n : ℕ) (k u : ℝ) :
    finitePartition n k u = exp (1-dualPrice k u/(2*u))+
      ∑ j ∈ Finset.range n, exp (1-dualPrice k u*(2 : ℝ)^j) := by
  unfold finitePartition
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => exp (1-dualPrice k u*(2 : ℝ)^j)) n]

theorem finitePartition_tendsto {k u : ℝ} (hk : sqrt 2 ≤ k) (hu : 1 ≤ u) :
    Tendsto (fun n : ℕ => finitePartition n k u) atTop (𝓝 (partitionSeries k u)) := by
  have hs := (exponentialTail_summable (dualPrice_ge_two hk hu)).hasSum.tendsto_sum_nat
  have hc : Tendsto (fun _ : ℕ => exp (1-dualPrice k u/(2*u))) atTop
      (𝓝 (exp (1-dualPrice k u/(2*u)))) := tendsto_const_nhds
  have h := hc.add hs
  simpa only [finitePartition_eq_range,partitionSeries,exponentialTail] using h

theorem finitePartition_le_series {k u : ℝ} (hk : sqrt 2 ≤ k) (hu : 1 ≤ u) (n : ℕ) :
    finitePartition n k u ≤ partitionSeries k u := by
  rw [finitePartition_eq_range]
  unfold partitionSeries exponentialTail
  exact add_le_add le_rfl ((exponentialTail_summable (dualPrice_ge_two hk hu)).sum_le_tsum
    (Finset.range n) (fun j _ => (exp_pos _).le))

theorem partitionSeries_le_one_iff {k u : ℝ} (hk : sqrt 2 ≤ k) (hu : 1 ≤ u) :
    partitionSeries k u ≤ 1 ↔ ∀ n : ℕ, finitePartition n k u ≤ 1 := by
  constructor
  · intro h n
    exact (finitePartition_le_series hk hu n).trans h
  · intro h
    exact le_of_tendsto (finitePartition_tendsto hk hu) (Eventually.of_forall h)

theorem all_finite_bounds_iff_series {k : ℝ} (hk : sqrt 2 ≤ k) :
    (∀ n : ℕ, finiteVectorBound n k) ↔ ∀ u : ℝ, 1 ≤ u → partitionSeries k u ≤ 1 := by
  have hk1 : 1 ≤ k := (one_le_sqrt.mpr (by norm_num : (1 : ℝ) ≤ 2)).trans hk
  constructor
  · intro h u hu
    apply (partitionSeries_le_one_iff hk hu).mpr
    intro n
    exact (finiteVectorBound_iff_partition n hk1).mp (h n) u hu
  · intro h n
    apply (finiteVectorBound_iff_partition n hk1).mpr
    intro u hu
    exact (finitePartition_le_series hk hu n).trans (h u hu)

end ThresholdHC.OptimalQuantile
