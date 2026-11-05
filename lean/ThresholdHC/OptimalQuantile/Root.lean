import ThresholdHC.OptimalQuantile.Endpoints
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
open Real
namespace ThresholdHC.OptimalQuantile

theorem exists_unique_scalarRoot :
    ∃! k : ℝ, k ∈ Set.Icc (sqrt 2) (31/20) ∧ scalarPeak k = 1 := by
  have hcap : sqrt (2 : ℝ) ≤ 31/20 := sqrt_le_iff.mpr (by norm_num)
  have hc : ContinuousOn scalarPeak (Set.Icc (sqrt 2) (31/20)) :=
    scalarPeak_continuousOn.mono (fun _ h => h.1)
  obtain ⟨k,hk,he⟩ := intermediate_value_Icc' hcap hc
    (show (1 : ℝ) ∈ Set.Icc (scalarPeak (31/20)) (scalarPeak (sqrt 2)) from
      ⟨scalarPeak_upper_endpoint.le,scalarPeak_lower_endpoint.le⟩)
  refine ⟨k,⟨hk,he⟩,?_⟩
  intro l hl
  exact scalarPeak_strictAntiOn.injOn hl.1.1 hk.1 (hl.2.trans he.symm)

def scalarRoot : ℝ := exists_unique_scalarRoot.choose

theorem scalarRoot_spec :
    scalarRoot ∈ Set.Icc (sqrt 2) (31/20) ∧ scalarPeak scalarRoot = 1 :=
  exists_unique_scalarRoot.choose_spec.1

theorem scalarRoot_interior : sqrt 2 < scalarRoot ∧ scalarRoot < 31/20 := by
  have hs := scalarRoot_spec
  constructor
  · apply lt_of_le_of_ne hs.1.1
    intro he
    have h := scalarPeak_lower_endpoint
    rw [he,hs.2] at h
    exact (lt_irrefl _ h)
  · apply lt_of_le_of_ne hs.1.2
    intro he
    have h := scalarPeak_upper_endpoint
    rw [← he,hs.2] at h
    exact (lt_irrefl _ h)

theorem scalarPeak_le_one_iff {k : ℝ} (hk : sqrt 2 ≤ k) :
    scalarPeak k ≤ 1 ↔ scalarRoot ≤ k := by
  constructor
  · intro h
    by_contra hn
    have hlt := scalarPeak_strictAntiOn hk scalarRoot_spec.1.1 (lt_of_not_ge hn)
    rw [scalarRoot_spec.2] at hlt
    exact (not_lt_of_ge h hlt)
  · intro h
    have hm := scalarPeak_strictAntiOn.antitoneOn scalarRoot_spec.1.1 hk h
    rwa [scalarRoot_spec.2] at hm

theorem scalarRoot_bounds_all_finite (n : ℕ) : finiteVectorBound n scalarRoot :=
  (all_finite_bounds_iff_peak scalarRoot_spec.1.1 scalarRoot_spec.1.2).mpr
    scalarRoot_spec.2.le n

theorem all_finite_bounds_iff_root {k : ℝ} (hk : sqrt 2 ≤ k) :
    (∀ n : ℕ, finiteVectorBound n k) ↔ scalarRoot ≤ k := by
  by_cases hcap : k ≤ 31/20
  · exact (all_finite_bounds_iff_peak hk hcap).trans (scalarPeak_le_one_iff hk)
  · have hroot : scalarRoot < k := scalarRoot_spec.1.2.trans_lt (lt_of_not_ge hcap)
    constructor
    · intro _
      exact hroot.le
    · intro _
      apply (all_finite_bounds_iff_series hk).mpr
      intro u hu
      have h := partitionSeries_strict_in_factor scalarRoot_spec.1.1 hroot hu
      exact h.le.trans ((all_finite_bounds_iff_series scalarRoot_spec.1.1).mp
        scalarRoot_bounds_all_finite u hu)

end ThresholdHC.OptimalQuantile
