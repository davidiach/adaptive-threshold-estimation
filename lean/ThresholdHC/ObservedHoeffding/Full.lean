import ThresholdHC.ObservedHoeffding.Specification
import ThresholdHC.ObservedHoeffding.Lower
import ThresholdHC.ObservedHoeffding.Construction

/-! The Hoeffding replication count of `prop:outer` (`paper/v6/core.tex`).

`weighted_hoeffding_target` and `replication_tail_target` are the weighted Hoeffding
bound and the displayed replication tail (`Hoeffding.lean`).
`hoeffding_confidence_lower_target` is the finite-cell testing lower bound under the
Hoeffding weight condition, and `hoeffding_design_lower_target` its form for every
finite measurable cell design (`Lower.lean`). `hoeffding_finite_observed` assembles
the replicated construction with `M = ⌈32 Δ⁻² log(2/δ)⌉₊` (`Construction.lean`), the
tail bound and the design-level lower bound. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.ObservedHoeffding
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.ObservedState

/-- Weighted Hoeffding for the sign target under a product sign prior. -/
theorem weighted_hoeffding_target : WeightedHoeffdingStatement := by
  intro I _ q w v r hw hv hs hr
  exact weighted_hoeffding q w hw hv hs hr

/-- The display in the proof of `prop:outer`. -/
theorem replication_tail_target : ReplicationTailStatement := by
  intro I _ q w M Δ δ hw hM hs hΔ hδ hcount
  exact replication_tail q w M hw hM hs hΔ hδ hcount

/-- `finite_confidence_lower` with the Hoeffding weight condition. -/
theorem hoeffding_confidence_lower_target : HoeffdingConfidenceLowerStatement := by
  intro m R _ A d w η qp qm hp hm B h Δ δ hB hh hΔ hδ hδ1 hη hd hsep hwn hcond hw hc
  exact hoeffding_confidence_lower A d w η qp qm hp hm hB hh hΔ hδ hδ1 hη hd hsep hwn hcond hw hc

/-- Every finite cell design meeting the Hoeffding condition forces the lower bound. -/
theorem hoeffding_design_lower_target : HoeffdingDesignLowerStatement := by
  intro h N cap cell hc δ hδ hd hcond R _ A B hB hw hconf
  exact hoeffding_design_lower h cap cell hc hδ hd hcond A hB hw hconf

/-- `prop:outer` with the paper's replicated construction and Hoeffding count. -/
theorem hoeffding_finite_observed : HoeffdingFiniteObservedStatement := by
  intro μ _ h δ hδ hd
  obtain ⟨N, M, c, v, cap, gap, cell, hc, hgap, hlaw, hcapb, hinj, hv, hvs, hcapc, hwc, hM,
    hMeq, hsq, hpos, hsep, hcdf⟩ := hoeffding_design_exists μ h hδ hd
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hcount : 32 * Real.log (2 / δ) / (cellDelta cap cell h) ^ 2 ≤ (M : ℝ) := by
    have hceil := Nat.le_ceil (32 * Real.log (2 / δ) / (cellDelta cap cell h) ^ 2)
    rw [← hMeq] at hceil
    exact hceil
  have htail := replication_exp_le (M := (M : ℝ)) hpos hδ hcount
  have hlog : 0 < Real.log (2 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ]; linarith)
  have hcond : 32 * Real.log (2 / δ) * (∑ i, (cellWeight cell i) ^ 2) ≤
      (cellDelta cap cell h) ^ 2 := by
    have h1 : 32 * Real.log (2 / δ) ≤ (M : ℝ) * (cellDelta cap cell h) ^ 2 :=
      (div_le_iff₀ (by positivity)).mp hcount
    calc 32 * Real.log (2 / δ) * (∑ i, (cellWeight cell i) ^ 2)
        ≤ 32 * Real.log (2 / δ) * (1 / (M : ℝ)) := by gcongr
      _ ≤ (cellDelta cap cell h) ^ 2 := by
        rw [mul_one_div, div_le_iff₀ hM']
        linarith
  refine ⟨N, M, c, v, cap, gap, cell, hc, hgap, hlaw, hcapb, hinj, hv, hvs, hcapc, hwc, hM, hMeq,
    hsq, htail, hpos, hsep, hcdf, ?_⟩
  intro R _ A B hB hw hconf
  exact hoeffding_design_lower h cap cell hc hδ hd hcond A hB hw hconf

end ThresholdHC.ObservedHoeffding
