import ThresholdHC.PaperStatements.Specification
import ThresholdHC.QuantileOptimality.Full
import ThresholdHC.QuantilePrice.Full
import ThresholdHC.QuantileSharpLaw.Full
import ThresholdHC.SelectionStability.Approximation

/-! Quantile constants.

The partition series at `k = 1.462554551279`, `u = 1.2591049` exceeds one: five
of its exponential terms already sum to more than one, by Taylor upper bounds on
`exp` at points of `[0,1]` raised to powers of two. Since the scalar peak is
strictly decreasing and equals one at the root, the root exceeds
`1.462554551279`, the lower end of the paper's decimal bracket.
Selection stability transfers any comparison `K ≤ Q ≤ cK` to the lower
endpoint `Q/c`; the comparisons with `c = 31/20` and `c = c_vec` are checked. -/
noncomputable section
open Real
namespace ThresholdHC.PaperStatements
open ThresholdHC.OptimalQuantile

theorem taylor_upper {x r : ℝ} (n : ℕ) (hn : 0 < n) (h0 : 0 ≤ x) (h1 : x ≤ 1)
    (hr : (∑ i ∈ Finset.range n, x ^ i / (i.factorial : ℝ)) +
      x ^ n * (n + 1) / ((n.factorial : ℝ) * n) ≤ r) : exp x ≤ r :=
  (Real.exp_bound' h0 h1 hn).trans hr

theorem exp_neg_lower {x r : ℝ} (n : ℕ) (hx : exp x ≤ r) : 1 / r ^ n ≤ exp (-(n * x)) := by
  rw [Real.exp_neg, Real.exp_nat_mul, ← one_div]
  exact one_div_le_one_div_of_le (pow_pos (exp_pos x) n) (pow_le_pow_left₀ (exp_pos x).le hx n)

theorem root_series_lower :
    1 < partitionSeries (1462554551279/1000000000000) (12591049/10000000) := by
  have hP : dualPrice (1462554551279/1000000000000) (12591049/10000000) = (184720422578013362354817863542502592241/62955245000000000000000000000000000000 : ℝ) := by
    unfold dualPrice; norm_num
  unfold partitionSeries
  rw [hP]
  have hA : 1 / (11795993010656344669639/10000000000000000000000 : ℝ) ^ 1 ≤ exp (1 - (184720422578013362354817863542502592241/62955245000000000000000000000000000000 : ℝ) / (2 * (12591049/10000000))) := by
    have hx : exp (26185907657612362354817863542502592241/158534514920401000000000000000000000000 : ℝ) ≤ (11795993010656344669639/10000000000000000000000 : ℝ) := taylor_upper 14 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have := exp_neg_lower 1 hx
    convert this using 2
    norm_num
  have h0 : 1 / (13151229065602658103947/5000000000000000000000 : ℝ) ^ 2 ≤ exp (1 - (184720422578013362354817863542502592241/62955245000000000000000000000000000000 : ℝ) * 2 ^ 0) := by
    have hx : exp (121765177578013362354817863542502592241/125910490000000000000000000000000000000 : ℝ) ≤ (13151229065602658103947/5000000000000000000000 : ℝ) := taylor_upper 18 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have := exp_neg_lower 2 hx
    convert this using 2
    norm_num
  have h1 : 1 / (1148589909305794389709/625000000000000000000 : ℝ) ^ 8 ≤ exp (1 - (184720422578013362354817863542502592241/62955245000000000000000000000000000000 : ℝ) * 2 ^ 1) := by
    have hx : exp (153242800078013362354817863542502592241/251820980000000000000000000000000000000 : ℝ) ≤ (1148589909305794389709/625000000000000000000 : ℝ) := taylor_upper 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have := exp_neg_lower 8 hx
    convert this using 2
    norm_num
  have h2 : 1 / (3912536300880965226043/2000000000000000000000 : ℝ) ^ 16 ≤ exp (1 - (184720422578013362354817863542502592241/62955245000000000000000000000000000000 : ℝ) * 2 ^ 2) := by
    have hx : exp (168981611328013362354817863542502592241/251820980000000000000000000000000000000 : ℝ) ≤ (3912536300880965226043/2000000000000000000000 : ℝ) := taylor_upper 12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have := exp_neg_lower 16 hx
    convert this using 2
    norm_num
  have h3 : 1 / (20183667677759313619029/10000000000000000000000 : ℝ) ^ 32 ≤ exp (1 - (184720422578013362354817863542502592241/62955245000000000000000000000000000000 : ℝ) * 2 ^ 3) := by
    have hx : exp (176851016953013362354817863542502592241/251820980000000000000000000000000000000 : ℝ) ≤ (20183667677759313619029/10000000000000000000000 : ℝ) := taylor_upper 10 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
    have := exp_neg_lower 32 hx
    convert this using 2
    norm_num
  have htail : exp (1 - (184720422578013362354817863542502592241/62955245000000000000000000000000000000 : ℝ) * 2 ^ 0) + exp (1 - (184720422578013362354817863542502592241/62955245000000000000000000000000000000 : ℝ) * 2 ^ 1) + exp (1 - (184720422578013362354817863542502592241/62955245000000000000000000000000000000 : ℝ) * 2 ^ 2) + exp (1 - (184720422578013362354817863542502592241/62955245000000000000000000000000000000 : ℝ) * 2 ^ 3) ≤
      exponentialTail (184720422578013362354817863542502592241/62955245000000000000000000000000000000 : ℝ) := by
    have hs := exponentialTail_summable (show (2 : ℝ) ≤ (184720422578013362354817863542502592241/62955245000000000000000000000000000000 : ℝ) by norm_num)
    have := hs.sum_le_tsum (Finset.range 4) (fun j _ => (exp_pos _).le)
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_one] at this
    exact this
  have hnum : (1 : ℝ) < 1 / (11795993010656344669639/10000000000000000000000 : ℝ) ^ 1 + 1 / (13151229065602658103947/5000000000000000000000 : ℝ) ^ 2 + 1 / (1148589909305794389709/625000000000000000000 : ℝ) ^ 8 + 1 / (3912536300880965226043/2000000000000000000000 : ℝ) ^ 16 + 1 / (20183667677759313619029/10000000000000000000000 : ℝ) ^ 32 := by norm_num
  linarith

theorem root_lower : (1462554551279/1000000000000 : ℝ) < scalarRoot := by
  have hk : sqrt 2 ≤ (1462554551279/1000000000000 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hpeak : 1 < scalarPeak (1462554551279/1000000000000) :=
    root_series_lower.trans_le (partitionSeries_le_peak hk (by norm_num))
  by_contra h
  push Not at h
  have := (scalarPeak_le_one_iff hk).mpr h
  linarith

open MeasureTheory in
/-- Selection stability with the lower endpoint `Q/c` from any comparison
`K ≤ Q ≤ cK` at the rounded law. -/
theorem factor_enclosure (μ μ₀ : Measure Tier6.Gap) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure μ₀] (T : Tier6.Gap → Tier6.Gap) (hm : Measurable T) {r η ρ B c : ℝ}
    (hc : 0 < c) (hr : 1 ≤ r) (hρ : 0 < ρ) (hrho : ρ ≤ 1/4) (hB : 0 < B)
    (hη : tvDist μ μ₀ / 2 ≤ η)
    (hd : ∀ d : Tier6.Gap, (d:ℝ) ≤ (T d:ℝ) ∧ (T d:ℝ) ≤ r*(d:ℝ))
    (hb : ∀ j, T ⁻¹' EntropyTail.band j = EntropyTail.band j)
    (hcomp : EntropyTail.selection (μ₀.map T) ρ B ≤
        EntropyTailQuantile.closedQuantileValue (μ₀.map T) ρ B ∧
      EntropyTailQuantile.closedQuantileValue (μ₀.map T) ρ B ≤
        ENNReal.ofReal c * EntropyTail.selection (μ₀.map T) ρ B) :
    max 0 ((EntropyTailQuantile.closedQuantileValue (μ₀.map T) ρ B).toReal / c - η) ≤
        (EntropyTail.selection μ ρ B).toReal ∧
      (EntropyTail.selection μ ρ B).toReal ≤
        min ρ (r*(EntropyTailQuantile.closedQuantileValue (μ₀.map T) ρ B).toReal + η) := by
  have hf := ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (EntropyTail.selection_le_rho (μ₀.map T) ρ B)
  have hupper := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf) hcomp.2
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le] at hupper
  apply SelectionStability.transfer_enclosure μ μ₀ T hm hr hρ hrho hB hη hd hb
  · rw [div_le_iff₀ hc]; linarith only [hupper]
  · exact ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (min_le_left _ _)) hcomp.1

open MeasureTheory in
theorem stability_quantile (μ μ₀ : Measure Tier6.Gap) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure μ₀] (T : Tier6.Gap → Tier6.Gap) (hm : Measurable T) {r η ρ B : ℝ}
    (hr : 1 ≤ r) (hρ : 0 < ρ) (hrho : ρ ≤ 1/4) (hB : 0 < B)
    (hη : tvDist μ μ₀ / 2 ≤ η)
    (hd : ∀ d : Tier6.Gap, (d:ℝ) ≤ (T d:ℝ) ∧ (T d:ℝ) ≤ r*(d:ℝ))
    (hb : ∀ j, T ⁻¹' EntropyTail.band j = EntropyTail.band j) :
    max 0 (20/31*(EntropyTailQuantile.closedQuantileValue (μ₀.map T) ρ B).toReal - η) ≤
        (EntropyTail.selection μ ρ B).toReal ∧
      (EntropyTail.selection μ ρ B).toReal ≤
        min ρ (r*(EntropyTailQuantile.closedQuantileValue (μ₀.map T) ρ B).toReal + η) := by
  have : IsProbabilityMeasure (μ₀.map T) :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).2 inferInstance
  obtain ⟨h1, h2⟩ := factor_enclosure μ μ₀ T hm (c := 31/20) (by norm_num) hr hρ hrho hB hη hd hb
    (QuantilePrice.quantile_le_31_20_selection (μ₀.map T) hρ hrho hB)
  refine ⟨?_, h2⟩
  convert h1 using 3
  ring

open MeasureTheory in
theorem stability_sharp (μ μ₀ : Measure Tier6.Gap) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure μ₀] (T : Tier6.Gap → Tier6.Gap) (hm : Measurable T) {r η ρ B : ℝ}
    (hr : 1 ≤ r) (hρ : 0 < ρ) (hrho : ρ ≤ 1/4) (hB : 0 < B)
    (hη : tvDist μ μ₀ / 2 ≤ η)
    (hd : ∀ d : Tier6.Gap, (d:ℝ) ≤ (T d:ℝ) ∧ (T d:ℝ) ≤ r*(d:ℝ))
    (hb : ∀ j, T ⁻¹' EntropyTail.band j = EntropyTail.band j) :
    max 0 ((EntropyTailQuantile.closedQuantileValue (μ₀.map T) ρ B).toReal / scalarRoot - η) ≤
        (EntropyTail.selection μ ρ B).toReal ∧
      (EntropyTail.selection μ ρ B).toReal ≤
        min ρ (r*(EntropyTailQuantile.closedQuantileValue (μ₀.map T) ρ B).toReal + η) := by
  have : IsProbabilityMeasure (μ₀.map T) :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).2 inferInstance
  have hc : 0 < scalarRoot := (Real.sqrt_pos.2 (by norm_num)).trans scalarRoot_interior.1
  exact factor_enclosure μ μ₀ T hm hc hr hρ hrho hB hη hd hb
    (QuantileSharpLaw.locked_sharp_quantile_comparison (μ₀.map T) hρ hrho hB)

end ThresholdHC.PaperStatements
