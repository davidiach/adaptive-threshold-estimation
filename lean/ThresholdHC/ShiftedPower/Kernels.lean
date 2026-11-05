import ThresholdHC.SubcriticalPower.Sublinear
import ThresholdHC.Tier6.HardPair

noncomputable section
open MeasureTheory Set Real
namespace ThresholdHC.ShiftedPower
open ThresholdHC.Tier6 ThresholdHC.SubcriticalPower ThresholdHC.RareAboveTwo

private def powerGap (p : ℝ) (hp : 1 ≤ p) (d : Gap) : Gap :=
  ⟨(d:ℝ)^p,Real.rpow_pos_of_pos d.property.1 _,(show (d:ℝ)^p ≤ (d:ℝ)^(1:ℝ) from
    Real.rpow_le_rpow_of_exponent_ge d.property.1 (by linarith [d.property.2]) hp).trans
      (by simpa using d.property.2)⟩

private theorem measurable_powerGap (p : ℝ) (hp : 1 ≤ p) : Measurable (powerGap p hp) := by
  apply Measurable.subtype_mk
  exact measurable_subtype_coe.pow_const _

/-- Raising each positive gap to power p turns the margin exponent into
α/p. This reduces integrated classifier error and work to the already
checked sublinear modulus, uniformly over actual laws in the envelope. -/
theorem power_kernel_bound (ν : Measure Gap) [IsProbabilityMeasure ν] {α p a h : ℝ}
    (hm : PowerMargin ν α a) (ha : 0 < a) (hh : 0 < h) (hα : 0 < α) (hp : 1 ≤ p) (hap : α < p) :
    (∫ d : Gap, min 1 ((h/(d:ℝ))^p) ∂ν) ≤ (h/a)^α/(1-α/p) := by
  have hp' : 0 < p := by linarith
  let g := powerGap p hp
  have hg : Measurable g := measurable_powerGap p hp
  let ξ := ν.map g
  let _ : IsProbabilityMeasure ξ := by dsimp [ξ]; exact Measure.isProbabilityMeasure_map_iff hg.aemeasurable |>.mpr inferInstance
  have hmargin : PowerMargin ξ (α/p) (a^p) := by
    intro x hx hxa
    let b := x^(p⁻¹)
    have hb : 0 < b := Real.rpow_pos_of_pos hx _
    have hbp : b^p=x := Real.rpow_inv_rpow hx.le hp'.ne'
    have hba := (Real.rpow_lt_rpow_iff hb.le ha.le hp').mp (hbp.trans_lt hxa)
    have hs : g ⁻¹' {d : Gap | (d:ℝ) ≤ x} = {d : Gap | (d:ℝ) ≤ b} := by
      ext d
      change (d:ℝ)^p ≤ x ↔ (d:ℝ) ≤ b
      rw [← hbp,Real.rpow_le_rpow_iff d.property.1.le hb.le hp']
    change ((ν.map g) {d : Gap | (d:ℝ) ≤ x}).toReal ≤ _
    rw [Measure.map_apply hg (measurableSet_le measurable_subtype_coe measurable_const),hs]
    apply (hm b hb hba).trans_eq
    rw [Real.div_rpow hb.le ha.le,Real.div_rpow hx.le (Real.rpow_nonneg ha.le _),
      ← Real.rpow_mul ha.le,show p*(α/p)=α by field_simp]
    dsimp [b]
    rw [← Real.rpow_mul hx.le,show p⁻¹*α=α/p by ring]
  have he := sublinear_modulus ξ hmargin (Real.rpow_pos_of_pos ha _) (div_pos hα hp') ((div_lt_one hp').mpr hap)
    (Real.rpow_pos_of_pos hh p)
  unfold modulus at he
  rw [integral_map hg.aemeasurable ((measurable_clippedGap (h^p)).aestronglyMeasurable)] at he
  have hfunc (d : Gap) : clippedGap (h^p) (g d) = min 1 ((h/(d:ℝ))^p) := by
    change min 1 (h^p/(d:ℝ)^p) = _
    rw [Real.div_rpow hh.le d.property.1.le]
  simp only [hfunc,← Real.div_rpow hh.le ha.le,← Real.rpow_mul (div_nonneg hh.le ha.le),
    show p*(α/p)=α by field_simp] at he
  exact he

end ThresholdHC.ShiftedPower
