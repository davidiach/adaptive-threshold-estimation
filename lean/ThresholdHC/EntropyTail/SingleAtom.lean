import ThresholdHC.EntropyTail.Objective
import ThresholdHC.EntropyTail.Specification

/-! On a point mass the selection functional is exactly `min{ρ, √ρ/(d√B)}`. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.EntropyTail
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo

/-- Every submeasure of a point mass is a multiple of it. -/
theorem eq_smul_dirac_of_le {σ : Measure Gap} {d : Gap} (hσ : σ ≤ Measure.dirac d) :
    σ = σ Set.univ • Measure.dirac d := by
  have hle := Measure.le_iff'.1 hσ
  ext A hA
  rw [Measure.smul_apply, smul_eq_mul]
  by_cases hd : d ∈ A
  · rw [Measure.dirac_apply_of_mem hd, mul_one]
    have hc : σ Aᶜ = 0 := by
      refine le_antisymm ((hle Aᶜ).trans ?_) zero_le
      rw [Measure.dirac_apply' _ hA.compl, Set.indicator_of_notMem (by simpa using hd)]
    rw [← measure_add_measure_compl hA, hc, add_zero]
  · rw [Measure.dirac_apply' _ hA, Set.indicator_of_notMem hd, mul_zero]
    refine le_antisymm ((hle A).trans ?_) zero_le
    rw [Measure.dirac_apply' _ hA, Set.indicator_of_notMem hd]

/-- The objective at any submeasure of `δ_d` is at least `min{ρ, h√(ρ d^{-2})}`. -/
theorem single_lower {d : Gap} {σ : Measure Gap} (hσ : σ ≤ Measure.dirac d) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (B : ℝ) :
    ENNReal.ofReal (min ρ (1 / Real.sqrt B * Real.sqrt (ρ * ((d : ℝ)⁻¹)^2))) ≤
      selectionObjective (Measure.dirac d) ρ B σ := by
  have hd := d.2
  have hh : 0 ≤ 1 / Real.sqrt B := by positivity
  have hi : 0 ≤ (d : ℝ)⁻¹ := inv_nonneg.2 hd.1.le
  have : IsFiniteMeasure σ := isFiniteMeasure_of_le _ hσ
  have hσeq := eq_smul_dirac_of_le hσ
  have hsσ : σ Set.univ = ENNReal.ofReal (σ Set.univ).toReal :=
    (ENNReal.ofReal_toReal (measure_ne_top σ _)).symm
  have hs1 : σ Set.univ ≤ 1 := (Measure.le_iff'.1 hσ Set.univ).trans (le_of_eq measure_univ)
  have hs0 : 0 ≤ (σ Set.univ).toReal := ENNReal.toReal_nonneg
  have hs1' : (σ Set.univ).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top hs1
  generalize (σ Set.univ).toReal = s at hsσ hs0 hs1'
  have hm0 : 0 ≤ min 1 (1 / Real.sqrt B / (d : ℝ)) :=
    le_min zero_le_one (div_nonneg hh hd.1.le)
  -- entropy part
  have hg : ENNReal.ofReal (s * ((d : ℝ)⁻¹)^2) ≤ gamma σ := by
    refine le_trans (le_of_eq ?_) (lintegral_le_gamma σ)
    conv_rhs => rw [hσeq]
    rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul, hsσ, ENNReal.ofReal_mul hs0]
  have hent : ENNReal.ofReal (1 / Real.sqrt B * Real.sqrt (ρ * (s * ((d : ℝ)⁻¹)^2))) ≤
      ENNReal.ofReal (1 / Real.sqrt B) * (ENNReal.ofReal ρ * gamma σ) ^ (1/2 : ℝ) := by
    rw [← entropyTerm_ofReal (g := s * ((d : ℝ)⁻¹)^2) hh hρ.le
      (mul_nonneg hs0 (sq_nonneg _))]
    gcongr
  -- remainder part
  have hts : tailCost σ (1 / Real.sqrt B) =
      ENNReal.ofReal (s * min 1 (1 / Real.sqrt B / (d : ℝ))) := by
    rw [hσeq, tailCost_smul, tailCost_dirac, hsσ, ← ENNReal.ofReal_mul hs0]
  have htail : tailCost (Measure.dirac d - σ) (1 / Real.sqrt B) =
      ENNReal.ofReal (min 1 (1 / Real.sqrt B / (d : ℝ)) -
        s * min 1 (1 / Real.sqrt B / (d : ℝ))) := by
    have hadd := tailCost_sub_add hσ (1 / Real.sqrt B)
    rw [hts, tailCost_dirac] at hadd
    rw [ENNReal.ofReal_sub _ (mul_nonneg hs0 hm0)]
    exact ENNReal.eq_sub_of_add_eq ENNReal.ofReal_ne_top hadd
  -- real inequality
  have hreal : min ρ (1 / Real.sqrt B * Real.sqrt (ρ * ((d : ℝ)⁻¹)^2)) ≤
      1 / Real.sqrt B * Real.sqrt (ρ * (s * ((d : ℝ)⁻¹)^2)) +
        (min 1 (1 / Real.sqrt B / (d : ℝ)) - s * min 1 (1 / Real.sqrt B / (d : ℝ))) := by
    have hsq : Real.sqrt (ρ * (s * ((d : ℝ)⁻¹)^2)) =
        Real.sqrt s * Real.sqrt (ρ * ((d : ℝ)⁻¹)^2) := by
      rw [show ρ * (s * ((d : ℝ)⁻¹)^2) = s * (ρ * ((d : ℝ)⁻¹)^2) by ring, Real.sqrt_mul hs0]
    have hss : s ≤ Real.sqrt s := by
      have h1 := Real.sqrt_le_sqrt hs1'
      rw [Real.sqrt_one] at h1
      nlinarith [Real.mul_self_sqrt hs0, Real.sqrt_nonneg s]
    have hr1 : Real.sqrt ρ ≤ 1 := by
      have h1 := Real.sqrt_le_sqrt hρ1
      rwa [Real.sqrt_one] at h1
    have hx : Real.sqrt (ρ * ((d : ℝ)⁻¹)^2) = Real.sqrt ρ * (d : ℝ)⁻¹ := by
      rw [Real.sqrt_mul hρ.le, Real.sqrt_sq hi]
    -- k = min ρ x is below both x and the single-gap cost min{1,h/d}
    have hk1 := min_le_right ρ (1 / Real.sqrt B * Real.sqrt (ρ * ((d : ℝ)⁻¹)^2))
    have hk2 : min ρ (1 / Real.sqrt B * Real.sqrt (ρ * ((d : ℝ)⁻¹)^2)) ≤
        min 1 (1 / Real.sqrt B / (d : ℝ)) := by
      refine le_min ((min_le_left _ _).trans (by linarith)) ((min_le_right _ _).trans ?_)
      rw [hx, le_div_iff₀ hd.1]
      have hdd : (d : ℝ)⁻¹ * (d : ℝ) = 1 := inv_mul_cancel₀ hd.1.ne'
      calc 1 / Real.sqrt B * (Real.sqrt ρ * (d : ℝ)⁻¹) * (d : ℝ)
          = 1 / Real.sqrt B * Real.sqrt ρ * ((d : ℝ)⁻¹ * (d : ℝ)) := by ring
        _ = 1 / Real.sqrt B * Real.sqrt ρ := by rw [hdd, mul_one]
        _ ≤ 1 / Real.sqrt B * 1 := mul_le_mul_of_nonneg_left hr1 hh
        _ = 1 / Real.sqrt B := mul_one _
    have hxp : 0 ≤ 1 / Real.sqrt B * Real.sqrt (ρ * ((d : ℝ)⁻¹)^2) :=
      mul_nonneg hh (Real.sqrt_nonneg _)
    rw [hsq]
    nlinarith [mul_le_mul_of_nonneg_left hss hxp, mul_nonneg (sub_nonneg.2 hk1) hs0,
      mul_nonneg (sub_nonneg.2 hk2) (sub_nonneg.2 hs1')]
  calc ENNReal.ofReal (min ρ (1 / Real.sqrt B * Real.sqrt (ρ * ((d : ℝ)⁻¹)^2)))
      ≤ ENNReal.ofReal (1 / Real.sqrt B * Real.sqrt (ρ * (s * ((d : ℝ)⁻¹)^2))) +
        ENNReal.ofReal (min 1 (1 / Real.sqrt B / (d : ℝ)) -
          s * min 1 (1 / Real.sqrt B / (d : ℝ))) := by
        rw [← ENNReal.ofReal_add (mul_nonneg hh (Real.sqrt_nonneg _))
          (by nlinarith [mul_le_mul_of_nonneg_right hs1' hm0])]
        exact ENNReal.ofReal_le_ofReal hreal
    _ ≤ selectionObjective (Measure.dirac d) ρ B σ := by
        rw [← htail]
        exact add_le_add hent le_rfl

theorem single_atom : SingleAtomStatement := by
  intro ρ B hρ hρ4 hB d
  have hd := d.2
  have hrate : aboveTwoRate (d : ℝ) ρ B =
      min ρ (1 / Real.sqrt B * Real.sqrt (ρ * ((d : ℝ)⁻¹)^2)) := by
    unfold aboveTwoRate
    congr 1
    have hB0 : Real.sqrt B ≠ 0 := (Real.sqrt_pos.2 hB).ne'
    have hd0 : (d : ℝ) ≠ 0 := hd.1.ne'
    rw [Real.sqrt_mul hρ.le, Real.sqrt_sq (inv_nonneg.2 hd.1.le)]
    field_simp
  rw [hrate]
  refine le_antisymm ?_ ?_
  · have hobj : selectionObjective (Measure.dirac d) ρ B (Measure.dirac d) ≤
        ENNReal.ofReal (1 / Real.sqrt B * Real.sqrt (ρ * ((d : ℝ)⁻¹)^2)) := by
      rw [selectionObjective_self,
        ← entropyTerm_ofReal (h := 1 / Real.sqrt B) (by positivity) hρ.le
          (sq_nonneg ((d : ℝ)⁻¹))]
      gcongr
      exact gamma_dirac_le d
    rw [ENNReal.ofReal_min]
    exact le_min (selection_le_rho _ _ _) ((selection_le_objective le_rfl ρ B).trans hobj)
  · unfold selection
    exact le_min (ENNReal.ofReal_le_ofReal (min_le_left _ _))
      (le_iInf₂ fun σ hσ => single_lower hσ hρ (by linarith) B)

end ThresholdHC.EntropyTail
