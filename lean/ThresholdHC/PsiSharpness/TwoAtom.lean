import ThresholdHC.PsiSharpness.Specification
import ThresholdHC.PsiClosedForm.Full
import ThresholdHC.QuantileOptimality.AtomicQuantile

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThresholdHC.PsiSharpness
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.PsiClosedForm
open ThresholdHC.EntropyTailQuantile

def twoAtomLaw (ρ : ℝ) (d₁ d₂ : Gap) : Measure Gap :=
  ENNReal.ofReal ρ • Measure.dirac d₁ + ENNReal.ofReal (1 - ρ) • Measure.dirac d₂

theorem twoAtom_probability {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (d₁ d₂ : Gap) :
    IsProbabilityMeasure (twoAtomLaw ρ d₁ d₂) := by
  constructor
  simp only [twoAtomLaw, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem
    (mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add hρ (sub_nonneg.2 hρ1)]
  norm_num

theorem twoAtom_tail {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (d₁ d₂ : Gap)
    (hd : (d₁ : ℝ) < (d₂ : ℝ)) :
    quantileTail (twoAtomLaw ρ d₁ d₂) ρ = ENNReal.ofReal ρ • Measure.dirac d₁ := by
  have := twoAtom_probability hρ.le hρ1 d₁ d₂
  apply ThresholdHC.QuantileOptimality.quantileTail_at_min_atom _ hρ hρ1 d₁
  · rw [twoAtomLaw, ae_add_measure_iff]
    constructor
    · apply Measure.ae_smul_measure
      simp
    · apply Measure.ae_smul_measure
      simpa using hd.le
  · have hne : d₂ ≠ d₁ := fun he => hd.ne (congrArg Subtype.val he.symm)
    simp [twoAtomLaw, measureReal_def, hne, hρ.le]

theorem twoAtom_core {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (d₁ d₂ : Gap)
    (hd : (d₁ : ℝ) < (d₂ : ℝ)) :
    quantileCore (twoAtomLaw ρ d₁ d₂) ρ = ENNReal.ofReal (1 - ρ) • Measure.dirac d₂ := by
  have : IsFiniteMeasure (ENNReal.ofReal ρ • Measure.dirac d₁) := ⟨by simp⟩
  rw [quantileCore, twoAtom_tail hρ hρ1 d₁ d₂ hd, twoAtomLaw, add_comm]
  exact Measure.add_sub_cancel

theorem inverseSquareCost_atom {w : ℝ} (hw : 0 ≤ w) (d : Gap) :
    inverseSquareCost (ENNReal.ofReal w • Measure.dirac d) =
      ENNReal.ofReal (w / (d : ℝ)^2) := by
  simp only [inverseSquareCost, lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
  rw [← ENNReal.ofReal_mul hw]
  congr 1
  field_simp

theorem twoAtom_quantile {ρ B : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hB : 0 < B)
    (d₁ d₂ : Gap) (hd : (d₁ : ℝ) < (d₂ : ℝ))
    (hbalance : (1 - ρ) / (d₂ : ℝ)^2 = ρ / (d₁ : ℝ)^2)
    (hh : 1 / Real.sqrt B ≤ (d₁ : ℝ) / 2) :
    quantileZero (twoAtomLaw ρ d₁ d₂) ρ B =
      ENNReal.ofReal (2 * (1 / Real.sqrt B) * ρ / (d₁ : ℝ)) := by
  have hd₁ := d₁.2.1
  have hh0 : 0 < 1 / Real.sqrt B := by positivity
  have hhd : 1 / Real.sqrt B ≤ (d₁ : ℝ) := by linarith [d₁.2.1]
  have hroot : Real.sqrt (ρ * (ρ / (d₁ : ℝ)^2)) = ρ / (d₁ : ℝ) := by
    rw [show ρ * (ρ / (d₁ : ℝ)^2) = (ρ / (d₁ : ℝ))^2 by ring]
    exact Real.sqrt_sq (by positivity)
  unfold quantileZero
  rw [twoAtom_tail hρ hρ1 d₁ d₂ hd, twoAtom_core hρ hρ1 d₁ d₂ hd,
    inverseSquareCost_atom (sub_nonneg.2 hρ1), hbalance,
    ← ENNReal.ofReal_mul hρ.le,
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.sqrt_eq_rpow,
    hroot, ← ENNReal.ofReal_mul hh0.le]
  have htail : ThresholdHC.EntropyTail.tailCost
      (ENNReal.ofReal ρ • Measure.dirac d₁) (1 / Real.sqrt B) =
      ENNReal.ofReal ((1 / Real.sqrt B) * ρ / (d₁ : ℝ)) := by
    simp only [ThresholdHC.EntropyTail.tailCost, lintegral_smul_measure, lintegral_dirac,
      smul_eq_mul, min_eq_right ((div_le_one d₁.2.1).2 hhd)]
    rw [← ENNReal.ofReal_mul hρ.le]
    congr 1
    ring
  rw [htail, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  have he : (1 / Real.sqrt B) * ρ / (d₁ : ℝ) +
      (1 / Real.sqrt B) * (ρ / (d₁ : ℝ)) = 2 * (1 / Real.sqrt B) * ρ / (d₁ : ℝ) := by ring
  rw [he, min_eq_right]
  apply ENNReal.ofReal_le_ofReal
  rw [div_le_iff₀ d₁.2.1]
  nlinarith

/-- Cauchy--Schwarz with the entire law selected, without cost entropy. -/
theorem rarePsi_le_full_cost (μ : Measure Gap) [IsProbabilityMeasure μ]
    (ρ : ℝ) {h : ℝ} (hh : 0 < h) :
    rarePsi μ ρ h ≤ ENNReal.ofReal h * (ENNReal.ofReal ρ * inverseSquareCost μ) ^ (1/2 : ℝ) := by
  unfold rarePsi
  refine iSup₂_le fun v hv => ?_
  have hb := rareObjective_le_zero μ hh hv μ le_rfl
  simpa [ThresholdHC.EntropyTail.tailCost] using hb

theorem twoAtom_psi_upper {ρ h : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hh : 0 < h)
    (d₁ d₂ : Gap) (hbalance : (1 - ρ) / (d₂ : ℝ)^2 = ρ / (d₁ : ℝ)^2) :
    rarePsi (twoAtomLaw ρ d₁ d₂) ρ h ≤
      ENNReal.ofReal (Real.sqrt 2 * h * ρ / (d₁ : ℝ)) := by
  have := twoAtom_probability hρ.le hρ1 d₁ d₂
  have hd₁ := d₁.2.1
  have hcost : inverseSquareCost (twoAtomLaw ρ d₁ d₂) =
      ENNReal.ofReal (2 * ρ / (d₁ : ℝ)^2) := by
    have he : inverseSquareCost (twoAtomLaw ρ d₁ d₂) =
        inverseSquareCost (ENNReal.ofReal ρ • Measure.dirac d₁) +
          inverseSquareCost (ENNReal.ofReal (1 - ρ) • Measure.dirac d₂) :=
      lintegral_add_measure _ _ _
    rw [he, inverseSquareCost_atom hρ.le,
      inverseSquareCost_atom (sub_nonneg.2 hρ1), hbalance,
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  have hroot : Real.sqrt (ρ * (2 * ρ / (d₁ : ℝ)^2)) = Real.sqrt 2 * ρ / (d₁ : ℝ) := by
    have hsq : (Real.sqrt 2 * ρ / (d₁ : ℝ))^2 = ρ * (2 * ρ / (d₁ : ℝ)^2) := by
      rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    rw [← hsq, Real.sqrt_sq (by positivity)]
  have hb := rarePsi_le_full_cost (twoAtomLaw ρ d₁ d₂) ρ hh
  rw [hcost, ← ENNReal.ofReal_mul hρ.le,
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.sqrt_eq_rpow,
    hroot, ← ENNReal.ofReal_mul hh.le] at hb
  convert hb using 1
  congr 1
  ring

theorem two_atom_sharpness : TwoAtomSharpnessStatement := by
  intro ρ B d₁ d₂ hρ hρ4 hB hgap hh
  change rarePsi (twoAtomLaw ρ d₁ d₂) ρ (1 / Real.sqrt B) = _ ∧
    quantileZero (twoAtomLaw ρ d₁ d₂) ρ B = _ ∧ _
  have hρ1 : ρ ≤ 1 := by linarith
  have hh0 : 0 < 1 / Real.sqrt B := by positivity
  have hratio : 1 < (1 - ρ) / ρ := (lt_div_iff₀ hρ).2 (by linarith)
  have hsqrt : 1 < Real.sqrt ((1 - ρ) / ρ) := by
    simpa using Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) hratio
  have hd : (d₁ : ℝ) < (d₂ : ℝ) := by rw [hgap]; nlinarith [d₁.2.1]
  have hbalance : (1 - ρ) / (d₂ : ℝ)^2 = ρ / (d₁ : ℝ)^2 := by
    rw [hgap, mul_pow, Real.sq_sqrt (by positivity)]
    field_simp [hρ.ne', d₁.2.1.ne', show 1 - ρ ≠ 0 by linarith]
  have := twoAtom_probability hρ.le hρ1 d₁ d₂
  have hQ := twoAtom_quantile hρ hρ1 hB d₁ d₂ hd hbalance hh
  have hupper := twoAtom_psi_upper hρ hρ1 hh0 d₁ d₂ hbalance
  have hprod : ENNReal.ofReal (Real.sqrt 2) *
      ENNReal.ofReal (Real.sqrt 2 * (1 / Real.sqrt B) * ρ / (d₁ : ℝ)) =
      ENNReal.ofReal (2 * (1 / Real.sqrt B) * ρ / (d₁ : ℝ)) := by
    rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    congr 1
    calc Real.sqrt 2 * (Real.sqrt 2 * (1 / Real.sqrt B) * ρ / (d₁ : ℝ)) =
        (Real.sqrt 2)^2 * ((1 / Real.sqrt B) * ρ / (d₁ : ℝ)) := by ring
      _ = _ := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; ring
  have hPsi : rarePsi (twoAtomLaw ρ d₁ d₂) ρ (1 / Real.sqrt B) =
      ENNReal.ofReal (Real.sqrt 2 * (1 / Real.sqrt B) * ρ / (d₁ : ℝ)) := by
    apply le_antisymm hupper
    apply (ENNReal.mul_le_mul_iff_right (by positivity : ENNReal.ofReal (Real.sqrt 2) ≠ 0)
      ENNReal.ofReal_ne_top).1
    rw [hprod, ← hQ]
    exact (psi_closed_form (twoAtomLaw ρ d₁ d₂) ρ B hρ hρ4 hB).1
  refine ⟨hPsi, hQ, ?_⟩
  change quantileZero (twoAtomLaw ρ d₁ d₂) ρ B =
    ENNReal.ofReal (Real.sqrt 2) * rarePsi (twoAtomLaw ρ d₁ d₂) ρ (1 / Real.sqrt B)
  rw [hQ, hPsi, hprod]

end ThresholdHC.PsiSharpness
