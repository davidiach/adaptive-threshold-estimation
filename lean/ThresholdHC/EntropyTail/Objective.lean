import ThresholdHC.EntropyTail.Gamma

/-! The truncated inverse-gap cost, the objective at the two extreme selections,
and a uniform positive lower bound for the objective. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.EntropyTail
open ThresholdHC.Tier6

theorem tailCost_zero (h : ℝ) : tailCost 0 h = 0 := by simp [tailCost]

theorem tailCost_sub_add {μ σ : Measure Gap} [IsFiniteMeasure σ] (hσ : σ ≤ μ) (h : ℝ) :
    tailCost (μ - σ) h + tailCost σ h = tailCost μ h := by
  unfold tailCost
  rw [← lintegral_add_measure, Measure.sub_add_cancel_of_le hσ]

theorem tailCost_smul (c : ℝ≥0∞) (τ : Measure Gap) (h : ℝ) :
    tailCost (c • τ) h = c * tailCost τ h := by
  unfold tailCost
  rw [lintegral_smul_measure, smul_eq_mul]

theorem tailCost_dirac (d : Gap) (h : ℝ) :
    tailCost (Measure.dirac d) h = ENNReal.ofReal (min 1 (h / (d : ℝ))) := by
  unfold tailCost
  exact lintegral_dirac _ _

/-- Since `d ≤ 1/2`, every magnitude costs at least `min{1,2h}`. -/
theorem tailCost_lower (τ : Measure Gap) {h : ℝ} (hh : 0 ≤ h) :
    ENNReal.ofReal (min 1 (2 * h)) * τ Set.univ ≤ tailCost τ h := by
  unfold tailCost
  rw [← lintegral_const]
  refine lintegral_mono fun d => ENNReal.ofReal_le_ofReal ?_
  have hd := d.2
  refine min_le_min_left 1 ?_
  rw [le_div_iff₀ hd.1]
  nlinarith

theorem entropyTerm_ofReal {h ρ g : ℝ} (hh : 0 ≤ h) (hρ : 0 ≤ ρ) (hg : 0 ≤ g) :
    ENNReal.ofReal h * (ENNReal.ofReal ρ * ENNReal.ofReal g) ^ (1/2 : ℝ) =
      ENNReal.ofReal (h * Real.sqrt (ρ * g)) := by
  rw [← ENNReal.ofReal_mul hρ, ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hρ hg) (by norm_num),
    ← Real.sqrt_eq_rpow, ← ENNReal.ofReal_mul hh]

theorem selectionObjective_zero (μ : Measure Gap) (ρ B : ℝ) :
    selectionObjective μ ρ B 0 = tailCost μ (1 / Real.sqrt B) := by
  unfold selectionObjective
  rw [gamma_zero, mul_zero, ENNReal.zero_rpow_of_pos (by norm_num), mul_zero, zero_add,
    Measure.sub_zero]

theorem selectionObjective_self (μ : Measure Gap) (ρ B : ℝ) :
    selectionObjective μ ρ B μ =
      ENNReal.ofReal (1 / Real.sqrt B) * (ENNReal.ofReal ρ * gamma μ) ^ (1/2 : ℝ) := by
  unfold selectionObjective
  rw [Measure.sub_self, tailCost_zero, add_zero]

theorem selection_le_rho (μ : Measure Gap) (ρ B : ℝ) : selection μ ρ B ≤ ENNReal.ofReal ρ :=
  min_le_left _ _

theorem selection_le_objective {μ σ : Measure Gap} (hσ : σ ≤ μ) (ρ B : ℝ) :
    selection μ ρ B ≤ selectionObjective μ ρ B σ :=
  (min_le_right _ _).trans (iInf₂_le σ hσ)

/-- Every admissible objective is at least `min{2h√ρ, min{1,2h}}`, `h = B^{-1/2}`. -/
theorem objective_lower {μ σ : Measure Gap} [IsProbabilityMeasure μ] (hσ : σ ≤ μ)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (B : ℝ) :
    ENNReal.ofReal (min (2 * (1 / Real.sqrt B) * Real.sqrt ρ) (min 1 (2 * (1 / Real.sqrt B)))) ≤
      selectionObjective μ ρ B σ := by
  have hh : 0 ≤ 1 / Real.sqrt B := by positivity
  have : IsFiniteMeasure σ := isFiniteMeasure_of_le μ hσ
  have hm0 : 0 ≤ min 1 (2 * (1 / Real.sqrt B)) := le_min zero_le_one (by linarith)
  have hsσ : σ Set.univ = ENNReal.ofReal (σ Set.univ).toReal :=
    (ENNReal.ofReal_toReal (measure_ne_top σ _)).symm
  have hs1 : σ Set.univ ≤ 1 := (Measure.le_iff'.1 hσ Set.univ).trans (le_of_eq measure_univ)
  have hs0 : 0 ≤ (σ Set.univ).toReal := ENNReal.toReal_nonneg
  have hs1' : (σ Set.univ).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top hs1
  generalize (σ Set.univ).toReal = s at hsσ hs0 hs1'
  have hg : ENNReal.ofReal (4 * s) ≤ gamma σ := by
    rw [ENNReal.ofReal_mul (by norm_num), ← hsσ]
    simpa using four_mass_le_gamma σ
  have hent : ENNReal.ofReal (1 / Real.sqrt B * Real.sqrt (ρ * (4 * s))) ≤
      ENNReal.ofReal (1 / Real.sqrt B) * (ENNReal.ofReal ρ * gamma σ) ^ (1/2 : ℝ) := by
    rw [← entropyTerm_ofReal (g := 4 * s) hh hρ (mul_nonneg (by norm_num) hs0)]
    gcongr
  have htail : ENNReal.ofReal (min 1 (2 * (1 / Real.sqrt B)) * (1 - s)) ≤
      tailCost (μ - σ) (1 / Real.sqrt B) := by
    have hmass : (μ - σ) Set.univ = ENNReal.ofReal (1 - s) := by
      rw [Measure.sub_apply MeasurableSet.univ hσ, measure_univ, hsσ, ENNReal.ofReal_sub _ hs0,
        ENNReal.ofReal_one]
    rw [ENNReal.ofReal_mul hm0, ← hmass]
    exact tailCost_lower (μ - σ) hh
  have hreal : min (2 * (1 / Real.sqrt B) * Real.sqrt ρ) (min 1 (2 * (1 / Real.sqrt B))) ≤
      1 / Real.sqrt B * Real.sqrt (ρ * (4 * s)) + min 1 (2 * (1 / Real.sqrt B)) * (1 - s) := by
    have hsq : Real.sqrt (ρ * (4 * s)) = 2 * Real.sqrt ρ * Real.sqrt s := by
      rw [show ρ * (4 * s) = (2:ℝ)^2 * ρ * s by ring,
        Real.sqrt_mul (show (0:ℝ) ≤ 2^2 * ρ by positivity) s,
        Real.sqrt_mul (show (0:ℝ) ≤ 2^2 by norm_num) ρ, Real.sqrt_sq (by norm_num)]
    have hss : s ≤ Real.sqrt s := by
      have h1 := Real.sqrt_le_sqrt hs1'
      rw [Real.sqrt_one] at h1
      nlinarith [Real.mul_self_sqrt hs0, Real.sqrt_nonneg s]
    rw [hsq]
    have h1 := min_le_left (2 * (1 / Real.sqrt B) * Real.sqrt ρ) (min 1 (2 * (1 / Real.sqrt B)))
    have h2 := min_le_right (2 * (1 / Real.sqrt B) * Real.sqrt ρ) (min 1 (2 * (1 / Real.sqrt B)))
    have hp : 0 ≤ 2 * (1 / Real.sqrt B) * Real.sqrt ρ := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hss hp, mul_nonneg (sub_nonneg.2 h1) hs0,
      mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 hs1')]
  calc ENNReal.ofReal (min (2 * (1 / Real.sqrt B) * Real.sqrt ρ) (min 1 (2 * (1 / Real.sqrt B))))
      ≤ ENNReal.ofReal (1 / Real.sqrt B * Real.sqrt (ρ * (4 * s)) +
          min 1 (2 * (1 / Real.sqrt B)) * (1 - s)) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (1 / Real.sqrt B * Real.sqrt (ρ * (4 * s))) +
          ENNReal.ofReal (min 1 (2 * (1 / Real.sqrt B)) * (1 - s)) :=
        ENNReal.ofReal_add (mul_nonneg hh (Real.sqrt_nonneg _))
          (mul_nonneg hm0 (by linarith))
    _ ≤ selectionObjective μ ρ B σ := add_le_add hent htail

theorem iInf_objective_lower (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 ≤ ρ)
    (B : ℝ) :
    ENNReal.ofReal (min (2 * (1 / Real.sqrt B) * Real.sqrt ρ) (min 1 (2 * (1 / Real.sqrt B)))) ≤
      ⨅ (σ : Measure Gap) (_ : σ ≤ μ), selectionObjective μ ρ B σ :=
  le_iInf₂ fun _ hσ => objective_lower hσ hρ B

end ThresholdHC.EntropyTail
