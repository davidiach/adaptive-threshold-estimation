import ThresholdHC.ArbitraryLawAdaptation.DominatedSelection

/-! The dominated-mass comparison, including unresolved mass at zero (A5). -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThresholdHC.ArbitraryLawAdaptation

theorem scaledSelection_residual {η σ : Measure ℝ} [IsFiniteMeasure η]
    (hσ : σ ≤ η) (c e : ℝ) :
    (ENNReal.ofReal c • η+ENNReal.ofReal e • Measure.dirac 0)-ENNReal.ofReal c • σ =
      ENNReal.ofReal c • (η-σ)+ENNReal.ofReal e • Measure.dirac 0 := by
  have : IsFiniteMeasure σ := isFiniteMeasure_of_le η hσ
  have : IsFiniteMeasure (ENNReal.ofReal c • σ) := σ.smul_finite ENNReal.ofReal_ne_top
  have he : (ENNReal.ofReal c • (η-σ)+ENNReal.ofReal e • Measure.dirac 0)+
      ENNReal.ofReal c • σ = ENNReal.ofReal c • η+ENNReal.ofReal e • Measure.dirac 0 := by
    calc
      _ = ENNReal.ofReal c • ((η-σ)+σ)+ENNReal.ofReal e • Measure.dirac 0 := by
        rw [smul_add]; ac_rfl
      _ = _ := by rw [Measure.sub_add_cancel_of_le hσ]
  rw [← he, Measure.add_sub_cancel]

theorem scaledSelection_objective {η σ : Measure ℝ} [IsFiniteMeasure η]
    (hσ : σ ≤ η) {c : ℝ} (hc : 1 ≤ c) (e ρ B : ℝ) :
    zeroObjective (ENNReal.ofReal c • η+ENNReal.ofReal e • Measure.dirac 0) ρ B
        (ENNReal.ofReal c • σ) ≤ ENNReal.ofReal c*zeroObjective η ρ B σ+ENNReal.ofReal e := by
  have : IsFiniteMeasure σ := isFiniteMeasure_of_le η hσ
  have hc0 : 0 ≤ c := le_trans zero_le_one hc
  have hroot : (ENNReal.ofReal c)^(1/2 : ℝ) ≤ ENNReal.ofReal c := by
    rw [ENNReal.ofReal_rpow_of_nonneg hc0 (by norm_num)]
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_self_of_one_le hc (by norm_num))
  unfold zeroObjective
  rw [zeroGamma_smul σ hc0, scaledSelection_residual hσ, zeroTailCost_add,
    zeroTailCost_smul, zeroTailCost_smul, zeroTailCost_dirac_zero, mul_one,
    mul_add, add_assoc]
  apply add_le_add _ le_rfl
  rw [mul_left_comm (ENNReal.ofReal ρ), ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  calc
    _ ≤ ENNReal.ofReal (1/Real.sqrt B) *
        (ENNReal.ofReal c*(ENNReal.ofReal ρ*zeroGamma σ)^(1/2 : ℝ)) :=
      mul_le_mul_right (mul_le_mul_left hroot _) _
    _ = _ := by ac_rfl

theorem zeroSelection_scaled_add_zero (η : Measure ℝ) [IsFiniteMeasure η]
    {c : ℝ} (hc : 1 ≤ c) (e ρ B : ℝ) :
    zeroSelection (ENNReal.ofReal c • η+ENNReal.ofReal e • Measure.dirac 0) ρ B ≤
      ENNReal.ofReal c*zeroSelection η ρ B+ENNReal.ofReal e := by
  have hcge : (1 : ℝ≥0∞) ≤ ENNReal.ofReal c := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hc
  have hcne := ne_of_gt (lt_of_lt_of_le zero_lt_one hcge)
  conv_rhs => rw [zeroSelection, mul_min, ← min_add_add_right]
  apply le_min
  · have hcap : ENNReal.ofReal ρ ≤ ENNReal.ofReal c*ENNReal.ofReal ρ := by
      simpa only [one_mul] using mul_le_mul_left hcge (ENNReal.ofReal ρ)
    exact (min_le_left _ _).trans (hcap.trans le_self_add)
  · rw [ENNReal.mul_iInf_of_ne hcne ENNReal.ofReal_ne_top, ENNReal.iInf_add]
    refine le_iInf fun σ => ?_
    rw [ENNReal.mul_iInf_of_ne hcne ENNReal.ofReal_ne_top, ENNReal.iInf_add]
    refine le_iInf fun hσ => ?_
    have hs : ENNReal.ofReal c • σ ≤ ENNReal.ofReal c • η+ENNReal.ofReal e • Measure.dirac 0 :=
      (smul_le_smul_left _ hσ).trans (by intro s; simp only [Measure.add_apply]; exact le_self_add)
    have hle : zeroSelection (ENNReal.ofReal c • η+ENNReal.ofReal e • Measure.dirac 0) ρ B ≤
        zeroObjective (ENNReal.ofReal c • η+ENNReal.ofReal e • Measure.dirac 0) ρ B
          (ENNReal.ofReal c • σ) :=
      (min_le_right _ _).trans (iInf₂_le (ENNReal.ofReal c • σ) hs)
    exact hle.trans (scaledSelection_objective hσ hc e ρ B)

/-- Dominated mass (A5). In fact, finite ambient measures suffice. -/
theorem zeroSelection_dominated_mass {ζ η : Measure ℝ} [IsFiniteMeasure η]
    {c e : ℝ} (hc : 1 ≤ c)
    (h : ζ ≤ ENNReal.ofReal c • η+ENNReal.ofReal e • Measure.dirac 0) (ρ B : ℝ) :
    zeroSelection ζ ρ B ≤ ENNReal.ofReal c*zeroSelection η ρ B+ENNReal.ofReal e := by
  have : IsFiniteMeasure (ENNReal.ofReal c • η) := η.smul_finite ENNReal.ofReal_ne_top
  have : IsFiniteMeasure (ENNReal.ofReal e • Measure.dirac (0 : ℝ)) :=
    (Measure.dirac (0 : ℝ)).smul_finite ENNReal.ofReal_ne_top
  exact (zeroSelection_mono h ρ B).trans (zeroSelection_scaled_add_zero η hc e ρ B)

end ThresholdHC.ArbitraryLawAdaptation
