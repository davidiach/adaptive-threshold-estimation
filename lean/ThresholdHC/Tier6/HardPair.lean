import ThresholdHC.Tier6.HardPairModel

noncomputable section
open MeasureTheory

namespace ThresholdHC.Tier6

theorem measurable_clippedGap (h : ℝ) : Measurable (clippedGap h) :=
  measurable_const.min (measurable_const.div measurable_subtype_coe)

theorem clippedGap_nonneg {h : ℝ} (hh : 0 ≤ h) (d : Gap) : 0 ≤ clippedGap h d :=
  le_min (by norm_num) (div_nonneg hh d.property.1.le)

theorem clippedGap_le_one (h : ℝ) (d : Gap) : clippedGap h d ≤ 1 := min_le_left _ _

theorem clippedGap_pos {h : ℝ} (hh : 0 < h) (d : Gap) : 0 < clippedGap h d :=
  lt_min (by norm_num) (div_pos hh d.property.1)

theorem integrable_clippedGap (μ : Measure Gap) [IsFiniteMeasure μ]
    {h : ℝ} (hh : 0 ≤ h) : Integrable (clippedGap h) μ := by
  apply (integrable_const (1 : ℝ)).mono' (measurable_clippedGap h).aestronglyMeasurable
  filter_upwards [] with d
  rw [Real.norm_of_nonneg (clippedGap_nonneg hh d)]
  exact clippedGap_le_one h d

theorem modulus_nonneg (μ : Measure Gap) {h : ℝ} (hh : 0 ≤ h) : 0 ≤ modulus μ h :=
  integral_nonneg (fun d => clippedGap_nonneg hh d)

theorem modulus_le_one (μ : Measure Gap) [IsProbabilityMeasure μ]
    {h : ℝ} (hh : 0 ≤ h) : modulus μ h ≤ 1 := by
  calc
    modulus μ h ≤ ∫ _ : Gap, (1 : ℝ) ∂μ :=
      integral_mono (integrable_clippedGap μ hh) (integrable_const _) (clippedGap_le_one h)
    _ = 1 := by simp

theorem modulus_pos (μ : Measure Gap) [IsProbabilityMeasure μ]
    {h : ℝ} (hh : 0 < h) : 0 < modulus μ h := by
  apply (integral_pos_iff_support_of_nonneg
    (fun d => clippedGap_nonneg hh.le d) (integrable_clippedGap μ hh.le)).mpr
  have hs : Function.support (clippedGap h) = Set.univ := by
    ext d
    simp [Function.mem_support, ne_of_gt (clippedGap_pos hh d)]
  rw [hs]
  simp

theorem measurable_hardEta (h : ℝ) : Measurable (hardEta h) :=
  measurable_const.mul (measurable_clippedGap h)

theorem measurable_hardPlus (h : ℝ) : Measurable (hardPlus h) :=
  measurable_const.add (measurable_hardEta h)

theorem measurable_hardMinus (h : ℝ) : Measurable (hardMinus h) :=
  measurable_const.sub (measurable_hardEta h)

theorem hardEta_bounds {h : ℝ} (hh : 0 ≤ h) (d : Gap) :
    0 ≤ hardEta h d ∧ hardEta h d ≤ 1/8 := by
  have hc0 := clippedGap_nonneg hh d
  have hc1 := clippedGap_le_one h d
  dsimp [hardEta]
  constructor <;> nlinarith

theorem gap_mul_hardEta_le {h : ℝ} (d : Gap) : (d : ℝ) * hardEta h d ≤ h/8 := by
  have hc : clippedGap h d ≤ h/(d : ℝ) := min_le_right _ _
  have hm := mul_le_mul_of_nonneg_left hc d.property.1.le
  have hd : (d : ℝ) ≠ 0 := ne_of_gt d.property.1
  rw [mul_div_cancel₀ _ hd] at hm
  dsimp [hardEta]
  nlinarith

theorem hard_pair_validity : HardPairValidityStatement := by
  intro h hh
  refine ⟨measurable_hardEta h, measurable_hardPlus h, measurable_hardMinus h, ?_⟩
  intro d
  have he := hardEta_bounds hh.le d
  refine ⟨he, gap_mul_hardEta_le d, ?_, ?_⟩
  · dsimp [hardPlus]
    constructor <;> linarith [he.1, he.2]
  · dsimp [hardMinus]
    constructor <;> linarith [he.1, he.2]

theorem integrable_hardEta (μ : Measure Gap) [IsFiniteMeasure μ]
    {h : ℝ} (hh : 0 ≤ h) : Integrable (hardEta h) μ :=
  (integrable_clippedGap μ hh).const_mul _

theorem integrable_hardPlus (μ : Measure Gap) [IsFiniteMeasure μ]
    {h : ℝ} (hh : 0 ≤ h) : Integrable (hardPlus h) μ :=
  (integrable_const _).add (integrable_hardEta μ hh)

theorem integrable_hardMinus (μ : Measure Gap) [IsFiniteMeasure μ]
    {h : ℝ} (hh : 0 ≤ h) : Integrable (hardMinus h) μ :=
  (integrable_const _).sub (integrable_hardEta μ hh)

theorem hard_pair_separation : HardPairSeparationStatement := by
  intro μ _ h hh
  unfold signMean hardPlus hardMinus
  rw [integral_add (integrable_const _) (integrable_hardEta μ hh.le),
    integral_sub (integrable_const _) (integrable_hardEta μ hh.le)]
  simp only [hardEta, integral_const_mul]
  change _ = (1/4) * ∫ d, clippedGap h d ∂μ
  ring

theorem clippedGap_scaling (c h : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) (d : Gap) :
    c * clippedGap h d ≤ clippedGap (c*h) d := by
  apply le_min
  · exact (mul_le_mul_of_nonneg_left (clippedGap_le_one h d) hc).trans (by simpa using hc1)
  · simpa only [clippedGap, mul_div_assoc] using
      mul_le_mul_of_nonneg_left (min_le_right (1 : ℝ) (h/(d : ℝ))) hc

theorem modulus_scaling : ModulusScalingStatement := by
  intro μ _ c h hc hc1 hh
  unfold modulus
  rw [← integral_const_mul]
  exact integral_mono ((integrable_clippedGap μ hh).const_mul c)
    (integrable_clippedGap μ (mul_nonneg hc hh)) (clippedGap_scaling c h hc hc1)

theorem budgetScale_pos {B : ℝ} (hB : 0 < B) : 0 < budgetScale B := by
  unfold budgetScale
  positivity

theorem budgetScale_square {B : ℝ} (hB : 0 < B) : (budgetScale B)^2 * B = 1/16 := by
  have hs : Real.sqrt B ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hB)
  have hsq := Real.sq_sqrt hB.le
  unfold budgetScale
  field_simp
  nlinarith

theorem budget_hard_pair : BudgetHardPairStatement := by
  intro μ _ B hB
  have hB0 : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hb := budgetScale_pos hB0
  refine ⟨hb, budgetScale_square hB0, ?_⟩
  rw [hard_pair_separation μ (budgetScale B) hb]
  have hs : 0 ≤ 1 / Real.sqrt B := by positivity
  have hscale := modulus_scaling μ (1/4) (1/Real.sqrt B) (by norm_num) (by norm_num) hs
  have heq : (1/4:ℝ) * (1/Real.sqrt B) = budgetScale B := by unfold budgetScale; ring
  rw [heq] at hscale
  linarith

end ThresholdHC.Tier6
