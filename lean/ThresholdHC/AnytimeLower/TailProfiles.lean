import ThresholdHC.EntropyTailQuantile.TailModulus
import ThresholdHC.RareAboveTwo.Model

noncomputable section
open MeasureTheory Real Set
open scoped ENNReal
namespace ThresholdHC.AnytimeLower
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.EntropyTailQuantile

/-- The capped inverse-gap profile, restricted to a small-gap region. -/
def tailProfile (τ h : ℝ) (d : Gap) : ℝ :=
  if (d:ℝ) ≤ τ then min 1 (h/(d:ℝ)) else 0

theorem measurable_tailProfile (τ h : ℝ) : Measurable (tailProfile τ h) := by
  unfold tailProfile
  exact Measurable.ite (measurableSet_le measurable_subtype_coe measurable_const)
    (measurable_const.min (measurable_const.div measurable_subtype_coe)) measurable_const

theorem tailProfile_bounds (τ : ℝ) {h : ℝ} (hh : 0 ≤ h) (d : Gap) :
    0 ≤ tailProfile τ h d ∧ tailProfile τ h d ≤ 1 := by
  unfold tailProfile
  split_ifs
  · exact ⟨tailKernel_nonneg hh d,min_le_left _ _⟩
  · norm_num

theorem tailProfile_mono (τ : ℝ) {a b : ℝ} (hab : a ≤ b) (d : Gap) :
    tailProfile τ a d ≤ tailProfile τ b d := by
  unfold tailProfile
  split_ifs
  · exact min_le_min_left _ (div_le_div_of_nonneg_right hab d.property.1.le)
  · rfl

theorem tailProfile_weighted (τ : ℝ) {h : ℝ} (hh : 0 ≤ h) (d : Gap) :
    (d:ℝ)*tailProfile τ h d ≤ h := by
  unfold tailProfile
  split_ifs
  · have hm := (le_div_iff₀ d.property.1).mp (min_le_right (1:ℝ) (h/(d:ℝ)))
    simpa only [mul_comm] using hm
  · simpa using hh

theorem tailProfile_quarter (τ : ℝ) {h : ℝ} (_hh : 0 ≤ h) (d : Gap) :
    tailProfile τ h d/4 ≤ tailProfile τ (h/4) d := by
  unfold tailProfile
  split_ifs
  · apply le_min
    · have hm := min_le_left (1:ℝ) (h/(d:ℝ))
      linarith
    · have hm := min_le_right (1:ℝ) (h/(d:ℝ))
      have he : h/4/(d:ℝ) = (h/(d:ℝ))/4 := by ring
      rw [he]
      linarith
  · norm_num

theorem integrable_tailProfile (μ : Measure Gap) [IsFiniteMeasure μ]
    (τ : ℝ) {h : ℝ} (hh : 0 ≤ h) : Integrable (tailProfile τ h) μ := by
  apply (integrable_const (1:ℝ)).mono' (measurable_tailProfile τ h).aestronglyMeasurable
  exact ae_of_all _ (fun d => by
    rw [Real.norm_of_nonneg (tailProfile_bounds τ hh d).1]
    exact (tailProfile_bounds τ hh d).2)

def profileMass (μ : Measure Gap) (τ h : ℝ) : ℝ := ∫ d, tailProfile τ h d ∂μ

theorem profileMass_nonneg (μ : Measure Gap) (τ : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    0 ≤ profileMass μ τ h := integral_nonneg (fun d => (tailProfile_bounds τ hh d).1)

theorem profileMass_mono (μ : Measure Gap) [IsFiniteMeasure μ]
    (τ : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    profileMass μ τ a ≤ profileMass μ τ b :=
  integral_mono (integrable_tailProfile μ τ ha) (integrable_tailProfile μ τ (ha.trans hab))
    (tailProfile_mono τ hab)

theorem profileMass_quarter (μ : Measure Gap) [IsFiniteMeasure μ]
    (τ : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    profileMass μ τ h/4 ≤ profileMass μ τ (h/4) := by
  rw [profileMass,← integral_div]
  exact integral_mono ((integrable_tailProfile μ τ hh).div_const 4)
    (integrable_tailProfile μ τ (by positivity)) (tailProfile_quarter τ hh)

/-- The baseline is constant on the small-gap region and zero outside it. -/
def tailBase (τ : ℝ) : SignLaw :=
  ⟨fun d => if (d:ℝ) ≤ τ then (1/4:ℝ) else 0,
    Measurable.ite (measurableSet_le measurable_subtype_coe measurable_const) measurable_const measurable_const,
    fun d => by dsimp only; split_ifs <;> norm_num⟩

def tailAlternative (τ a b : ℝ) (hb : 0 ≤ b) (hab : b ≤ a) : SignLaw :=
  ⟨fun d => (tailBase τ).val d+(tailProfile τ a d-tailProfile τ b d)/32,
    (tailBase τ).property.1.add (((measurable_tailProfile τ a).sub (measurable_tailProfile τ b)).div_const 32),
    fun d => by
      have ha0 := tailProfile_bounds τ (hb.trans hab) d
      have hb0 := tailProfile_bounds τ hb d
      have hm := tailProfile_mono τ hab d
      dsimp only [tailBase]
      change 0 ≤ (if (d:ℝ) ≤ τ then (1/4:ℝ) else 0)+_ ∧
        (if (d:ℝ) ≤ τ then (1/4:ℝ) else 0)+(tailProfile τ a d-tailProfile τ b d)/32 ≤ 1
      split_ifs <;> constructor <;> linarith⟩

theorem tailAlternative_central (τ : ℝ) {a b : ℝ} (hb : 0 ≤ b) (hab : b ≤ a)
    (d : Gap) (hd : (d:ℝ) ≤ τ) :
    1/4 ≤ (tailAlternative τ a b hb hab).val d ∧
      (tailAlternative τ a b hb hab).val d ≤ 9/32 := by
  have ha0 := tailProfile_bounds τ (hb.trans hab) d
  have hb0 := tailProfile_bounds τ hb d
  have hm := tailProfile_mono τ hab d
  dsimp [tailAlternative,tailBase]
  rw [ite_eq_left hd]
  constructor <;> linarith

theorem tailAlternative_outside (τ : ℝ) {a b : ℝ} (hb : 0 ≤ b) (hab : b ≤ a)
    (d : Gap) (hd : ¬(d:ℝ) ≤ τ) :
    (tailAlternative τ a b hb hab).val d = 0 := by
  simp [tailAlternative,tailBase,tailProfile,hd]

theorem tailAlternative_contrast (τ : ℝ) {a b : ℝ} (hb : 0 ≤ b) (hab : b ≤ a)
    (d : Gap) :
    (d:ℝ)*|(tailAlternative τ a b hb hab).val d-(tailBase τ).val d| ≤ a/32 := by
  have hm := tailProfile_mono τ hab d
  have hz := (tailProfile_bounds τ hb d).1
  have hw := tailProfile_weighted τ (hb.trans hab) d
  change (d:ℝ)*|((tailBase τ).val d+_)-(tailBase τ).val d| ≤ _
  rw [add_sub_cancel_left,abs_of_nonneg (div_nonneg (sub_nonneg.mpr hm) (by norm_num))]
  have hd := mul_nonneg d.property.1.le hz
  nlinarith only [hw,hd]

theorem tailAlternative_mean (μ : Measure Gap) [IsFiniteMeasure μ]
    (τ : ℝ) {a b : ℝ} (hb : 0 ≤ b) (hab : b ≤ a) :
    signMean μ (tailAlternative τ a b hb hab).val-signMean μ (tailBase τ).val =
      (profileMass μ τ a-profileMass μ τ b)/32 := by
  have hbase : Integrable (tailBase τ).val μ := by
    apply (integrable_const (1:ℝ)).mono' (tailBase τ).property.1.aestronglyMeasurable
    exact ae_of_all _ (fun d => by
      rw [Real.norm_of_nonneg ((tailBase τ).property.2 d).1]
      exact ((tailBase τ).property.2 d).2)
  have hi : Integrable (fun d => tailProfile τ a d-tailProfile τ b d) μ :=
    (integrable_tailProfile μ τ (hb.trans hab)).sub (integrable_tailProfile μ τ hb)
  simp only [signMean,tailAlternative]
  rw [integral_add hbase (hi.div_const 32),add_sub_cancel_left,integral_div,
    integral_sub (integrable_tailProfile μ τ (hb.trans hab)) (integrable_tailProfile μ τ hb)]
  rfl

end ThresholdHC.AnytimeLower
