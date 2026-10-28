import ThresholdHC.UnbiasedConverse.CreationInformation
import ThresholdHC.Tier6.Full

noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal
namespace ThresholdHC.UnbiasedConverse
open ThresholdHC ThresholdHC.Proofs ThresholdHC.Proofs.Transcript
open ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.Tier6

def tiltCoefficient (h e : ℝ) : ℝ := 32*(h*e)^2/(1-4*e^2)^2

theorem tilt_denominator_pos {e : ℝ} (he : 0 ≤ e) (he1 : e ≤ 1/8) :
    0 < 1-4*e^2 := by nlinarith

theorem local_tilt_information {d η h e A B : ℝ}
    (hd : 0 < d) (hd1 : d ≤ 1/2) (hη : 0 ≤ η) (hηe : η ≤ e)
    (hh : 0 < h) (he : 0 ≤ e) (he1 : e ≤ 1/8) (hdη : d*η ≤ h*e)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (_hAB : 0 < A+B) :
    klB (mixPredict d (1/2+η) A B) (mixPredict d (1/2-η) A B) ≤ tiltCoefficient h e ∧
    klB (mixPredict d (1/2-η) A B) (mixPredict d (1/2+η) A B) ≤ tiltCoefficient h e := by
  have hc : 0 ≤ tiltCoefficient h e := by unfold tiltCoefficient; positivity
  by_cases hAz : A = 0
  · simpa only [hAz, mixPredict_zero_left, klB_self] using And.intro hc hc
  by_cases hBz : B = 0
  · rw [hBz, mixPredict_zero_right (by linarith : (1/2:ℝ)+η ≠ 0) hAz,
      mixPredict_zero_right (by linarith : (1/2:ℝ)-η ≠ 0) hAz, klB_self]
    exact ⟨hc,hc⟩
  have hAp : 0 < A := lt_of_le_of_ne hA (Ne.symm hAz)
  have hBp : 0 < B := lt_of_le_of_ne hB (Ne.symm hBz)
  have heD := tilt_denominator_pos he he1
  have hηD := tilt_denominator_pos hη (hηe.trans he1)
  have hn : 32*d^2*η^2 ≤ 32*(h*e)^2 := by
    nlinarith [mul_self_le_mul_self (mul_nonneg hd.le hη) hdη]
  have hden : (1-4*e^2)^2 ≤ (1-4*η^2)^2 := by
    have hsq := mul_self_le_mul_self hη hηe
    nlinarith
  have hb : 32*d^2*η^2/(1-4*η^2)^2 ≤ tiltCoefficient h e := by
    calc
      _ ≤ 32*(h*e)^2/(1-4*η^2)^2 := div_le_div_of_nonneg_right hn (sq_nonneg _)
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos heD) hden
  rw [mixPredict_plus_ratio hBz, mixPredict_minus_ratio hBz]
  exact ⟨(lemmaA_forward d η (A/B) hd hd1 hη (by linarith) (div_pos hAp hBp)).trans hb,
    (lemmaA_reverse d η (A/B) hd hd1 hη (by linarith) (div_pos hAp hBp)).trans hb⟩

def tiltEta (h e : ℝ) (d : Gap) : ℝ := e * clippedGap h d

theorem measurable_tiltEta (h e : ℝ) : Measurable (tiltEta h e) :=
  measurable_const.mul (measurable_clippedGap h)

theorem tiltEta_bounds {h e : ℝ} (hh : 0 < h) (he : 0 ≤ e) (d : Gap) :
    0 ≤ tiltEta h e d ∧ tiltEta h e d ≤ e ∧ (d:ℝ)*tiltEta h e d ≤ h*e := by
  have h0 := clippedGap_nonneg hh.le d
  have h1 := clippedGap_le_one h d
  have h2 : (d:ℝ)*clippedGap h d ≤ h := by
    have hm := mul_le_mul_of_nonneg_left (min_le_right (1:ℝ) (h/(d:ℝ))) d.property.1.le
    simpa only [mul_div_cancel₀ _ d.property.1.ne', clippedGap] using hm
  dsimp only [tiltEta]
  exact ⟨mul_nonneg he h0, by nlinarith, by nlinarith [mul_le_mul_of_nonneg_right h2 he]⟩

def tiltPlus (h e : ℝ) (hh : 0 < h) (he : 0 ≤ e) (he1 : e ≤ 1/8) : SignLaw :=
  ⟨fun d => 1/2+tiltEta h e d, measurable_const.add (measurable_tiltEta h e), by
    intro d; have hb := tiltEta_bounds hh he d
    constructor <;> linarith [hb.1,hb.2.1]⟩

def tiltMinus (h e : ℝ) (hh : 0 < h) (he : 0 ≤ e) (he1 : e ≤ 1/8) : SignLaw :=
  ⟨fun d => 1/2-tiltEta h e d, measurable_const.sub (measurable_tiltEta h e), by
    intro d; have hb := tiltEta_bounds hh he d
    constructor <;> linarith [hb.1,hb.2.1]⟩

theorem tilt_mean_separation (μ : Measure Gap) [IsProbabilityMeasure μ]
    {h e : ℝ} (hh : 0 < h) (he : 0 ≤ e) (he1 : e ≤ 1/8) :
    signMean μ (tiltPlus h e hh he he1).val - signMean μ (tiltMinus h e hh he he1).val =
      2*e*modulus μ h := by
  have hi : Integrable (tiltEta h e) μ := (integrable_clippedGap μ hh.le).const_mul e
  unfold signMean tiltPlus tiltMinus
  rw [integral_add (integrable_const _) hi, integral_sub (integrable_const _) hi]
  simp only [tiltEta, integral_const_mul, modulus]
  ring

end ThresholdHC.UnbiasedConverse
