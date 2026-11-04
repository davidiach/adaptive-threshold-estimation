import ThresholdHC.SmoothDensity.Representation
import ThresholdHC.Envelope.Minimax
import ThresholdHC.RareAboveTwo.PowerLaw
import ThresholdHC.SubcriticalPower.Layers
import ThresholdHC.Proofs.Modulus

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThresholdHC.SmoothDensity
open ThresholdHC.Tier6 ThresholdHC.Confidence ThresholdHC.RareAboveTwo
open ThresholdHC.EntropyTailQuantile ThresholdHC.SubcriticalPower

theorem smoothModel_cdf {s : ℕ} {M : ℝ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (h : SmoothModel s M μ q) {x : ℝ} (hx : 0 ≤ x) :
    μ.real {d : Gap | (d : ℝ) ≤ x} ≤ 2 * M * x := by
  obtain ⟨f,hf,hn,hs,_,hb,hr⟩ := h
  have hsup (p : ℝ) : f p ≤ M := (le_abs_self _).trans (by simpa using hb 0 (Nat.zero_le s) p)
  have hc : HasCompactSupport f := HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (fun p hp => by
      by_contra h
      exact hp (hs p h))
  have hi : Integrable f volume := hf.continuous.integrable_of_hasCompactSupport hc
  let S : Set ℝ := {p | |p - 1 / 2| ≤ x}
  have hS : S = Icc (1 / 2 - x) (1 / 2 + x) := by
    ext p
    simp only [S,mem_ofPred_eq,abs_le,mem_Icc]
    constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
  let F := S.indicator (fun _ => (1 : ℝ))
  have hF : Measurable F := measurable_const.indicator (hS ▸ measurableSet_Icc)
  have hbound (p : ℝ) : |F p| ≤ 1 := by by_cases hp : p ∈ S <;> simp [F,hp]
  have he := hr F hF ⟨1,hbound⟩
  have hpair (d : Gap) : q.val d * F (1 / 2 + (d : ℝ)) +
      (1 - q.val d) * F (1 / 2 - (d : ℝ)) = if (d : ℝ) ≤ x then 1 else 0 := by
    have hp : |(1 / 2 : ℝ) + d - 1 / 2| = (d : ℝ) := by
      rw [add_sub_cancel_left, abs_of_pos d.property.1]
    have hm : |(1 / 2 : ℝ) - d - 1 / 2| = (d : ℝ) := by
      rw [show (1 / 2 : ℝ) - d - 1 / 2 = -(d : ℝ) by ring,abs_neg,abs_of_pos d.property.1]
    simp only [F,S,Set.indicator,mem_ofPred_eq,hp,hm]
    split_ifs <;> ring
  simp_rw [hpair] at he
  have hleft : (∫ d : Gap, if (d : ℝ) ≤ x then (1 : ℝ) else 0 ∂μ) =
      μ.real {d : Gap | (d : ℝ) ≤ x} := by
    change (∫ d, {d : Gap | (d : ℝ) ≤ x}.indicator (fun _ => (1 : ℝ)) d ∂μ) = _
    rw [integral_indicator (measurableSet_le measurable_subtype_coe measurable_const)]
    simp
  rw [hleft] at he
  have hright : (fun p => f p * F p) = S.indicator f := by
    funext p
    by_cases hp : p ∈ S <;> simp [F,hp]
  rw [hright,integral_indicator (hS ▸ measurableSet_Icc),hS] at he
  rw [he]
  calc
    _ ≤ ∫ p in Icc (1 / 2 - x) (1 / 2 + x), M := by
      apply integral_mono_ae hi.integrableOn
        (integrableOn_const (hs := by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
      exact ae_of_all _ hsup
    _ = _ := by
      simp [measureReal_def,Real.volume_Icc]
      rw [ENNReal.toReal_ofReal (add_nonneg hx hx)]
      ring

theorem smoothModel_envelope {s : ℕ} {M : ℝ} (hM : 1 ≤ M)
    (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (h : SmoothModel s M μ q) :
    ThresholdHC.Envelope.Within
      (powerGapLaw 1 (1 / (2 * M)) (by norm_num) (by positivity) (by
        apply (div_le_iff₀ (by positivity : 0 < 2 * M)).mpr
        linarith)) μ := by
  intro x hx
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change μ.real {d : Gap | (d : ℝ) ≤ x} ≤
    (powerGapLaw 1 (1 / (2 * M)) _ _ _).real {d : Gap | (d : ℝ) ≤ x}
  rw [powerGapLaw_cdf _ _ _ _ _ x hx,Real.rpow_one]
  apply le_min measureReal_le_one
  convert smoothModel_cdf μ q h hx.le using 1
  field_simp

/-- The reference linear law's clipped modulus has the explicit logarithmic form. -/
theorem linear_modulus (a h : ℝ) (ha : 0 < a) (ha1 : a ≤ 1 / 2)
    (hh : 0 < h) (hh1 : h < a) :
    modulus (powerGapLaw 1 a (by norm_num) ha ha1) h =
      (h / a) * (1 + Real.log (a / h)) := by
  let μ := powerGapLaw 1 a (by norm_num) ha ha1
  change tailModulus μ h = _
  rw [tail_layers μ hh.le]
  have he : (∫ t in (0 : ℝ)..1, μ.real {d : Gap | (d : ℝ) ≤ h / t}) =
      ∫ t in (0 : ℝ)..1, min 1 ((h / a) / t) := by
    apply intervalIntegral.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro t ht
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    rw [powerGapLaw_cdf _ _ _ _ _ _ (div_pos hh ht.1),Real.rpow_one]
    congr 1
    ring
  rw [he,ThresholdHC.Proofs.power_modulus_critical (h / a)
    (div_pos hh ha) ((div_lt_one ha).mpr hh1)]
  rw [show a / h = (h / a)⁻¹ by simp,Real.log_inv]
  ring

end ThresholdHC.SmoothDensity
