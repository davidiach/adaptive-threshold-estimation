import ThresholdHC.Tier6.HardPair
import Mathlib.MeasureTheory.Integral.Layercake

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal
namespace ThresholdHC.Envelope
open ThresholdHC.Tier6

/-- A law in the envelope has at most the reference mass at every small-gap cutoff. -/
def Within (μ ν : Measure Gap) : Prop :=
  ∀ t : ℝ, 0 < t → ν {d | (d:ℝ) ≤ t} ≤ μ {d | (d:ℝ) ≤ t}

theorem within_self (μ : Measure Gap) : Within μ μ := fun _ _ => le_rfl

private theorem compare_layers (μ ν : Measure Gap) (f : Gap → ℝ)
    (hm : Measurable f) (hn : ∀ d, 0 ≤ f d)
    (h : ∀ t : ℝ, 0 < t → ν {d | t ≤ f d} ≤ μ {d | t ≤ f d}) :
    (∫⁻ d, ENNReal.ofReal (f d) ∂ν) ≤ ∫⁻ d, ENNReal.ofReal (f d) ∂μ := by
  rw [lintegral_eq_lintegral_meas_le ν (ae_of_all _ hn) hm.aemeasurable,
    lintegral_eq_lintegral_meas_le μ (ae_of_all _ hn) hm.aemeasurable]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := (0:ℝ)))] with t ht using h t ht

private theorem compare_integrals (μ ν : Measure Gap) (f : Gap → ℝ)
    (hm : Measurable f) (hn : ∀ d, 0 ≤ f d) (hi : Integrable f μ)
    (he : (∫⁻ d, ENNReal.ofReal (f d) ∂ν) ≤ ∫⁻ d, ENNReal.ofReal (f d) ∂μ) :
    Integrable f ν ∧ (∫ d, f d ∂ν) ≤ ∫ d, f d ∂μ := by
  have hf := (hasFiniteIntegral_iff_ofReal (ae_of_all μ hn)).mp hi.hasFiniteIntegral
  refine ⟨⟨hm.aestronglyMeasurable,(hasFiniteIntegral_iff_ofReal (ae_of_all ν hn)).mpr (he.trans_lt hf)⟩,?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all ν hn) hm.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all μ hn) hm.aestronglyMeasurable]
  exact ENNReal.toReal_mono hf.ne he

theorem modulus_le (μ ν : Measure Gap) [IsProbabilityMeasure μ] (h : Within μ ν)
    {a : ℝ} (ha : 0 < a) : modulus ν a ≤ modulus μ a := by
  have hm := measurable_clippedGap a
  have hn := clippedGap_nonneg ha.le
  have hi : Integrable (clippedGap a) μ :=
    (integrable_const (1:ℝ)).mono' hm.aestronglyMeasurable
      (ae_of_all _ (fun d => by simpa only [Real.norm_eq_abs,abs_of_nonneg (hn d)] using clippedGap_le_one a d))
  apply (compare_integrals μ ν _ hm hn hi (compare_layers μ ν _ hm hn ?_)).2
  intro t ht
  by_cases ht1 : t ≤ 1
  · have he : {d : Gap | t ≤ clippedGap a d} = {d : Gap | (d:ℝ) ≤ a/t} := by
      ext d
      simp only [Set.mem_ofPred_eq,clippedGap,le_min_iff,ht1,true_and,le_div_iff₀ ht,le_div_iff₀ d.property.1,mul_comm]
    rw [he]
    exact h _ (div_pos ha ht)
  · have he : {d : Gap | t ≤ clippedGap a d} = ∅ := Set.eq_empty_iff_forall_notMem.mpr
      (fun d hd => ht1 (hd.trans (clippedGap_le_one a d)))
    simp [he]

theorem inverse_moment_le (μ ν : Measure Gap) (h : Within μ ν)
    (hi : Integrable (fun d : Gap => (d:ℝ)⁻¹) μ) :
    Integrable (fun d : Gap => (d:ℝ)⁻¹) ν ∧ (∫ d : Gap, (d:ℝ)⁻¹ ∂ν) ≤ ∫ d : Gap, (d:ℝ)⁻¹ ∂μ := by
  have hm : Measurable (fun d : Gap => (d:ℝ)⁻¹) := measurable_subtype_coe.inv
  have hn (d : Gap) : 0 ≤ (d:ℝ)⁻¹ := inv_nonneg.mpr d.property.1.le
  apply compare_integrals μ ν _ hm hn hi (compare_layers μ ν _ hm hn ?_)
  intro t ht
  have he : {d : Gap | t ≤ (d:ℝ)⁻¹} = {d : Gap | (d:ℝ) ≤ 1/t} := by
    ext d
    simp only [Set.mem_ofPred_eq,← one_div,le_div_iff₀ ht,le_div_iff₀ d.property.1,mul_comm]
  rw [he]
  exact h _ (one_div_pos.mpr ht)

end ThresholdHC.Envelope
