import ThresholdHC.Genie.UniformGapModel
import Mathlib.Analysis.SpecialFunctions.NonIntegrable

/-! The counterexample's latent divergence, and every positive-cap reveal
information ratio, are infinite. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.Genie
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.StoppingProgram
open ThresholdHC.CapIdentification

theorem uniformGap_inverse_not_integrable :
    ¬Integrable (fun d : Gap => ((1/2:ℝ)-d.val)⁻¹) uniformGapLaw := by
  intro h
  have h' : Integrable (fun d : Gap => ((1/2:ℝ)-d.val)⁻¹)
      (Measure.comap Subtype.val volume) :=
    (integrable_smul_measure (by norm_num : (2:ℝ≥0∞) ≠ 0) (by norm_num)).mp h
  have hi : IntegrableOn (fun x : ℝ => ((1/2:ℝ)-x)⁻¹) (Set.Ioc 0 (1/2)) volume :=
    (integrableOn_iff_comap_subtypeVal measurableSet_Ioc).mpr h'
  have hn : IntervalIntegrable (fun x : ℝ => (x-1/2)⁻¹) volume 0 (1/2) := by
    have hneg := hi.neg
    change IntegrableOn (fun x : ℝ => -((1/2:ℝ)-x)⁻¹) (Set.Ioc 0 (1/2)) volume at hneg
    have he : (fun x : ℝ => -((1/2:ℝ)-x)⁻¹) = (fun x => (x-1/2)⁻¹) := by
      funext x
      rw [←inv_neg,neg_sub]
    rw [he] at hneg
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr hneg
  simpa using hn

theorem singularExample_latentDivergence : latentDivergence uniformGapLaw singularExamplePriors = ⊤ := by
  by_contra hC
  have hbound : (∫⁻ d : Gap, ENNReal.ofReal (((1/2:ℝ)-d.val)⁻¹) ∂uniformGapLaw) ≤
      16*latentDivergence uniformGapLaw singularExamplePriors := by
    rw [latentDivergence,←lintegral_const_mul' _ _ (by norm_num : (16:ℝ≥0∞) ≠ ⊤)]
    apply lintegral_mono
    intro d
    change ENNReal.ofReal (((1/2:ℝ)-d.val)⁻¹) ≤
      16*(perspective (1/4-0) (1/2-d.val)+perspective (1/4-0) (1-(1/2-d.val)))
    by_cases hd : d.val = 1/2
    · simp [hd,perspective]
    have hp : 0 < (1/2:ℝ)-d.val := by
      by_contra hp
      apply hd
      linarith [d.property.2]
    calc
      _ = 16*perspective (1/4-0) (1/2-d.val) := by
        rw [perspective_pos hp,←ENNReal.ofReal_ofNat 16,←ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 16)]
        congr 1
        ring
      _ ≤ _ := mul_le_mul_right (le_add_right le_rfl) _
  have hf : (∫⁻ d : Gap, ENNReal.ofReal (((1/2:ℝ)-d.val)⁻¹) ∂uniformGapLaw) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (by norm_num) hC) hbound
  apply uniformGap_inverse_not_integrable
  apply (lintegral_ofReal_ne_top_iff_integrable ?_ ?_).mp hf
  · exact (measurable_const.sub measurable_subtype_coe).inv.aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun d => inv_nonneg.mpr (sub_nonneg.mpr d.property.2))

theorem singularExample_genie_top (N : ℕ) (hN : 0 < N) :
    genieInformationRatio uniformGapLaw N singularExamplePriors = ⊤ :=
  (genieInformationRatio_top_iff uniformGapLaw N hN singularExamplePriors).mpr singularExample_latentDivergence

end ThresholdHC.Genie
