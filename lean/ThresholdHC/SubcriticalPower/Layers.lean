import ThresholdHC.EntropyTailQuantile.QuantileTailBound
import ThresholdHC.RareAboveTwo.PowerLaw
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section
open MeasureTheory Set Real Filter
open scoped ENNReal
namespace ThresholdHC.SubcriticalPower
open ThresholdHC.Tier6 ThresholdHC.EntropyTailQuantile ThresholdHC.RareAboveTwo

/-- The fractional lower-quantile measure has the reference CDF clipped
at its total mass. This identity also covers an atom at the threshold. -/
theorem quantile_cdf (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ : ℝ} (hr : 0 < ρ) (hu : ρ ≤ 1) (x : ℝ) :
    (quantileTail μ ρ).real {d : Gap | (d:ℝ) ≤ x} = min ρ (μ.real {d : Gap | (d:ℝ) ≤ x}) := by
  let t := quantileThreshold μ ρ
  let S := {d : Gap | (d:ℝ) ≤ x}
  have hm : MeasurableSet S := measurableSet_le measurable_subtype_coe measurable_const
  have hp := quantileThreshold_properties μ hr hu
  by_cases hx : x < t
  · rw [min_eq_right (hp.2.2.2 x hx).le]
    have hsub : S ∩ {d : Gap | (d:ℝ) < t} = S := inter_eq_left.mpr (fun _ hd => lt_of_le_of_lt hd hx)
    have hem : S ∩ {d : Gap | (d:ℝ) = t} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro d ⟨h₁,h₂⟩
      exact (ne_of_lt (lt_of_le_of_lt h₁ hx)) h₂
    change ((quantileTail μ ρ) S).toReal = (μ S).toReal
    simp only [quantileTail,Measure.add_apply,Measure.smul_apply,Measure.restrict_apply hm]
    change (μ (S ∩ {d : Gap | (d:ℝ) < t}) + ENNReal.ofReal (quantileBoundaryFraction μ ρ) *
      μ (S ∩ {d : Gap | (d:ℝ) = t})).toReal = _
    rw [hsub,hem,measure_empty,mul_zero,add_zero]
  · have hx' : t ≤ x := le_of_not_gt hx
    have hs : ρ ≤ μ.real S := hp.2.2.1.trans (measureReal_mono (fun _ hd => le_trans hd hx'))
    rw [min_eq_left hs]
    calc _ = (quantileTail μ ρ).real univ := by
               apply measureReal_congr
               filter_upwards [quantileTail_support μ ρ] with d hd
               exact propext ⟨fun _ => mem_univ _,fun _ => le_trans hd hx'⟩
         _ = ρ := quantileTail_real_mass μ hr hu

/-- Layer-cake representation on a bounded interval. The closed inequality
in the CDF makes the identity usable without a continuity hypothesis. -/
theorem tail_layers (ν : Measure Gap) [IsFiniteMeasure ν] {h : ℝ} (hh : 0 ≤ h) :
    tailModulus ν h = ∫ t in (0:ℝ)..1, ν.real {d : Gap | (d:ℝ) ≤ h/t} := by
  let F (t : ℝ) := ν.real {d : Gap | (d:ℝ) ≤ h/t}
  let S : Set ℝ := Ioc 0 1
  have hs : MeasurableSet S := measurableSet_Ioc
  rw [tailModulus,(tailKernel_integrable ν hh).integral_eq_integral_meas_le (ae_of_all ν (tailKernel_nonneg hh)),
    intervalIntegral.integral_of_le zero_le_one]
  calc _ = ∫ t in Ioi (0:ℝ), S.indicator F t := by
             apply integral_congr_ae
             filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht
             have ht' : 0 < t := ht
             by_cases hu : t ≤ 1
             · rw [indicator_of_mem (show t ∈ S from ⟨ht',hu⟩)]
               apply congrArg ν.real
               ext d
               simp only [mem_ofPred_eq,le_min_iff,hu,true_and,le_div_iff₀ d.property.1,le_div_iff₀ ht',mul_comm]
             · rw [indicator_of_notMem (show t ∉ S from fun ht => hu ht.2)]
               have hem : {d : Gap | t ≤ min 1 (h/(d:ℝ))} = ∅ :=
                 eq_empty_iff_forall_notMem.mpr (fun d hd => hu (le_trans hd (min_le_left _ _)))
               rw [hem,measureReal_empty]
       _ = _ := by
         rw [integral_indicator hs,Measure.restrict_restrict hs,inter_eq_left.mpr (show S ⊆ Ioi 0 from fun _ hd => hd.1)]

theorem mass_le_tail (ν : Measure Gap) [IsFiniteMeasure ν] {h : ℝ} (hh : 0 ≤ h) :
    ν.real {d : Gap | (d:ℝ) ≤ h} ≤ tailModulus ν h := by
  let S := {d : Gap | (d:ℝ) ≤ h}
  have hm : MeasurableSet S := measurableSet_le measurable_subtype_coe measurable_const
  have he : (∫ d : Gap, S.indicator (fun _ => (1:ℝ)) d ∂ν) = ν.real S := by
    rw [integral_indicator hm,setIntegral_const]; simp
  rw [← he,tailModulus]
  apply integral_mono ((integrable_const _).indicator hm) (tailKernel_integrable ν hh)
  intro d
  by_cases hd : d ∈ S
  · rw [indicator_of_mem hd]
    exact le_min le_rfl ((one_le_div d.property.1).mpr hd)
  · rw [indicator_of_notMem hd]; exact tailKernel_nonneg hh d

end ThresholdHC.SubcriticalPower
