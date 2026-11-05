import ThresholdHC.QuantileOptimality.AtomicCost

noncomputable section
open MeasureTheory Real Set
open scoped ENNReal BigOperators Classical
namespace ThresholdHC.QuantileOptimality
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTailQuantile

theorem quantileThreshold_at_min_atom (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (d : Gap)
    (hs : ∀ᵐ x : Gap ∂μ, (d : ℝ) ≤ (x : ℝ)) (hm : ρ ≤ μ.real {d}) :
    quantileThreshold μ ρ=(d : ℝ) := by
  have hp := quantileThreshold_properties μ hρ hρ1
  have hbelow : μ {x : Gap | (x : ℝ) < (d : ℝ)}=0 := by
    simpa only [ae_iff,not_le] using hs
  have hCDF : ρ ≤ μ.real {x : Gap | (x : ℝ) ≤ (d : ℝ)} := hm.trans (measureReal_mono (by
    intro x hx
    rw [mem_singleton_iff] at hx
    subst x
    exact (le_refl (d : ℝ))))
  apply le_antisymm
  · by_contra h
    have hc := hp.2.2.2 (d : ℝ) (lt_of_not_ge h)
    exact (not_lt_of_ge hCDF) hc
  · by_contra h
    have hlt : quantileThreshold μ ρ < (d : ℝ) := lt_of_not_ge h
    have hzero : μ {x : Gap | (x : ℝ) ≤ quantileThreshold μ ρ}=0 :=
      measure_mono_null (fun x hx => (show (x : ℝ) ≤ quantileThreshold μ ρ from hx).trans_lt hlt) hbelow
    have hr := hp.2.2.1
    simp only [measureReal_def,hzero,ENNReal.toReal_zero] at hr
    exact (not_le_of_gt hρ) hr

theorem quantileTail_at_min_atom (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (d : Gap)
    (hs : ∀ᵐ x : Gap ∂μ, (d : ℝ) ≤ (x : ℝ)) (hm : ρ ≤ μ.real {d}) :
    quantileTail μ ρ = ENNReal.ofReal ρ • Measure.dirac d := by
  have ht := quantileThreshold_at_min_atom μ hρ hρ1 d hs hm
  have hbelow : μ {x : Gap | (x : ℝ) < (d : ℝ)}=0 := by
    simpa only [ae_iff,not_le] using hs
  have hset : {x : Gap | (x : ℝ)=(d : ℝ)} = {d} := by
    ext x
    simp only [mem_ofPred_eq,mem_singleton_iff,Subtype.ext_iff]
  have hr := quantileBoundaryFraction_properties μ hρ hρ1
  have hmul : quantileBoundaryFraction μ ρ*μ.real {d}=ρ := by
    have h := hr.2.2
    rw [ht,hset] at h
    simp only [measureReal_def,hbelow,ENNReal.toReal_zero,sub_zero] at h
    exact h
  unfold quantileTail
  rw [ht,Measure.restrict_eq_zero.mpr hbelow,zero_add,hset,Measure.restrict_singleton,smul_smul]
  have he : ENNReal.ofReal (quantileBoundaryFraction μ ρ)*μ {d}=ENNReal.ofReal ρ := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ {d}),← ENNReal.ofReal_mul hr.1]
    exact congrArg ENNReal.ofReal hmul
  rw [he]

end ThresholdHC.QuantileOptimality
