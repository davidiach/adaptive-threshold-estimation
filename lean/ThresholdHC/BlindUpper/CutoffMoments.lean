import ThresholdHC.BlindUpper.CutoffProcedure
import ThresholdHC.Uniform713.Estimator
import ThresholdHC.Proofs.Tier2.ClassifierExpectations

noncomputable section

namespace ThresholdHC.BlindUpper
open MeasureTheory ThresholdHC.CriticalEntropy ThresholdHC.Uniform713
open scoped ENNReal

theorem integrable_sampled_cutoff {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (L : ℕ) (f : ℕ → Ω → ℝ)
    (hm : ∀ l, Measurable (f l)) (hi : ∀ l, Integrable (f l) μ)
    (hz : ∀ l, L < l → f l = 0) : Integrable (sampled f) (samplingMeasure μ) := by
  apply integrable_sampled hm hi
  apply summable_of_ne_finset_zero (s := Finset.range (L+1))
  intro l hl
  have h : L < l := by simp only [Finset.mem_range] at hl; omega
  simp [hz l h]

theorem integral_sampled_cutoff {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (L : ℕ) (f : ℕ → Ω → ℝ)
    (hm : ∀ l, Measurable (f l)) (hi : ∀ l, Integrable (f l) μ)
    (hz : ∀ l, L < l → f l = 0) :
    (∫ z, sampled f z ∂samplingMeasure μ) =
      ∑ l ∈ Finset.range (L+1), levelProb l * ∫ ω, f l ω ∂μ := by
  rw [integral_sampled (integrable_sampled_cutoff μ L f hm hi hz)]
  apply tsum_eq_sum
  intro l hl
  have h : L < l := by simp only [Finset.mem_range] at hl; omega
  simp [hz l h]

theorem cutoffValue_increment (L l : ℕ) (ω : ℕ → Bool) :
    cutoffValue L (l,ω) =
      if l ≤ L then increment (fun k => classifierValue k ω) l / levelProb l else 0 := by
  cases l <;> simp [cutoffValue,increment,ThresholdHC.pLevel,levelProb]

theorem classifierStop_real (l : ℕ) (ω : ℕ → Bool) :
    (classifierStop l ω : ℝ) = Tier2.Model.work (fun k => dyadicMean Tier2.observations k ω) l := by
  simp [classifierStop,Tier2.Model.work,cap]

theorem cutoff_section_integrable (L l : ℕ) (p : unitInterval) :
    Integrable (fun ω => cutoffValue L (l,ω)) (Tier2.tapeMeasure p) := by
  simp_rw [cutoffValue_increment]
  by_cases h : l ≤ L
  · simp only [ite_eq_left h]
    exact (Tier2.Model.integrable_classifier_increment
      (fun k => measurable_prefixMean Tier2.measurable_observations _) l).div_const _
  · simp only [ite_eq_right h]
    exact integrable_zero _ _ _

theorem cutoff_section_sq_integrable (L l : ℕ) (p : unitInterval) :
    Integrable (fun ω => (cutoffValue L (l,ω))^2) (Tier2.tapeMeasure p) := by
  simp_rw [cutoffValue_increment]
  by_cases h : l ≤ L
  · simp only [ite_eq_left h,div_pow]
    exact (Tier2.Model.integrable_classifier_increment_sq
      (fun k => measurable_prefixMean Tier2.measurable_observations _) l).div_const _
  · simp only [ite_eq_right h,zero_pow (by omega : 2 ≠ 0)]
    exact integrable_zero _ _ _

theorem cutoff_integrable (L : ℕ) (p : unitInterval) :
    Integrable (cutoffValue L) (samplingMeasure (Tier2.tapeMeasure p)) := by
  apply integrable_sampled_cutoff (Tier2.tapeMeasure p) L
    (fun l ω => cutoffValue L (l,ω))
    (fun l => (measurable_cutoffValue L).comp (measurable_const.prodMk measurable_id))
    (cutoff_section_integrable L · p)
  intro l hl
  funext ω
  simp [cutoffValue,not_le.mpr hl]

theorem cutoff_sq_integrable (L : ℕ) (p : unitInterval) :
    Integrable (fun z => (cutoffValue L z)^2) (samplingMeasure (Tier2.tapeMeasure p)) := by
  apply integrable_sampled_cutoff (Tier2.tapeMeasure p) L
    (fun l ω => (cutoffValue L (l,ω))^2)
    (fun l => ((measurable_cutoffValue L).comp (measurable_const.prodMk measurable_id)).pow_const 2)
    (cutoff_section_sq_integrable L · p)
  intro l hl
  funext ω
  simp [cutoffValue,not_le.mpr hl]

theorem cutoff_mean (L : ℕ) (p : unitInterval) :
    (∫ z, cutoffValue L z ∂samplingMeasure (Tier2.tapeMeasure p)) =
      ∫ ω, classifierValue L ω ∂Tier2.tapeMeasure p := by
  have he := integral_sampled_cutoff (Tier2.tapeMeasure p) L
    (fun l ω => cutoffValue L (l,ω))
    (fun l => (measurable_cutoffValue L).comp (measurable_const.prodMk measurable_id))
    (cutoff_section_integrable L · p) (fun l hl => by funext ω; simp [cutoffValue,not_le.mpr hl])
  change (∫ z, sampled (fun l ω => cutoffValue L (l,ω)) z ∂_) = _
  rw [he]
  calc
    _ = ∑ l ∈ Finset.range (L+1),
        ∫ ω, increment (fun k => classifierValue k ω) l ∂Tier2.tapeMeasure p := by
      apply Finset.sum_congr rfl
      intro l hl
      have h : l ≤ L := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hl
      simp_rw [cutoffValue_increment,ite_eq_left h,integral_div]
      exact mul_div_cancel₀ _ (ne_of_gt (levelProb_pos l))
    _ = _ := by
      have hi (l : ℕ) : Integrable (fun ω => increment (fun k => classifierValue k ω) l)
          (Tier2.tapeMeasure p) := Tier2.Model.integrable_classifier_increment
        (m := dyadicMean Tier2.observations)
        (fun k => measurable_prefixMean Tier2.measurable_observations (2^k)) l
      rw [← integral_finsetSum _ (fun l hl => hi l)]
      apply integral_congr_ae
      exact ae_of_all _ (fun ω => sum_increment (fun k => classifierValue k ω) L)

end ThresholdHC.BlindUpper
