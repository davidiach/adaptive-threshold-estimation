import ThresholdHC.BlindUpper.CutoffMoments
import ThresholdHC.Proofs.Tier2.ClassifierProb

noncomputable section

namespace ThresholdHC.BlindUpper
open MeasureTheory ThresholdHC.CriticalEntropy ThresholdHC.Uniform713
open scoped ENNReal

theorem cutoff_secondMoment_sum (L : ℕ) (p : unitInterval) :
    (∫ z, (cutoffValue L z)^2 ∂samplingMeasure (Tier2.tapeMeasure p)) =
      ∑ l ∈ Finset.range (L+1),
        (∫ ω, (increment (fun k => classifierValue k ω) l)^2 ∂Tier2.tapeMeasure p) / levelProb l := by
  have he := integral_sampled_cutoff (Tier2.tapeMeasure p) L
    (fun l ω => (cutoffValue L (l,ω))^2)
    (fun l => ((measurable_cutoffValue L).comp (measurable_const.prodMk measurable_id)).pow_const 2)
    (cutoff_section_sq_integrable L · p)
    (fun l hl => by funext ω; simp [cutoffValue,not_le.mpr hl])
  change (∫ z, sampled (fun l ω => (cutoffValue L (l,ω))^2) z ∂_) = _
  rw [he]
  apply Finset.sum_congr rfl
  intro l hl
  have h : l ≤ L := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hl
  simp_rw [cutoffValue_increment,ite_eq_left h,div_pow,integral_div]
  have hp := ne_of_gt (levelProb_pos l)
  field_simp

theorem cutoff_secondMoment_eq (L : ℕ) (d : ℝ) (S : Bool) (hd : 0 < d) (hdmax : d ≤ 1/2) :
    (∫ z, (cutoffValue L z)^2 ∂samplingMeasure (Tier2.tapeMeasure (Tier2.coinParameter d S hd hdmax))) =
      ThresholdHC.secondMomentK 1 1 L d S := by
  rw [cutoff_secondMoment_sum]
  unfold ThresholdHC.secondMomentK
  apply Finset.sum_congr rfl
  intro l hl
  have h : l ≤ L := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hl
  exact (congrArg (fun x : ℝ => x / levelProb l)
    (Tier2.deltaK_secondMoment_eq_integral L l h (Tier2.coinParameter d S hd hdmax))).symm

theorem cutoff_secondMoment_le (L : ℕ) (d : ℝ) (S : Bool) (hd : 0 < d) (hdmax : d ≤ 1/2) :
    (∫ z, (cutoffValue L z)^2 ∂samplingMeasure (Tier2.tapeMeasure (Tier2.coinParameter d S hd hdmax))) ≤
      85 * min (Real.sqrt ((2 : ℝ)^L)) d⁻¹ := by
  rw [cutoff_secondMoment_eq]
  exact ThresholdHC.Proofs.lemma7_second_moment L d S hd hdmax

theorem cutoff_cost_section_integrable (L l : ℕ) (p : unitInterval) :
    Integrable (fun ω => (cutoffCost L (l,ω) : ℝ)) (Tier2.tapeMeasure p) := by
  have hm : Measurable (fun ω => (cutoffCost L (l,ω) : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
      ((measurable_cutoffCost L).comp (measurable_const.prodMk measurable_id))
  apply Integrable.of_bound hm.aestronglyMeasurable ((2 : ℝ)^L)
  apply ae_of_all
  intro ω
  rw [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast cutoffCost_le L (l,ω)

theorem cutoff_cost_integrable (L : ℕ) (p : unitInterval) :
    Integrable (fun z => (cutoffCost L z : ℝ)) (samplingMeasure (Tier2.tapeMeasure p)) := by
  apply integrable_sampled_cutoff (Tier2.tapeMeasure p) L (fun l ω => (cutoffCost L (l,ω) : ℝ))
    (fun l => (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
      ((measurable_cutoffCost L).comp (measurable_const.prodMk measurable_id)))
    (cutoff_cost_section_integrable L · p)
  intro l hl
  funext ω
  simp [cutoffCost,not_le.mpr hl]

theorem cutoff_cost_mean_eq (L : ℕ) (d : ℝ) (S : Bool) (hd : 0 < d) (hdmax : d ≤ 1/2) :
    (∫ z, (cutoffCost L z : ℝ) ∂samplingMeasure (Tier2.tapeMeasure (Tier2.coinParameter d S hd hdmax))) =
      ThresholdHC.workMomentK 1 1 L d S := by
  let p := Tier2.coinParameter d S hd hdmax
  have he := integral_sampled_cutoff (Tier2.tapeMeasure p) L (fun l ω => (cutoffCost L (l,ω) : ℝ))
    (fun l => (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
      ((measurable_cutoffCost L).comp (measurable_const.prodMk measurable_id)))
    (cutoff_cost_section_integrable L · p)
    (fun l hl => by funext ω; simp [cutoffCost,not_le.mpr hl])
  change (∫ z, sampled (fun l ω => (cutoffCost L (l,ω) : ℝ)) z ∂_) = _
  rw [he]
  unfold ThresholdHC.workMomentK
  apply Finset.sum_congr rfl
  intro l hl
  have h : l ≤ L := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hl
  calc
    _ = levelProb l * ∫ ω, Tier2.Model.work (fun k => dyadicMean Tier2.observations k ω) l
        ∂Tier2.tapeMeasure p := by
      congr 1
      apply integral_congr_ae
      exact ae_of_all _ (fun ω => by simp [cutoffCost,h,classifierStop_real])
    _ = _ := (congrArg (fun x : ℝ => levelProb l * x) (Tier2.levelWork_eq_integral L l h p)).symm

theorem cutoff_cost_mean_le (L : ℕ) (d : ℝ) (S : Bool) (hd : 0 < d) (hdmax : d ≤ 1/2) :
    (∫ z, (cutoffCost L z : ℝ) ∂samplingMeasure (Tier2.tapeMeasure (Tier2.coinParameter d S hd hdmax))) ≤
      149 * min (Real.sqrt ((2 : ℝ)^L)) d⁻¹ := by
  rw [cutoff_cost_mean_eq]
  exact ThresholdHC.Proofs.lemma7_work L d S hd hdmax

end ThresholdHC.BlindUpper
