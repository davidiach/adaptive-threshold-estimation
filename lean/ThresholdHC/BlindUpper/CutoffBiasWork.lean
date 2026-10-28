import ThresholdHC.BlindUpper.CutoffBounds

noncomputable section

namespace ThresholdHC.BlindUpper
open MeasureTheory ThresholdHC.CriticalEntropy ThresholdHC.Uniform713
open scoped ENNReal

theorem binary_mean_error {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ)
    (hY : Measurable Y) (hbin : ∀ ω, Y ω = 0 ∨ Y ω = 1) (S : Bool) :
    |(∫ ω, Y ω ∂μ)-Tier2.bit S| ≤ μ.real {ω | Y ω ≠ Tier2.bit S} := by
  have hi : Integrable Y μ := by
    apply Integrable.of_bound hY.aestronglyMeasurable 1
    exact ae_of_all _ (fun ω => by rcases hbin ω with h | h <;> simp [h])
  have hset : MeasurableSet {ω | Y ω ≠ Tier2.bit S} :=
    (measurableSet_eq_fun hY measurable_const).compl
  calc
    _ = |∫ ω, Y ω-Tier2.bit S ∂μ| := by
      rw [integral_sub hi (integrable_const _)]; simp
    _ ≤ ∫ ω, |Y ω-Tier2.bit S| ∂μ := abs_integral_le_integral_abs
    _ = _ := by
      have he : (fun ω => |Y ω-Tier2.bit S|) =
          {ω | Y ω ≠ Tier2.bit S}.indicator (fun _ => (1 : ℝ)) := by
        funext ω
        rcases hbin ω with h | h <;> cases S <;> simp [h,Tier2.bit,Set.indicator_apply]
      rw [he,integral_indicator_const (1 : ℝ) hset]
      simp

theorem cutoff_bias_le (L : ℕ) (d : ℝ) (S : Bool) (hd : 0 < d) (hdmax : d ≤ 1/2) :
    |(∫ z, cutoffValue L z ∂samplingMeasure (Tier2.tapeMeasure (Tier2.coinParameter d S hd hdmax)))
      - Tier2.bit S| ≤ min 1 ((((2 : ℝ)^L*d^2)⁻¹)^2) := by
  rw [cutoff_mean]
  have hb := binary_mean_error (Tier2.tapeMeasure (Tier2.coinParameter d S hd hdmax))
    (classifierValue L) (measurable_classifierValue L)
    (fun ω => Tier2.Model.decision_zero_or_one (fun k => dyadicMean Tier2.observations k ω) L) S
  have he := ThresholdHC.Proofs.lemma6_error L d S hd hdmax
  rw [Tier2.errProbK_eq_measure L d S hd hdmax] at he
  exact hb.trans he

theorem cutoff_expected_work_real (L : ℕ) (p : unitInterval) :
    expectedStoppedProcedureWork levelMeasure p (cutoffProcedure L) =
      ENNReal.ofReal (∫ z, (cutoffCost L z : ℝ) ∂samplingMeasure (Tier2.tapeMeasure p)) := by
  rw [ofReal_integral_eq_lintegral_ofReal (cutoff_cost_integrable L p)
    (ae_of_all _ (fun z => Nat.cast_nonneg (cutoffCost L z)))]
  unfold expectedStoppedProcedureWork samplingMeasure
  apply lintegral_congr
  intro z
  simp [stoppedProcedureWork,cutoffProcedure,finiteStoppedProcedure]

theorem cutoff_expected_work_le (L : ℕ) (d : ℝ) (S : Bool) (hd : 0 < d) (hdmax : d ≤ 1/2) :
    expectedStoppedProcedureWork levelMeasure (Tier2.coinParameter d S hd hdmax) (cutoffProcedure L) ≤
      ENNReal.ofReal (149*min (Real.sqrt ((2 : ℝ)^L)) d⁻¹) := by
  rw [cutoff_expected_work_real]
  exact ENNReal.ofReal_le_ofReal (cutoff_cost_mean_le L d S hd hdmax)

theorem cutoff_expected_work_pos (L : ℕ) (p : unitInterval) :
    0 < expectedStoppedProcedureWork levelMeasure p (cutoffProcedure L) := by
  have hlow : ENNReal.ofReal (levelProb 0) ≤ expectedStoppedProcedureWork levelMeasure p (cutoffProcedure L) := by
    have hf : Measurable (fun z : ℕ × (ℕ → Bool) =>
        ({0} : Set ℕ).indicator (fun _ => (1 : ℝ≥0∞)) z.1) :=
      (measurable_const.indicator (measurableSet_singleton 0)).comp measurable_fst
    have hm := lintegral_mono (μ := samplingMeasure (Tier2.tapeMeasure p))
      (f := fun z : ℕ × (ℕ → Bool) => ({0} : Set ℕ).indicator (fun _ => (1 : ℝ≥0∞)) z.1)
      (g := fun z => stoppedProcedureWork (cutoffProcedure L) z) (fun z => by
        by_cases hz : z.1 = 0
        · simp only [Set.indicator_apply,Set.mem_singleton_iff,hz,ite_true]
          have hez : z = (0,z.2) := Prod.ext hz rfl
          rw [hez]
          simp [stoppedProcedureWork,cutoffProcedure,finiteStoppedProcedure,cutoff_zero_level_cost]
        · simp [Set.indicator_apply,hz])
    have he : (∫⁻ z : ℕ × (ℕ → Bool),
        ({0} : Set ℕ).indicator (fun _ => (1 : ℝ≥0∞)) z.1 ∂samplingMeasure (Tier2.tapeMeasure p)) =
        ENNReal.ofReal (levelProb 0) := by
      rw [samplingMeasure,lintegral_prod _ hf.aemeasurable]
      simp only [lintegral_const,measure_univ,mul_one]
      rw [lintegral_indicator_fun_one (measurableSet_singleton 0),levelMeasure_singleton]
    rw [he] at hm
    exact hm
  exact (ENNReal.ofReal_pos.mpr (levelProb_pos 0)).trans_le hlow

end ThresholdHC.BlindUpper
