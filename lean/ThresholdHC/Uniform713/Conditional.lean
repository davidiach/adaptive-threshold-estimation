import ThresholdHC.Uniform713.Specification
import ThresholdHC.Uniform713.ClassifierModel
import ThresholdHC.Uniform713.Series
import ThresholdHC.Uniform713.Estimator
import ThresholdHC.Uniform713.Convergence

/-!
Fixed-law assembly of the actual random-level classifier estimator.
The tail interface is proved from independent bounded observations by Concentration.
No classifier error, expected work, moment, or unbiasedness conclusion is assumed here.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace ThresholdHC.Uniform713

/-- The full fixed-gap, fixed-sign estimator analysis, including exact unbiasedness. -/
theorem conditional_bounds {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (d : ℝ) (s : Bool)
    (hd : 0 < d) (hdhalf : d ≤ 1/2)
    (ht : HasMeanTails μ (dyadicMean X) (coinMean d s)) :
    MemLp (estimator (decisions X)) 2 (samplingMeasure μ) ∧
    Integrable (sampled (levelWork X)) (samplingMeasure μ) ∧
    (∫ x, (estimator (decisions X) x)^2 ∂samplingMeasure μ) < 23/d ∧
    (∫ x, sampled (levelWork X) x ∂samplingMeasure μ) < 31/d ∧
    (∫ x, estimator (decisions X) x ∂samplingMeasure μ) = signValue s := by
  have hz : ∀ L, Measurable (decisions X L) :=
    fun L => measurable_decision (dyadicMean X) ht.measurable L
  have hzi : ∀ L, Integrable (decisions X L) μ :=
    fun L => integrable_decision (dyadicMean X) ht.measurable μ L
  have hzb : ∀ L ω, decisions X L ω = 0 ∨ decisions X L ω = 1 :=
    fun L ω => decision_zero_or_one (fun k => dyadicMean X k ω) L
  have herr : ∀ L, μ.real {ω | decisions X L ω ≠ signValue s} ≤
      errorPrefactor/(cap L*d^2)^2 := by
    intro L
    cases s with
    | false =>
      simpa only [decisions, signValue, Bool.false_eq_true, ↓reduceIte] using
        error_negative_bound L hd (by simpa only [coinMean, Bool.false_eq_true, ↓reduceIte] using ht)
    | true =>
      simpa only [decisions, signValue, ↓reduceIte] using
        error_positive_bound L hd (by simpa only [coinMean, ↓reduceIte] using ht)
  have hi2 : ∀ L, Integrable (fun ω => (increment (fun k => decisions X k ω) L)^2) μ :=
    fun L => integrable_classifier_increment_sq ht.measurable L
  have he : ∀ L, (∫ ω, (increment (fun k => decisions X k ω) L)^2 ∂μ) ≤
      min 1 (3/(cap L*d^2)^2) := by
    intro L
    exact increment_secondMoment_envelope (signValue s) hd hdhalf ht.measurable herr L
  have hs2 := secondMomentSeries_bound d hd hdhalf
    (fun L => ∫ ω, (increment (fun k => decisions X k ω) L)^2 ∂μ)
    (fun L => integral_nonneg (fun ω => sq_nonneg _)) he
  have hY : MemLp (estimator (decisions X)) 2 (samplingMeasure μ) :=
    estimator_memLp hz hi2 hs2.1
  have hY2 : (∫ x, (estimator (decisions X) x)^2 ∂samplingMeasure μ) < 23/d := by
    rw [estimator_second_moment hY]
    exact hs2.2
  have hwm : ∀ L, Measurable (levelWork X L) :=
    fun L => measurable_work (dyadicMean X) ht.measurable L
  have hwi : ∀ L, Integrable (levelWork X L) μ :=
    fun L => integrable_work (dyadicMean X) ht.measurable μ L
  have hw0 : ∀ L ω, 0 ≤ levelWork X L ω :=
    fun L ω => (work_pos (fun k => dyadicMean X k ω) L).le
  have hw : ∀ L, (∫ ω, levelWork X L ω ∂μ) ≤ 7*workEnvelope L d := by
    intro L
    cases s with
    | false =>
      exact expected_work_negative_bound L hd hdhalf
        (by simpa only [coinMean, Bool.false_eq_true, ↓reduceIte] using ht)
    | true =>
      exact expected_work_positive_bound L hd hdhalf
        (by simpa only [coinMean, ↓reduceIte] using ht)
  have hsw := workSeries_bound d hd hdhalf
    (fun L => ∫ ω, levelWork X L ω ∂μ) (fun L => integral_nonneg (hw0 L)) hw
  have hW : Integrable (sampled (levelWork X)) (samplingMeasure μ) := by
    apply integrable_sampled hwm hwi
    simpa only [Real.norm_of_nonneg (hw0 _ _)] using hsw.1
  have hW1 : (∫ x, sampled (levelWork X) x ∂samplingMeasure μ) < 31/d := by
    rw [integral_sampled hW]
    exact hsw.2
  have hsb : ∀ ω : Ω, (fun _ : Ω => signValue s) ω = 0 ∨
      (fun _ : Ω => signValue s) ω = 1 := by
    intro ω
    cases s <;> simp [signValue]
  have hlim : Tendsto (fun L => ∫ ω, decisions X L ω ∂μ) atTop (𝓝 (signValue s)) := by
    have hp := tendsto_error_probability μ (fun L => {ω | decisions X L ω ≠ signValue s}) d hd herr
    simpa only [integral_const, probReal_univ, one_smul] using
      tendsto_mean_of_binary_error hz measurable_const hzb hsb hp
  have hYu : (∫ x, estimator (decisions X) x ∂samplingMeasure μ) = signValue s :=
    estimator_unbiased hzi (hY.integrable (by norm_num)) hlim
  exact ⟨hY, hW, hY2, hW1, hYu⟩

end ThresholdHC.Uniform713

#print axioms ThresholdHC.Uniform713.conditional_bounds
