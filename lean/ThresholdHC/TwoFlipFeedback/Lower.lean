import ThresholdHC.TwoFlipFeedback.LowerBayes

/-! Lift of the per-seed Bayes bound to the original experiment: every
estimator with a pathwise cap of two flips in the noninteractive normal form
has worst rare mean squared error at least `lowerValue = 1547585/10^8`. The
private seed, the hidden magnitudes and signs, and arbitrary measurable
outputs are retained; outputs are clipped to `[0, 1/4]`, which cannot increase
the loss. -/

noncomputable section
namespace ThresholdHC.TwoFlipFeedback
open MeasureTheory
open scoped ENNReal
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.HardBudget

private theorem measurable_clipped {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R)
    (w : Prefix 2) : Measurable (fun r => clippedOutput A r w) :=
  measurable_const.max (measurable_const.min
    (A.output_measurable.comp (measurable_id.prodMk measurable_const)))

private def seedLoss {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (q : SignLaw)
    (θ : ℝ) (r : R) : ℝ :=
  ∑ w, seedWeight twoGapLaw A q r w * (clippedOutput A r w - θ)^2

private theorem seedLoss_integrable {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R)
    (q : SignLaw) (θ : ℝ) (hθ : 0 ≤ θ ∧ θ ≤ 1/4) : Integrable (seedLoss A q θ) A.randomLaw := by
  have hm : Measurable (seedLoss A q θ) :=
    Finset.measurable_sum _ fun w _ => (measurable_seedWeight twoGapLaw A q w).mul
      (((measurable_clipped A w).sub measurable_const).pow_const 2)
  refine (integrable_const (1:ℝ)).mono' hm.aestronglyMeasurable (ae_of_all _ fun r => ?_)
  have ht := seedWeight_total twoGapLaw A q r
  have hn : 0 ≤ seedLoss A q θ r :=
    Finset.sum_nonneg fun w _ => mul_nonneg (ht.1 w) (sq_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hn, ← ht.2]
  apply Finset.sum_le_sum
  intro w _
  have hc := clippedOutput_mem A r w
  have hs : (clippedOutput A r w - θ)^2 ≤ 1 := by nlinarith
  exact mul_le_of_le_one_right (ht.1 w) hs

private theorem seedLoss_nonneg {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R)
    (q : SignLaw) (θ : ℝ) (r : R) : 0 ≤ seedLoss A q θ r :=
  Finset.sum_nonneg fun w _ => mul_nonneg ((seedWeight_total twoGapLaw A q r).1 w) (sq_nonneg _)

private theorem seed_bayes {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R)
    (hA : NoninteractiveCapTwo A) (r : R) :
    lowerValue ≤ (1 - designPrior) * seedLoss A nullLaw 0 r +
      designPrior * seedLoss A hardLaw (1/4) r := by
  have h := policy_bayes (A.policy r) (hA r) (clippedOutput A r)
  unfold policyLoss wordLoss at h
  unfold seedLoss seedWeight
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  convert h using 2
  ring

/-- The uniform lower bound for the noninteractive cap-two class. -/
theorem uniform_lower {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R)
    (hcap : PathwiseCap A 2) (hA : NoninteractiveCapTwo A) :
    ENNReal.ofReal lowerValue ≤ rareSquaredRisk A := by
  have hp : 0 ≤ designPrior := by norm_num [designPrior]
  have hq : 0 ≤ 1 - designPrior := by norm_num [designPrior]
  have r0 : squaredRisk (experimentLaw twoGapLaw A nullLaw) (populationOutput A) 0 ≤
      rareSquaredRisk A := by
    have h := le_iSup₂ (f := fun (q : SignLaw) (_ : RarePrior twoGapLaw (1/4) q) =>
      squaredRisk (experimentLaw twoGapLaw A q) (populationOutput A) (signMean twoGapLaw q.val))
      nullLaw nullLaw_rare
    rwa [nullLaw_mean] at h
  have r1 : squaredRisk (experimentLaw twoGapLaw A hardLaw) (populationOutput A) (1/4) ≤
      rareSquaredRisk A := by
    have h := le_iSup₂ (f := fun (q : SignLaw) (_ : RarePrior twoGapLaw (1/4) q) =>
      squaredRisk (experimentLaw twoGapLaw A q) (populationOutput A) (signMean twoGapLaw q.val))
      hardLaw hardLaw_rare
    rwa [hardLaw_mean] at h
  have l0 := capped_risk_lower twoGapLaw A hcap nullLaw 0 ⟨le_rfl, by norm_num⟩
  have l1 := capped_risk_lower twoGapLaw A hcap hardLaw (1/4) ⟨by norm_num, le_rfl⟩
  change ENNReal.ofReal (∫ r, seedLoss A nullLaw 0 r ∂A.randomLaw) ≤ _ at l0
  change ENNReal.ofReal (∫ r, seedLoss A hardLaw (1/4) r ∂A.randomLaw) ≤ _ at l1
  have i0 := seedLoss_integrable A nullLaw 0 ⟨le_rfl, by norm_num⟩
  have i1 := seedLoss_integrable A hardLaw (1/4) ⟨by norm_num, le_rfl⟩
  have hint : lowerValue ≤ (1 - designPrior) * (∫ r, seedLoss A nullLaw 0 r ∂A.randomLaw) +
      designPrior * (∫ r, seedLoss A hardLaw (1/4) r ∂A.randomLaw) := by
    have h := integral_mono (integrable_const lowerValue) ((i0.const_mul _).add (i1.const_mul _))
      (fun r => seed_bayes A hA r)
    simp only [Pi.add_apply] at h
    rw [integral_const, integral_add (i0.const_mul _) (i1.const_mul _), integral_const_mul,
      integral_const_mul] at h
    simpa using h
  have n0 : 0 ≤ ∫ r, seedLoss A nullLaw 0 r ∂A.randomLaw :=
    integral_nonneg (seedLoss_nonneg A nullLaw 0)
  have n1 : 0 ≤ ∫ r, seedLoss A hardLaw (1/4) r ∂A.randomLaw :=
    integral_nonneg (seedLoss_nonneg A hardLaw (1/4))
  calc
    ENNReal.ofReal lowerValue ≤ ENNReal.ofReal ((1 - designPrior) *
        (∫ r, seedLoss A nullLaw 0 r ∂A.randomLaw) +
        designPrior * (∫ r, seedLoss A hardLaw (1/4) r ∂A.randomLaw)) :=
      ENNReal.ofReal_le_ofReal hint
    _ = ENNReal.ofReal (1 - designPrior) * ENNReal.ofReal (∫ r, seedLoss A nullLaw 0 r ∂A.randomLaw) +
        ENNReal.ofReal designPrior * ENNReal.ofReal (∫ r, seedLoss A hardLaw (1/4) r ∂A.randomLaw) := by
      rw [ENNReal.ofReal_add (mul_nonneg hq n0) (mul_nonneg hp n1), ENNReal.ofReal_mul hq,
        ENNReal.ofReal_mul hp]
    _ ≤ ENNReal.ofReal (1 - designPrior) * rareSquaredRisk A +
        ENNReal.ofReal designPrior * rareSquaredRisk A := by
      gcongr
      · exact l0.trans r0
      · exact l1.trans r1
    _ = rareSquaredRisk A := by
      rw [← add_mul, ← ENNReal.ofReal_add hq hp, sub_add_cancel, ENNReal.ofReal_one, one_mul]

/-- The minimax risk of the class is at least `lowerValue`. -/
theorem minimax_lower : ENNReal.ofReal lowerValue ≤ noninteractiveMinimax := by
  unfold noninteractiveMinimax
  apply le_sInf
  rintro t ⟨R, _, A, hcap, hA, rfl⟩
  exact uniform_lower A hcap hA

end ThresholdHC.TwoFlipFeedback
