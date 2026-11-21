import ThresholdHC.TwoFlipDominance.AlmostSureDepth

/-! The lower bound for the paper's class under the almost-sure cap. Halting
after two flips holds almost surely, so the risk is at least that of the
clipped output read from the padded two-prefix; the per-seed Bayes bound
`policy_bayes` of `ThresholdHC.TwoFlipFeedback` applies on the almost-sure set
of seeds in the normal form. The arguments copy `capped_risk_lower` and
`uniform_lower` of that group with the pathwise steps replaced by almost-sure
ones; that group is not edited. -/

noncomputable section
namespace ThresholdHC.TwoFlipDominance
open MeasureTheory
open scoped ENNReal
open ThresholdHC.Tier3 ThresholdHC.Tier4 ThresholdHC.Tier6 ThresholdHC.RareAboveTwo
open ThresholdHC.HardBudget ThresholdHC.TwoFlipFeedback

private theorem clip_sq_le' (M θ x : ℝ) (hθ : 0 ≤ θ ∧ θ ≤ M) :
    (clipEstimate M x - θ)^2 ≤ (x - θ)^2 := by
  unfold clipEstimate
  rcases le_total x 0 with h | h
  · rw [min_eq_right (h.trans (hθ.1.trans hθ.2)), max_eq_left h]
    nlinarith
  · rcases le_total x M with h' | h'
    · rw [min_eq_right h', max_eq_right h]
    · rw [min_eq_left h', max_eq_right (hθ.1.trans hθ.2)]
      nlinarith

/-- Under the almost-sure cap, for a target in `[0, 1/4]` and a rare sign law,
the risk is at least that of the clipped prefix estimate. -/
theorem capped_risk_lower_ae {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R)
    (hcap : AlmostSureCap A 2) (q : SignLaw) (hq : RarePrior twoGapLaw (1/4) q) (θ : ℝ)
    (hθ : 0 ≤ θ ∧ θ ≤ 1/4) :
    ENNReal.ofReal (∫ r, ∑ w, seedWeight twoGapLaw A q r w * (clippedOutput A r w - θ)^2
      ∂A.randomLaw) ≤ squaredRisk (experimentLaw twoGapLaw A q) (populationOutput A) θ := by
  let f : R × Prefix 2 → ℝ := fun z => (clippedOutput A z.1 z.2 - θ)^2
  have hf : Measurable f := by
    have ho : Measurable (fun z : R × Prefix 2 => A.output (padJoint 2 z)) :=
      A.output_measurable.comp (measurable_padJoint 2)
    exact ((measurable_const.max (measurable_const.min ho)).sub measurable_const).pow_const 2
  have hb (x : R × Prefix 2) : |f x| ≤ 1/16 := by
    have h := clippedOutput_mem A x.1 x.2
    have e : |f x| = (clippedOutput A x.1 x.2 - θ)^2 := abs_of_nonneg (sq_nonneg _)
    rw [e]
    nlinarith
  rw [← prefix_kernel_integral twoGapLaw A q f hf (1/16) hb,
    ofReal_integral_eq_lintegral_ofReal (prefix_bounded_integrable twoGapLaw A q f hf (1/16) hb)
      (ae_of_all _ fun _ => sq_nonneg _)]
  unfold squaredRisk
  apply lintegral_mono_ae
  filter_upwards [ThresholdHC.StoppingProgram.original_path_valid twoGapLaw A q, hcap q hq]
    with z hz hw
  apply ENNReal.ofReal_le_ofReal
  have hhalt : A.policy z.1.1 (processHistory z.2 2) = none := by
    by_contra hne
    have h3 := (ThresholdHC.StoppingProgram.valid_path_continuation_work (A.policy z.1.1)
      z.2 hz 2 hne).trans hw
    rw [show ((2:ℕ):ℝ≥0∞) = ENNReal.ofReal 2 by simp] at h3
    have h4 := (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp h3
    norm_num at h4
  have hpad := ThresholdHC.StoppingProgram.valid_path_halt_reconstruction (A.policy z.1.1) z.2
    hz 2 hhalt
  change (clipEstimate (1/4) (A.output (z.1.1, padPrefix 2 (processPrefix 2 z.2))) - θ)^2 ≤
    (A.output (z.1.1, z.2) - θ)^2
  rw [hpad]
  exact clip_sq_le' _ _ _ hθ

private theorem measurable_clipped' {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R)
    (w : Prefix 2) : Measurable (fun r => clippedOutput A r w) :=
  measurable_const.max (measurable_const.min
    (A.output_measurable.comp (measurable_id.prodMk measurable_const)))

/-- The clipped seed loss at the sign law `q` and the target `θ`. -/
private def localSeedLoss {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (q : SignLaw)
    (θ : ℝ) (r : R) : ℝ :=
  ∑ w, seedWeight twoGapLaw A q r w * (clippedOutput A r w - θ)^2

private theorem localSeedLoss_integrable {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R)
    (q : SignLaw) (θ : ℝ) (hθ : 0 ≤ θ ∧ θ ≤ 1/4) :
    Integrable (localSeedLoss A q θ) A.randomLaw := by
  have hm : Measurable (localSeedLoss A q θ) :=
    Finset.measurable_sum _ fun w _ => (measurable_seedWeight twoGapLaw A q w).mul
      (((measurable_clipped' A w).sub measurable_const).pow_const 2)
  refine (integrable_const (1:ℝ)).mono' hm.aestronglyMeasurable (ae_of_all _ fun r => ?_)
  have ht := seedWeight_total twoGapLaw A q r
  have hn : 0 ≤ localSeedLoss A q θ r :=
    Finset.sum_nonneg fun w _ => mul_nonneg (ht.1 w) (sq_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hn, ← ht.2]
  apply Finset.sum_le_sum
  intro w _
  have hc := clippedOutput_mem A r w
  have hs : (clippedOutput A r w - θ)^2 ≤ 1 := by nlinarith
  exact mul_le_of_le_one_right (ht.1 w) hs

private theorem localSeedLoss_nonneg {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R)
    (q : SignLaw) (θ : ℝ) (r : R) : 0 ≤ localSeedLoss A q θ r :=
  Finset.sum_nonneg fun w _ => mul_nonneg ((seedWeight_total twoGapLaw A q r).1 w) (sq_nonneg _)

private theorem local_seed_bayes {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (r : R)
    (hr : NormalAt (A.policy r)) :
    lowerValue ≤ (1 - designPrior) * localSeedLoss A nullLaw 0 r +
      designPrior * localSeedLoss A hardLaw (1/4) r := by
  have h := policy_bayes (A.policy r) hr (clippedOutput A r)
  unfold policyLoss wordLoss at h
  unfold localSeedLoss seedWeight
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  convert h using 2
  ring

/-- The uniform lower bound for the paper's class under the almost-sure cap. -/
theorem uniform_lower_ae {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R)
    (hcap : AlmostSureCap A 2) (hA : LocalAcquisition A) :
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
  have l0 := capped_risk_lower_ae A hcap nullLaw nullLaw_rare 0 ⟨le_rfl, by norm_num⟩
  have l1 := capped_risk_lower_ae A hcap hardLaw hardLaw_rare (1/4) ⟨by norm_num, le_rfl⟩
  change ENNReal.ofReal (∫ r, localSeedLoss A nullLaw 0 r ∂A.randomLaw) ≤ _ at l0
  change ENNReal.ofReal (∫ r, localSeedLoss A hardLaw (1/4) r ∂A.randomLaw) ≤ _ at l1
  have i0 := localSeedLoss_integrable A nullLaw 0 ⟨le_rfl, by norm_num⟩
  have i1 := localSeedLoss_integrable A hardLaw (1/4) ⟨by norm_num, le_rfl⟩
  have hint : lowerValue ≤ (1 - designPrior) * (∫ r, localSeedLoss A nullLaw 0 r ∂A.randomLaw) +
      designPrior * (∫ r, localSeedLoss A hardLaw (1/4) r ∂A.randomLaw) := by
    have hae : ∀ᵐ r ∂A.randomLaw, lowerValue ≤ (1 - designPrior) * localSeedLoss A nullLaw 0 r +
        designPrior * localSeedLoss A hardLaw (1/4) r := by
      filter_upwards [seed_dominance A hcap hA] with r hr
      exact local_seed_bayes A r hr.2
    have h := integral_mono_ae (integrable_const lowerValue)
      ((i0.const_mul _).add (i1.const_mul _)) hae
    simp only [Pi.add_apply] at h
    rw [integral_const, integral_add (i0.const_mul _) (i1.const_mul _), integral_const_mul,
      integral_const_mul] at h
    simpa using h
  have n0 : 0 ≤ ∫ r, localSeedLoss A nullLaw 0 r ∂A.randomLaw :=
    integral_nonneg (localSeedLoss_nonneg A nullLaw 0)
  have n1 : 0 ≤ ∫ r, localSeedLoss A hardLaw (1/4) r ∂A.randomLaw :=
    integral_nonneg (localSeedLoss_nonneg A hardLaw (1/4))
  calc
    ENNReal.ofReal lowerValue ≤ ENNReal.ofReal ((1 - designPrior) *
        (∫ r, localSeedLoss A nullLaw 0 r ∂A.randomLaw) +
        designPrior * (∫ r, localSeedLoss A hardLaw (1/4) r ∂A.randomLaw)) :=
      ENNReal.ofReal_le_ofReal hint
    _ = ENNReal.ofReal (1 - designPrior) *
          ENNReal.ofReal (∫ r, localSeedLoss A nullLaw 0 r ∂A.randomLaw) +
        ENNReal.ofReal designPrior *
          ENNReal.ofReal (∫ r, localSeedLoss A hardLaw (1/4) r ∂A.randomLaw) := by
      rw [ENNReal.ofReal_add (mul_nonneg hq n0) (mul_nonneg hp n1), ENNReal.ofReal_mul hq,
        ENNReal.ofReal_mul hp]
    _ ≤ ENNReal.ofReal (1 - designPrior) * rareSquaredRisk A +
        ENNReal.ofReal designPrior * rareSquaredRisk A := by
      gcongr
      · exact l0.trans r0
      · exact l1.trans r1
    _ = rareSquaredRisk A := by
      rw [← add_mul, ← ENNReal.ofReal_add hq hp, sub_add_cancel, ENNReal.ofReal_one, one_mul]

/-- The minimax risk of the paper's class is at least `lowerValue`. -/
theorem local_minimax_lower : ENNReal.ofReal lowerValue ≤ localMinimax := by
  unfold localMinimax
  apply le_sInf
  rintro t ⟨R, _, A, hcap, hA, rfl⟩
  exact uniform_lower_ae A hcap hA

end ThresholdHC.TwoFlipDominance
