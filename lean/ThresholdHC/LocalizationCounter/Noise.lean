import ThresholdHC.LocalizationCounter.Specification
import ThresholdHC.Observable713.Realization
import ThresholdHC.Proofs.Tier2.ClassifierExpectations
import ThresholdHC.Proofs.Tier2.ClassifierTelescoping

/-! Proposition `loc:prop:noise`. The level-zero event `J = 0` has probability
`p₀ = 1 - 2^{-1/2}` and there every first-stop classifier returns the first flip,
so `Y = X/p₀` with `X` one Bernoulli flip of success probability `1/2-d`. Hence
`E Y² ≥ (1/2-d)/p₀` for the 713 variant, for the original untruncated estimator
and for the truncated original estimator. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace ThresholdHC.LocalizationCounter
open ThresholdHC.Tier6 ThresholdHC.Uniform713 ThresholdHC.ObservableSimulation
  ThresholdHC.CriticalEntropy ThresholdHC.BlindUpper

/-- At level zero every first-stop classifier reads only the first flip. -/
theorem firstDecision_level_zero (b : ℕ → ℕ → ℝ) (ω : ℕ → Bool) :
    firstDecision b (fun k => dyadicMean Tier2.observations k ω) 0 = Tier2.bit (ω 0) := by
  have hs : firstStop b (fun k => dyadicMean Tier2.observations k ω) 0 = 0 :=
    Nat.le_zero.mp (firstStop_le _ _ _)
  unfold firstDecision
  rw [hs]
  simp only [dyadicMean, prefixMean, pow_zero, Finset.range_one, Finset.sum_singleton,
    Nat.cast_one, div_one, Tier2.observations]
  cases ω 0 <;> norm_num [Tier2.bit]

theorem bit_nonneg (b : Bool) : 0 ≤ Tier2.bit b := by
  unfold Tier2.bit; split <;> norm_num

/-- The level-zero term alone gives the second-moment floor `p/p₀`. -/
theorem level_zero_floor (z : ℕ → (ℕ → Bool) → ℝ) (hz : ∀ l, Measurable (z l))
    (h0 : ∀ ω, z 0 ω = Tier2.bit (ω 0)) (p : unitInterval) :
    ENNReal.ofReal ((p : ℝ) / levelProb 0) ≤
      ∫⁻ x, ENNReal.ofReal ((estimator z x)^2) ∂samplingMeasure (Tier2.tapeMeasure p) := by
  have hm : Measurable (fun x => ENNReal.ofReal ((estimator z x)^2)) :=
    ((measurable_estimator hz).pow_const 2).ennreal_ofReal
  rw [samplingMeasure, lintegral_prod _ hm.aemeasurable]
  have hc := levelProb_pos 0
  have hlev : (∫⁻ l, ∫⁻ ω, ENNReal.ofReal ((estimator z (l,ω))^2)
      ∂Tier2.tapeMeasure p ∂levelMeasure) =
      ∑' l, ENNReal.ofReal (levelProb l) *
        ∫⁻ ω, ENNReal.ofReal ((estimator z (l,ω))^2) ∂Tier2.tapeMeasure p := by
    simp only [levelMeasure, lintegral_sum_measure, lintegral_smul_measure, lintegral_dirac,
      smul_eq_mul]
  rw [hlev]
  refine le_trans ?_ (ENNReal.le_tsum 0)
  have hval (ω : ℕ → Bool) :
      ENNReal.ofReal ((estimator z (0,ω))^2) =
        ENNReal.ofReal (Tier2.bit (ω 0)) * ENNReal.ofReal (1/(levelProb 0)^2) := by
    rw [← ENNReal.ofReal_mul (bit_nonneg _)]
    congr 1
    simp only [estimator, increment, h0]
    cases ω 0 <;> simp [Tier2.bit]
  simp_rw [hval]
  have hint : Integrable (fun ω : ℕ → Bool => Tier2.bit (ω 0)) (Tier2.tapeMeasure p) :=
    Integrable.of_bound (Tier2.measurable_observations 0).aestronglyMeasurable 1
      (ae_of_all _ (fun x => by unfold Tier2.bit; split <;> norm_num))
  have hmean : ∫ ω, Tier2.bit (ω 0) ∂Tier2.tapeMeasure p = (p : ℝ) :=
    Tier2.observations_mean p 0
  have hbm : Measurable (fun ω : ℕ → Bool => ENNReal.ofReal (Tier2.bit (ω 0))) :=
    (Tier2.measurable_observations 0).ennreal_ofReal
  rw [lintegral_mul_const _ hbm, ← ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ (fun ω => bit_nonneg _)), hmean, ← ENNReal.ofReal_mul unitInterval.nonneg',
    ← ENNReal.ofReal_mul hc.le]
  apply le_of_eq
  congr 1
  field_simp

theorem levelProb_zero : levelProb 0 = 1 - rLevel := by simp [levelProb]

theorem gapParameter_false_val (d : Gap) :
    ((gapParameter false d : unitInterval) : ℝ) = 1/2 - (d : ℝ) := by
  simp [gapParameter]; ring

/-- At the Dirac magnitude law with every coin negative, the call law is one
geometric level and one tape with success probability `1/2-d`. -/
theorem negative_call_lintegral (d : Gap) (F : ℕ × (ℕ → Bool) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z, F z ∂callMeasure (Measure.dirac d) negativeSign) =
      ∫⁻ z, F z ∂levelMeasure.prod (Tier2.tapeMeasure (gapParameter false d)) := by
  have hp := populationInput_preserving (Measure.dirac d) levelMeasure (gapParameter false)
    (gapParameter true) (signUnit negativeSign) (measurable_gapParameter false)
    (measurable_gapParameter true) (measurable_signUnit negativeSign)
  change (∫⁻ z, F z ∂levelMeasure.prod
    (originalPopulationTapeLaw (Measure.dirac d) negativeSign)) = _
  unfold originalPopulationTapeLaw
  rw [← hp.lintegral_comp hF]
  unfold populationMeasure
  rw [population_lintegral (Measure.dirac d) levelMeasure _ _ _ (measurable_gapParameter false)
    (measurable_gapParameter true) (measurable_signUnit negativeSign) F hF, lintegral_dirac]
  simp [signUnit, negativeSign]

theorem observable713_noise_floor_proof : Observable713NoiseFloorStatement := by
  intro d hd
  have hI : Integrable (fun d : Gap => (d : ℝ)⁻¹) (Measure.dirac d) := integrable_dirac (by simp)
  have hmean := Observable713.output_mean (Measure.dirac d) negativeSign hI
  have hzero : signMean (Measure.dirac d) negativeSign.val = 0 := by
    simp [signMean, negativeSign]
  rw [hzero] at hmean
  have hc : 0 < 1 - rLevel := sub_pos.mpr rLevel_lt_one
  refine ⟨Observable713.output_memLp _ _ hI, hmean, ?_, div_pos (by linarith) hc⟩
  rw [evariance_eq_lintegral_ofReal, hmean]
  simp only [sub_zero]
  rw [Observable713.output_lintegral (Measure.dirac d) negativeSign
    (fun x : ℝ => ENNReal.ofReal (x^2)) (measurable_id.pow_const 2).ennreal_ofReal,
    negative_call_lintegral d _ (Observable713.measurable_callValue.pow_const 2).ennreal_ofReal]
  have h := level_zero_floor (decisions Tier2.observations)
    Observable713.measurable_classifierValue (fun ω => firstDecision_level_zero _ ω)
    (gapParameter false d)
  rw [gapParameter_false_val, levelProb_zero] at h
  exact h

theorem original_second_moment_floor_proof : OriginalSecondMomentFloorStatement := by
  intro d _
  have h := level_zero_floor
    (fun j ω => Tier2.Model.decision (fun k => dyadicMean Tier2.observations k ω) j)
    (fun l => Tier2.Model.measurable_decision _
      (fun _k => measurable_prefixMean Tier2.measurable_observations _) l)
    (fun ω => firstDecision_level_zero _ ω) (gapParameter false d)
  rw [gapParameter_false_val, levelProb_zero] at h
  exact h

theorem truncated_noise_floor_proof : TruncatedNoiseFloorStatement := by
  intro L d hd hd2
  let p := Tier2.coinParameter d false hd hd2.le
  have hc : 0 < 1 - rLevel := sub_pos.mpr rLevel_lt_one
  have hterm (l : ℕ) (hl : l ∈ Finset.range (L+1)) :
      0 ≤ (∑ x : Fin (2^L) → Bool, streamProb (coinP d false) x * (deltaK 1 1 l x)^2) /
        pLevel l := by
    have he := Tier2.deltaK_secondMoment_eq_integral L l
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)) p
    change (∑ x : Fin (2^L) → Bool, streamProb (p : ℝ) x * (deltaK 1 1 l x)^2) / pLevel l ≥ 0
    rw [he]
    exact div_nonneg (integral_nonneg (fun ω => sq_nonneg _))
      (mul_pos hc (pow_pos rLevel_pos l)).le
  have h0 : (∑ x : Fin (2^L) → Bool, streamProb (coinP d false) x * (deltaK 1 1 0 x)^2) /
      pLevel 0 = (1/2 - d) / (1 - rLevel) := by
    have he := Tier2.deltaK_secondMoment_eq_integral L 0 (Nat.zero_le L) p
    change (∑ x : Fin (2^L) → Bool, streamProb (p : ℝ) x * (deltaK 1 1 0 x)^2) / pLevel 0 = _
    rw [he]
    have hv (ω : ℕ → Bool) :
        (increment (fun j => Tier2.Model.decision
          (fun k => dyadicMean Tier2.observations k ω) j) 0)^2 = Tier2.bit (ω 0) := by
      simp only [increment]
      change (firstDecision _ (fun k => dyadicMean Tier2.observations k ω) 0)^2 = _
      rw [firstDecision_level_zero]
      cases ω 0 <;> simp [Tier2.bit]
    simp_rw [hv]
    have hmean : ∫ ω, Tier2.bit (ω 0) ∂Tier2.tapeMeasure p = (p : ℝ) :=
      Tier2.observations_mean p 0
    rw [hmean]
    simp [p, coinP, pLevel, sub_eq_add_neg]
  have hfloor : (1/2 - d) / (1 - rLevel) ≤ secondMomentK 1 1 L d false := by
    unfold secondMomentK
    rw [← h0]
    exact Finset.single_le_sum hterm (Finset.mem_range.mpr (Nat.succ_pos L))
  refine ⟨hfloor, ?_⟩
  rw [Proofs.lemma7_telescoping L d false 1 1]
  linarith

end ThresholdHC.LocalizationCounter
