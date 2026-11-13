import ThresholdHC.RobustContinuation.RaceOrder

/-! The error of a race under a law with larger gaps than its reference.

Let `π` be a coupling of reference gaps `z.1` and true gaps `z.2` with
`z.1 ≤ z.2`, and let the true population be the second marginal of `π` plus a
part `μ₀` that is coupled to no positive reference gap, such as the mass a
reference law has at zero. For a downward negative test and an upward positive
test, the population error of the race under the true law, with any sign law
of the true gaps, is at most the error at the coupled reference gaps with
the same signs, plus the mass of `μ₀`.

For the bank designed from a reference law `η`, with the first marginal of
`π` equal to `c η`, this gives

  `error ≤ ρ ε + c u + c ∫ ordinary error dη + μ₀(all gaps)`,

the bound of the known-law theorem with the reference law in the integral.
No coin of gap zero is needed: mass at zero in the reference is charged in
full through `μ₀`. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace ThresholdHC.RobustContinuation
open ThresholdHC ThresholdHC.Tier2 ThresholdHC.Tier6 ThresholdHC.ObservableSimulation
open ThresholdHC.BlindUpper ThresholdHC.EntropyTailUpper ThresholdHC.RareAboveTwo

/-- The error of the race at reference gaps `z.1` with the signs of the true
gaps `z.2`. -/
def coupledRaceError (π : Measure (Gap × Gap)) (q : SignLaw) (neg pos : PrefixTest) (L : ℕ) : ℝ :=
  ∫ z, q.val z.2 * raceConditionalError neg pos L true z.1 +
    (1 - q.val z.2) * raceConditionalError neg pos L false z.1 ∂π

theorem measurable_coupledIntegrand (q : SignLaw) (neg pos : PrefixTest) (L : ℕ) :
    Measurable (fun z : Gap × Gap => q.val z.2 * raceConditionalError neg pos L true z.1 +
      (1 - q.val z.2) * raceConditionalError neg pos L false z.1) :=
  ((q.property.1.comp measurable_snd).mul
      ((measurable_raceConditionalError neg pos L true).comp measurable_fst)).add
    ((measurable_const.sub (q.property.1.comp measurable_snd)).mul
      ((measurable_raceConditionalError neg pos L false).comp measurable_fst))

theorem integrable_coupledIntegrand (π : Measure (Gap × Gap)) [IsFiniteMeasure π] (q : SignLaw)
    (neg pos : PrefixTest) (L : ℕ) :
    Integrable (fun z : Gap × Gap => q.val z.2 * raceConditionalError neg pos L true z.1 +
      (1 - q.val z.2) * raceConditionalError neg pos L false z.1) π := by
  apply Integrable.of_bound (measurable_coupledIntegrand q neg pos L).aestronglyMeasurable 1
  refine ae_of_all _ fun z => ?_
  have ht : raceConditionalError neg pos L true z.1 ∈ Icc (0:ℝ) 1 :=
    ⟨measureReal_nonneg, measureReal_le_one⟩
  have hf : raceConditionalError neg pos L false z.1 ∈ Icc (0:ℝ) 1 :=
    ⟨measureReal_nonneg, measureReal_le_one⟩
  have hq := q.property.2 z.2
  rw [Real.norm_of_nonneg (add_nonneg (mul_nonneg hq.1 ht.1) (mul_nonneg (by linarith) hf.1))]
  nlinarith [mul_le_mul_of_nonneg_left ht.2 hq.1,
    mul_le_mul_of_nonneg_left hf.2 (by linarith : 0 ≤ 1 - q.val z.2)]

/-- Transfer of the error. Under a true law coupled above the reference
gaps, the population error of the race is at most its error at the coupled
reference gaps with the same signs, plus the uncoupled mass. -/
theorem coupled_population_error_le {neg pos : PrefixTest} (hneg : DownwardTest neg)
    (hpos : UpwardTest pos) (π : Measure (Gap × Gap)) [IsFiniteMeasure π]
    (hup : ∀ᵐ z ∂π, (z.1:ℝ) ≤ z.2) (μ₀ : Measure Gap) [IsFiniteMeasure μ₀] (q : SignLaw)
    (L : ℕ) :
    racePopulationError (π.map Prod.snd + μ₀) q neg pos L ≤
      coupledRaceError π q neg pos L + μ₀.real univ := by
  have hfm : Measurable (fun d : Gap => q.val d * raceConditionalError neg pos L true d +
      (1 - q.val d) * raceConditionalError neg pos L false d) :=
    (q.property.1.mul (measurable_raceConditionalError neg pos L true)).add
      ((measurable_const.sub q.property.1).mul (measurable_raceConditionalError neg pos L false))
  have hle1 : ∀ d : Gap, q.val d * raceConditionalError neg pos L true d +
      (1 - q.val d) * raceConditionalError neg pos L false d ≤ 1 := by
    intro d
    have ht : raceConditionalError neg pos L true d ≤ 1 := measureReal_le_one
    have hf : raceConditionalError neg pos L false d ≤ 1 := measureReal_le_one
    have hq := q.property.2 d
    nlinarith [mul_le_mul_of_nonneg_left ht hq.1,
      mul_le_mul_of_nonneg_left hf (by linarith : 0 ≤ 1 - q.val d)]
  unfold racePopulationError coupledRaceError
  rw [integral_add_measure (integrable_racePopulationError _ q neg pos L)
    (integrable_racePopulationError μ₀ q neg pos L),
    integral_map measurable_snd.aemeasurable hfm.aestronglyMeasurable]
  refine add_le_add ?_ ?_
  · refine integral_mono_ae ?_ (integrable_coupledIntegrand π q neg pos L) ?_
    · exact (integrable_map_measure hfm.aestronglyMeasurable measurable_snd.aemeasurable).mp
        (integrable_racePopulationError (π.map Prod.snd) q neg pos L)
    · filter_upwards [hup] with z hz
      have hq := q.property.2 z.2
      exact add_le_add
        (mul_le_mul_of_nonneg_left (raceConditionalError_antitone hneg hpos L true hz) hq.1)
        (mul_le_mul_of_nonneg_left (raceConditionalError_antitone hneg hpos L false hz)
          (by linarith))
  · have h := integral_mono (integrable_racePopulationError μ₀ q neg pos L)
      (integrable_const (1:ℝ)) hle1
    simpa using h

/-- The error of the bank designed from a reference law `η`, under a true
law coupled above `c η`: at most `ρ ε + c u + c ∫ ordinary error dη` plus the
uncoupled mass. -/
theorem robust_bank_population_error (η : Measure Gap) [IsProbabilityMeasure η]
    (π : Measure (Gap × Gap)) [IsFiniteMeasure π] (hup : ∀ᵐ z ∂π, (z.1:ℝ) ≤ z.2) {c : ℝ}
    (hc : 0 ≤ c) (href : π.map Prod.fst = ENNReal.ofReal c • η) (μ₀ : Measure Gap)
    [IsFiniteMeasure μ₀] (weights : ℕ → ℝ≥0) (hw : HasSum weights 1) {ε u ρ : ℝ} (hε : 0 ≤ ε)
    (hu : 0 ≤ u) (q : SignLaw) (hq : RarePrior (π.map Prod.snd + μ₀) ρ q) (L : ℕ) :
    racePopulationError (π.map Prod.snd + μ₀) q (negativeBankTest weights ε)
        (positiveBankTest η weights u) L ≤
      ρ*ε + c*u + c*(∫ d : Gap, ordinaryErrorKernel (Uniform713.cap L) (d:ℝ) ∂η) +
        μ₀.real univ := by
  set neg := negativeBankTest weights ε with hnegdef
  set pos := positiveBankTest η weights u with hposdef
  let o := fun d : Gap => ordinaryErrorKernel (Uniform713.cap L) (d:ℝ)
  let k := tapeEventProbability false (everPrefixHit pos)
  have hom : Measurable o := by
    change Measurable (fun d : Gap => ordinaryErrorKernel (Uniform713.cap L) (d:ℝ))
    unfold ordinaryErrorKernel
    fun_prop
  have hkm : Measurable k := measurable_tapeEventProbability false (measurableSet_everPrefixHit pos)
  have ho0 : ∀ d, 0 ≤ o d := fun d => by
    change 0 ≤ ordinaryErrorKernel (Uniform713.cap L) (d:ℝ)
    unfold ordinaryErrorKernel
    positivity
  have ho1 : ∀ d, o d ≤ 1 := fun d => min_le_left _ _
  have hk0 : ∀ d, 0 ≤ k d := fun d => measureReal_nonneg
  have hk1 : ∀ d, k d ≤ 1 := fun d => measureReal_le_one
  have hqm := q.property.1
  have hbound : ∀ {ν : Measure Gap} [IsFiniteMeasure ν] {f : Gap → ℝ}, Measurable f →
      (∀ d, 0 ≤ f d) → (∀ d, f d ≤ 1) → Integrable f ν := by
    intro ν _ f hf h0 h1
    apply Integrable.of_bound hf.aestronglyMeasurable 1
    exact ae_of_all _ fun d => by rw [Real.norm_of_nonneg (h0 d)]; exact h1 d
  have hqi : ∀ {ν : Measure Gap} [IsFiniteMeasure ν], Integrable q.val ν := fun {ν} _ =>
    hbound hqm (fun d => (q.property.2 d).1) (fun d => (q.property.2 d).2)
  have htransfer := coupled_population_error_le (negativeBankTest_downward weights hε)
    (positiveBankTest_upward η weights u) π hup μ₀ q L
  refine htransfer.trans (add_le_add ?_ le_rfl)
  -- The error at the reference gaps, coin by coin.
  have hpoint : ∀ z : Gap × Gap, q.val z.2 * raceConditionalError neg pos L true z.1 +
      (1 - q.val z.2) * raceConditionalError neg pos L false z.1 ≤
      ε * q.val z.2 + o z.1 + k z.1 := by
    intro z
    have hq := q.property.2 z.2
    have h1 : raceConditionalError neg pos L true z.1 ≤ ε + o z.1 :=
      (race_error_positive_bound neg pos L z.1).trans
        (add_le_add (negative_bank_probability weights hw hε z.1) le_rfl)
    have h2 : raceConditionalError neg pos L false z.1 ≤ k z.1 + o z.1 :=
      race_error_negative_bound neg pos L z.1
    nlinarith [mul_le_mul_of_nonneg_left h1 hq.1,
      mul_le_mul_of_nonneg_left h2 (by linarith : 0 ≤ 1 - q.val z.2),
      mul_nonneg hq.1 (hk0 z.1)]
  have hi1 : Integrable (fun z : Gap × Gap => q.val z.2) π :=
    (integrable_map_measure hqm.aestronglyMeasurable measurable_snd.aemeasurable).mp hqi
  have hi2 : Integrable (fun z : Gap × Gap => o z.1) π :=
    (integrable_map_measure hom.aestronglyMeasurable measurable_fst.aemeasurable).mp
      (hbound hom ho0 ho1)
  have hi3 : Integrable (fun z : Gap × Gap => k z.1) π :=
    (integrable_map_measure hkm.aestronglyMeasurable measurable_fst.aemeasurable).mp
      (hbound hkm hk0 hk1)
  have hi0 : Integrable (fun z : Gap × Gap => ε * q.val z.2) π := hi1.const_mul ε
  have hi12 : Integrable (fun z : Gap × Gap => ε * q.val z.2 + o z.1) π := hi0.add hi2
  have hi : Integrable (fun z : Gap × Gap => ε * q.val z.2 + o z.1 + k z.1) π := hi12.add hi3
  have hsum := integral_mono (integrable_coupledIntegrand π q neg pos L) hi hpoint
  have hsplit : (∫ z : Gap × Gap, ε * q.val z.2 + o z.1 + k z.1 ∂π) =
      ε * (∫ z : Gap × Gap, q.val z.2 ∂π) + (∫ z : Gap × Gap, o z.1 ∂π) +
        ∫ z : Gap × Gap, k z.1 ∂π := by
    rw [integral_add hi12 hi3, integral_add hi0 hi2, integral_const_mul]
  rw [hsplit] at hsum
  -- The three integrals.
  have hA : (∫ z : Gap × Gap, q.val z.2 ∂π) ≤ ρ := by
    have hmap : (∫ z : Gap × Gap, q.val z.2 ∂π) = ∫ d, q.val d ∂(π.map Prod.snd) :=
      (integral_map measurable_snd.aemeasurable hqm.aestronglyMeasurable).symm
    have hadd : signMean (π.map Prod.snd + μ₀) q.val =
        (∫ d, q.val d ∂(π.map Prod.snd)) + ∫ d, q.val d ∂μ₀ := integral_add_measure hqi hqi
    have h0 : 0 ≤ ∫ d, q.val d ∂μ₀ := integral_nonneg fun d => (q.property.2 d).1
    have hq' : signMean (π.map Prod.snd + μ₀) q.val ≤ ρ := hq
    linarith
  have hB : (∫ z : Gap × Gap, o z.1 ∂π) = c * ∫ d, o d ∂η := by
    rw [← integral_map measurable_fst.aemeasurable hom.aestronglyMeasurable, href,
      integral_smul_measure, ENNReal.toReal_ofReal hc, smul_eq_mul]
  have hC : (∫ z : Gap × Gap, k z.1 ∂π) ≤ c * u := by
    rw [← integral_map measurable_fst.aemeasurable hkm.aestronglyMeasurable, href,
      integral_smul_measure, ENNReal.toReal_ofReal hc, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (positive_bank_integrated_probability η weights hw hu) hc
  change coupledRaceError π q neg pos L ≤ _
  unfold coupledRaceError
  have hε' : ε * (∫ z : Gap × Gap, q.val z.2 ∂π) ≤ ρ * ε := by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right hA hε
  rw [hB] at hsum
  change (∫ z : Gap × Gap, q.val z.2 * raceConditionalError neg pos L true z.1 +
    (1 - q.val z.2) * raceConditionalError neg pos L false z.1 ∂π) ≤
      ρ*ε + c*u + c*(∫ d : Gap, o d ∂η)
  linarith

end ThresholdHC.RobustContinuation
