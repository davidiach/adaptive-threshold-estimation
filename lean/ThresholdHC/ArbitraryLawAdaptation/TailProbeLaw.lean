import ThresholdHC.ArbitraryLawAdaptation.TailProbeProbability
import ThresholdHC.ArbitraryLawAdaptation.TailTestLaw

/-! The tail probe on fresh coins of the original population.

The coin array of the original simulation law is a stream of independent
tapes with the actual population tape law. On that stream, for every
probability law `μ` of positive gaps and every measurable gap-dependent sign
law:

* with probability at least `7/8` the certificate is at least
  `F(2^{-J}) = μ((0, 2^{-J}])` at every flip budget and every coin cap;
* at a fixed budget `b` and coin cap `M`, with probability at least `3/4` it
  is at most `min{1, 128 max(u_J, W_J/b, 1/M)}`, where `u_J` is the unresolved
  mass and `W_J = ∫ w_J dμ`.

No inverse moment of `μ` and no candidate family is assumed. -/

noncomputable section
open MeasureTheory Real
namespace ThresholdHC.ArbitraryLawAdaptation
open ThresholdHC.Tier2 ThresholdHC.Tier6 ThresholdHC.CriticalEntropy
open ThresholdHC.ObservableSimulation

/-- The stream of fresh coins is the coin array of the original simulation
law, for every adaptive estimator. -/
theorem originalSimulationLaw_coins {R : Type} [MeasurableSpace R] (μ : Measure Gap)
    [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (q : SignLaw) :
    (originalSimulationLaw μ A q).map Prod.snd =
      Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q) := by
  unfold originalSimulationLaw
  rw [Measure.map_snd_prod, measure_univ, one_smul]

theorem one_le_tailWorkEnvelope (J : ℕ) (d : Gap) : 1 ≤ tailWorkEnvelope J d := by
  have hd0 : (0 : ℝ) < d := d.property.1
  have hd1 : (d : ℝ) ≤ 1 / 2 := d.property.2
  have hlog := tailLog_nonneg J (d : ℝ)
  have hsq : (d : ℝ) ^ 2 ≤ 1 := by nlinarith
  have h1 : 1 ≤ 1024 / (d : ℝ) ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  unfold tailWorkEnvelope
  refine le_min (one_le_pow₀ (by norm_num)) ?_
  nlinarith

/-- `W_J ≥ 1`: one coin costs at least one flip. -/
theorem one_le_tailWorkEnvelope_integral (μ : Measure Gap) [IsProbabilityMeasure μ] (J : ℕ) :
    1 ≤ ∫ d : Gap, tailWorkEnvelope J d ∂μ := by
  have hr : Integrable (fun d : Gap => tailWorkEnvelope J d) μ :=
    ThresholdHC.Tier5.integrable_of_abs_bound μ _
      ((measurable_tailWorkEnvelope J).comp measurable_subtype_coe) (4 ^ J) fun d => by
        rw [abs_of_nonneg (tailWorkEnvelope_nonneg J d)]
        exact tailWorkEnvelope_le J d
  have h := integral_mono (integrable_const (1 : ℝ)) hr fun d => one_le_tailWorkEnvelope J d
  simpa using h

/-- Validity on the original population. With probability at least `7/8` the
certificate covers the small-gap mass `F(2^{-J})` at every flip budget and
every coin cap simultaneously, for every sign law. -/
theorem original_probe_valid (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (J : ℕ) :
    7 / 8 ≤ (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)).real
      {ω | ∀ b M, μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ J} ≤
        probeUpper (probeCompleted J b M ω)} := by
  apply stream_probe_valid (originalPopulationTapeLaw μ q) J measureReal_le_one
  rw [original_tail_unresolved μ q J]
  have h := tail_unresolved_mass_lower μ J
  linarith

/-- Performance on the original population, with the coin cap. At a fixed
flip budget `b ≥ 1` and coin cap `M ≥ 1`, with probability at least `3/4` the
certificate is at most `min{1, 128 max(u_J, W_J/b, 1/M)}`. -/
theorem original_probe_performance (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (J b M : ℕ) (hb : 0 < b) (hM : 0 < M) :
    3 / 4 ≤ (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)).real
      {ω | probeUpper (probeCompleted J b M ω) ≤
        min 1 (128 * max (max (tailUnresolvedMass μ J)
          ((∫ d : Gap, tailWorkEnvelope J d ∂μ) / b)) (1 / M))} := by
  have h := stream_probe_performance (originalPopulationTapeLaw μ q) J b M hb hM
    (original_tail_expected_work μ q J)
  rwa [original_tail_unresolved μ q J] at h

/-- Performance without a coin cap: a cap of at least the flip budget is
inactive, and the bound is `min{1, 128 max(u_J, W_J/b)}`. -/
theorem original_probe_performance_uncapped (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (J b M : ℕ) (hb : 0 < b) (hbM : b ≤ M) :
    3 / 4 ≤ (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)).real
      {ω | probeUpper (probeCompleted J b M ω) ≤
        min 1 (128 * max (tailUnresolvedMass μ J)
          ((∫ d : Gap, tailWorkEnvelope J d ∂μ) / b))} := by
  have h := original_probe_performance μ q J b M hb (hb.trans_le hbM)
  have hW := one_le_tailWorkEnvelope_integral μ J
  have hb' : (0 : ℝ) < b := Nat.cast_pos.mpr hb
  have hM' : (0 : ℝ) < M := Nat.cast_pos.mpr (hb.trans_le hbM)
  have hbM' : (b : ℝ) ≤ M := Nat.cast_le.mpr hbM
  have hle : 1 / (M : ℝ) ≤ (∫ d : Gap, tailWorkEnvelope J d ∂μ) / b :=
    calc 1 / (M : ℝ) ≤ 1 / b := one_div_le_one_div_of_le hb' hbM'
      _ ≤ (∫ d : Gap, tailWorkEnvelope J d ∂μ) / b := div_le_div_of_nonneg_right hW hb'.le
  rwa [max_eq_left (hle.trans (le_max_right _ _))] at h

end ThresholdHC.ArbitraryLawAdaptation
