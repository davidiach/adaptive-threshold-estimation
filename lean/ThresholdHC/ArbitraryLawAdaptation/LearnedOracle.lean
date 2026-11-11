import ThresholdHC.ArbitraryLawAdaptation.LearnedCDF
import ThresholdHC.ArbitraryLawAdaptation.CDFSelection
import ThresholdHC.ArbitraryLawAdaptation.DominatedMass

/-! The learned law retains the oracle rate: (A11).

Let `μ' = L(V D / 2)` and let `e` be the slack of (A13). The witness `λ` is
the lowest unit mass of the finite measure `128 μ' + e δ₀`: its mass at zero
is `min{1, e}`, and the rest is the lowest-gap part of `128 μ'`, with a
fraction of a boundary atom. It is a probability law dominated by
`128 μ' + e δ₀`, and its distribution function is `min{1, 128 F_{μ'} + e}`.
By (A13) the learned law `μ̄` lies above `λ` in the distribution order, so

  `K_{μ̄} ≤ √3 K_λ ≤ √3 (128 K_{μ'} + e) ≤ √3 (4096 K_μ + 2^22 K_μ) < 2^24 K_μ`

by the CDF comparison (A2), dominated mass (A5), the light contraction (A3)
and (A14). `K` of a law with mass at zero is the zero-extended selection
functional, which keeps the infimum over all fractional selections. The
witness, `μ'` and the onset are proof quantities. -/

noncomputable section
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
namespace ThresholdHC.ArbitraryLawAdaptation
open ThresholdHC.Tier2 ThresholdHC.Tier6 ThresholdHC.EntropyTailQuantile
open ThresholdHC.CriticalEntropy ThresholdHC.ObservableSimulation

/-- The distribution function of the lowest-gap quantile part of mass `r`:
`min{r, F(x)}`. -/
theorem quantileTail_cdf (η : Measure Gap) [IsProbabilityMeasure η] {r : ℝ} (hr : 0 < r)
    (hr1 : r ≤ 1) (x : ℝ) :
    (quantileTail η r).real {d : Gap | (d : ℝ) ≤ x} =
      min r (η.real {d : Gap | (d : ℝ) ≤ x}) := by
  have hS : MeasurableSet {d : Gap | (d : ℝ) ≤ x} :=
    measurableSet_le measurable_subtype_coe measurable_const
  obtain ⟨-, -, hmass, hbelow⟩ := quantileThreshold_properties η hr hr1
  by_cases hx : x < quantileThreshold η r
  · rw [min_eq_right (hbelow x hx).le]
    have h1 : {d : Gap | (d : ℝ) ≤ x} ∩ {d : Gap | (d : ℝ) < quantileThreshold η r} =
        {d : Gap | (d : ℝ) ≤ x} :=
      Set.inter_eq_left.mpr fun d (hd : (d : ℝ) ≤ x) => lt_of_le_of_lt hd hx
    have h2 : {d : Gap | (d : ℝ) ≤ x} ∩ {d : Gap | (d : ℝ) = quantileThreshold η r} = ∅ := by
      ext d
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro hd he
      rw [he] at hd
      exact absurd hd (not_le.mpr hx)
    unfold quantileTail
    rw [measureReal_def, Measure.add_apply, Measure.smul_apply, Measure.restrict_apply hS,
      Measure.restrict_apply hS, h1, h2, measure_empty, smul_zero, add_zero]
    rfl
  · have htx : quantileThreshold η r ≤ x := not_lt.mp hx
    have hge : r ≤ η.real {d : Gap | (d : ℝ) ≤ x} :=
      hmass.trans (measureReal_mono fun d (hd : (d : ℝ) ≤ quantileThreshold η r) =>
        le_trans hd htx)
    rw [min_eq_left hge]
    have hnull : quantileTail η r {d : Gap | (d : ℝ) ≤ x}ᶜ = 0 := by
      have h := quantileTail_support η r
      rw [ae_iff] at h
      exact measure_mono_null
        (fun d (hd : ¬ (d : ℝ) ≤ x) => fun hle : (d : ℝ) ≤ quantileThreshold η r =>
          hd (le_trans hle htx)) h
    have hfull : quantileTail η r {d : Gap | (d : ℝ) ≤ x} = ENNReal.ofReal r := by
      rw [← quantileTail_mass η hr hr1, ← measure_add_measure_compl hS, hnull, add_zero]
    rw [measureReal_def, hfull, ENNReal.toReal_ofReal hr.le]

/-- The lowest unit mass of the finite measure `128 η + e δ₀` on the real
line, for a law `η` of positive gaps. Its mass at zero is `min{1, e}`, and the
rest is `128` times the lowest-gap quantile part of `η` of mass `(1 - e)/128`,
which splits a boundary atom. -/
def clippedLaw (η : Measure Gap) (e : ℝ) : Measure ℝ :=
  if 1 ≤ e then Measure.dirac 0
  else ENNReal.ofReal e • Measure.dirac 0 +
    (128 : ℝ≥0∞) • (quantileTail η ((1 - e) / 128)).map Subtype.val

/-- The witness is dominated by `128 η + e δ₀`. -/
theorem clippedLaw_le (η : Measure Gap) [IsProbabilityMeasure η] {e : ℝ} (he : 0 ≤ e) :
    clippedLaw η e ≤
      ENNReal.ofReal 128 • η.map Subtype.val + ENNReal.ofReal e • Measure.dirac 0 := by
  unfold clippedLaw
  by_cases h1 : 1 ≤ e
  · rw [ite_eq_left h1]
    have hone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal e := by
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal h1
    calc (Measure.dirac 0 : Measure ℝ) = (1 : ℝ≥0∞) • Measure.dirac 0 := (one_smul _ _).symm
      _ ≤ ENNReal.ofReal e • Measure.dirac 0 := fun s => by
          simp only [Measure.smul_apply, smul_eq_mul]
          gcongr
      _ ≤ ENNReal.ofReal 128 • η.map Subtype.val + ENNReal.ofReal e • Measure.dirac 0 :=
          Measure.le_add_left le_rfl
  · rw [ite_eq_right h1]
    have hr : 0 < (1 - e) / 128 := by
      have : 0 < 1 - e := by linarith [not_le.mp h1]
      positivity
    have hr1 : (1 - e) / 128 ≤ 1 := by linarith
    have hq : (quantileTail η ((1 - e) / 128)).map Subtype.val ≤ η.map Subtype.val :=
      Measure.map_mono (quantileTail_le η hr hr1) measurable_subtype_coe
    rw [add_comm, ENNReal.ofReal_ofNat]
    refine add_le_add (fun s => ?_) le_rfl
    simp only [Measure.smul_apply, smul_eq_mul]
    gcongr

/-- The witness is a probability law. -/
theorem clippedLaw_probability (η : Measure Gap) [IsProbabilityMeasure η] {e : ℝ} (he : 0 ≤ e) :
    IsProbabilityMeasure (clippedLaw η e) := by
  unfold clippedLaw
  by_cases h1 : 1 ≤ e
  · rw [ite_eq_left h1]
    infer_instance
  · rw [ite_eq_right h1]
    have hr : 0 < (1 - e) / 128 := by
      have : 0 < 1 - e := by linarith [not_le.mp h1]
      positivity
    have hr1 : (1 - e) / 128 ≤ 1 := by linarith
    constructor
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, measure_univ,
      Measure.map_apply measurable_subtype_coe MeasurableSet.univ, Set.preimage_univ,
      quantileTail_mass η hr hr1, smul_eq_mul, smul_eq_mul, mul_one,
      ← ENNReal.ofReal_ofNat 128, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_add he (by positivity),
      show e + 128 * ((1 - e) / 128) = 1 by ring, ENNReal.ofReal_one]

/-- The distribution function of the witness on the nonnegative half-line:
`min{1, 128 F_η(x) + e}`. -/
theorem clippedLaw_Iic (η : Measure Gap) [IsProbabilityMeasure η] {e : ℝ} (he : 0 ≤ e) {x : ℝ}
    (hx : 0 ≤ x) :
    clippedLaw η e (Set.Iic x) =
      ENNReal.ofReal (min 1 (128 * η.real {d : Gap | (d : ℝ) ≤ x} + e)) := by
  have hF0 : 0 ≤ η.real {d : Gap | (d : ℝ) ≤ x} := measureReal_nonneg
  unfold clippedLaw
  by_cases h1 : 1 ≤ e
  · rw [ite_eq_left h1, min_eq_left (by linarith), ENNReal.ofReal_one]
    exact Measure.dirac_apply_of_mem (Set.mem_Iic.mpr hx)
  · rw [ite_eq_right h1]
    have hr : 0 < (1 - e) / 128 := by
      have : 0 < 1 - e := by linarith [not_le.mp h1]
      positivity
    have hr1 : (1 - e) / 128 ≤ 1 := by linarith
    have : IsFiniteMeasure (quantileTail η ((1 - e) / 128)) :=
      isFiniteMeasure_of_le η (quantileTail_le η hr hr1)
    have hq : (quantileTail η ((1 - e) / 128)).map Subtype.val (Set.Iic x) =
        ENNReal.ofReal (min ((1 - e) / 128) (η.real {d : Gap | (d : ℝ) ≤ x})) := by
      rw [Measure.map_apply measurable_subtype_coe measurableSet_Iic,
        ← quantileTail_cdf η hr hr1 x, ofReal_measureReal]
      rfl
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, hq,
      Measure.dirac_apply_of_mem (Set.mem_Iic.mpr hx), smul_eq_mul, smul_eq_mul, mul_one,
      ← ENNReal.ofReal_ofNat 128, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_add he (mul_nonneg (by norm_num) (le_min hr.le hF0))]
    congr 1
    rcases le_total ((1 - e) / 128) (η.real {d : Gap | (d : ℝ) ≤ x}) with h | h
    · rw [min_eq_left h, min_eq_left (by linarith)]
      ring
    · rw [min_eq_right h, min_eq_right (by linarith)]
      ring

/-- The witness puts no mass on the negative half-line. -/
theorem clippedLaw_Iio_zero (η : Measure Gap) (e : ℝ) : clippedLaw η e (Set.Iio 0) = 0 := by
  have hpre : (Subtype.val : Gap → ℝ) ⁻¹' Set.Iio 0 = ∅ := by
    ext d
    simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_empty_iff_false, iff_false, not_lt]
    exact d.property.1.le
  have hd : (Measure.dirac (0 : ℝ)) (Set.Iio 0) = 0 := by
    rw [Measure.dirac_apply' _ measurableSet_Iio]
    simp
  unfold clippedLaw
  split_ifs
  · exact hd
  · rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, hd,
      Measure.map_apply measurable_subtype_coe measurableSet_Iio, hpre, measure_empty,
      smul_zero, smul_zero, add_zero]

/-- The distribution function of the witness, as a real function, on the
nonnegative half-line. -/
theorem clippedLaw_cdf (η : Measure Gap) [IsProbabilityMeasure η] {e : ℝ} (he : 0 ≤ e) {x : ℝ}
    (hx : 0 ≤ x) :
    cdf (clippedLaw η e) x = min 1 (128 * η.real {d : Gap | (d : ℝ) ≤ x} + e) := by
  have := clippedLaw_probability η he
  have hF0 : 0 ≤ η.real {d : Gap | (d : ℝ) ≤ x} := measureReal_nonneg
  rw [cdf_eq_real, measureReal_def, clippedLaw_Iic η he hx,
    ENNReal.toReal_ofReal (le_min zero_le_one (by linarith))]

/-- Above the first grid point the envelope's distribution function is its
total mass. -/
theorem envelopeCDF_top (c : ℕ → ℝ) (n : ℕ) {x : ℝ} (hx : gridPoint 1 ≤ x) :
    envelopeCDF c n x = c 0 := by
  have hx0 : 0 ≤ x := (gridPoint_pos 1).le.trans hx
  have hall (i : Fin n) : gridPoint (i.val + 1) ≤ x :=
    (gridPoint_antitone (by omega : 1 ≤ i.val + 1)).trans hx
  simp only [envelopeCDF, ite_eq_left hx0, ite_eq_left (hall _)]
  exact envelope_weights_sum c n

/-- The finite envelope law puts no mass on the negative half-line. -/
theorem envelopeLaw_Iio_zero (c : ℕ → ℝ) (n : ℕ) : envelopeLaw c n (Set.Iio 0) = 0 := by
  have hd (y : ℝ) (hy : 0 ≤ y) : (Measure.dirac y) (Set.Iio (0 : ℝ)) = 0 := by
    rw [Measure.dirac_apply' _ measurableSet_Iio]
    exact Set.indicator_of_notMem (by simpa using hy) _
  unfold envelopeLaw
  rw [Measure.add_apply, Measure.smul_apply, hd 0 le_rfl, smul_zero, zero_add,
    Measure.finsetSum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Measure.smul_apply, hd _ (gridPoint_pos _).le, smul_zero]

/-- (A11), deterministic form. Let `U` be certificates with `U 0 = 1` that
satisfy the upper half of (A8) at every depth `i + 1 ≤ J`. Under the pilot's
onset condition, the selection functional of the law learned from them is at
most `2^24` times the oracle's; `16777216 = 2^24`. The selection functional
of the learned law, which has mass at zero, is the zero-extended one, with
the infimum over all fractional selections. -/
theorem learned_selection_le (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 < ρ)
    (hρ4 : ρ ≤ 1 / 4) {J : ℕ} (hJ : 1 ≤ J) (hon : PilotOnset μ ρ J) (U : ℕ → ℝ)
    (hU0 : ∀ i, 0 ≤ U i) (hU1 : U 0 = 1)
    (hbound : ∀ i, i < J → U i ≤ pilotBound μ J ρ (i + 1)) :
    zeroSelection (envelopeLaw (prefixMinimum U) (J - 1)) ρ (4 ^ J) ≤
      16777216 * EntropyTail.selection μ ρ (4 ^ J) := by
  have hρ1 : ρ ≤ 1 := by linarith
  have hc0 : ∀ j, 0 ≤ prefixMinimum U j := prefixMinimum_nonneg hU0
  have hmono : Antitone (prefixMinimum U) := prefixMinimum_antitone U
  have he0 : 0 ≤ learnedSlack μ ρ J (prefixMinimum U (J - 1)) :=
    (hc0 (J - 1)).trans (le_learnedSlack μ ρ J _)
  have hlearned : IsProbabilityMeasure (envelopeLaw (prefixMinimum U) (J - 1)) :=
    learnedEnvelope_probability hU0 hU1 (J - 1)
  have hwitness : IsProbabilityMeasure
      (clippedLaw (lightLaw μ) (learnedSlack μ ρ J (prefixMinimum U (J - 1)))) :=
    clippedLaw_probability (lightLaw μ) he0
  -- Both laws have full mass on `[0, 1/2]`.
  have hgrid : gridPoint 1 ≤ (1 / 2 : ℝ) := by
    unfold gridPoint
    norm_num
  have hhalf_learned : cdf (envelopeLaw (prefixMinimum U) (J - 1)) (1 / 2) = 1 := by
    rw [cdf_eq_real, measureReal_def, envelopeLaw_Iic hc0 hmono, envelopeCDF_top _ _ hgrid]
    change (ENNReal.ofReal (U 0)).toReal = 1
    rw [hU1, ENNReal.ofReal_one, ENNReal.toReal_one]
  have hfull : (lightLaw μ).real {d : Gap | (d : ℝ) ≤ 1 / 2} = 1 := by
    have hu : {d : Gap | (d : ℝ) ≤ 1 / 2} = Set.univ :=
      Set.eq_univ_of_forall fun d => d.property.2
    rw [hu, measureReal_def, measure_univ, ENNReal.toReal_one]
  have hhalf_witness : cdf (clippedLaw (lightLaw μ)
      (learnedSlack μ ρ J (prefixMinimum U (J - 1)))) (1 / 2) = 1 := by
    rw [clippedLaw_cdf (lightLaw μ) he0 (by norm_num), hfull]
    exact min_eq_left (by linarith)
  -- (A13): the witness lies below the learned law in the distribution order.
  have hdom : ∀ x, cdf (envelopeLaw (prefixMinimum U) (J - 1)) x ≤
      cdf (clippedLaw (lightLaw μ) (learnedSlack μ ρ J (prefixMinimum U (J - 1)))) x := by
    intro x
    by_cases hx : 0 ≤ x
    · have hF0 : 0 ≤ (lightLaw μ).real {d : Gap | (d : ℝ) ≤ x} := measureReal_nonneg
      rw [clippedLaw_cdf (lightLaw μ) he0 hx, cdf_eq_real, measureReal_def]
      exact ENNReal.toReal_le_of_le_ofReal (le_min zero_le_one (by linarith))
        (learned_cdf_le μ hρ hρ1 U hU0 hU1 hbound x)
    · have hzero : envelopeLaw (prefixMinimum U) (J - 1) (Set.Iic x) = 0 :=
        measure_mono_null (fun y (hy : y ≤ x) => lt_of_le_of_lt hy (not_le.mp hx))
          (envelopeLaw_Iio_zero _ _)
      rw [cdf_eq_real, measureReal_def, hzero, ENNReal.toReal_zero]
      exact cdf_nonneg _ x
  -- (A2), (A5), (A3) and (A14).
  have hcoupling := zeroSelection_le_sqrt_three_of_cdf
    (clippedLaw (lightLaw μ) (learnedSlack μ ρ J (prefixMinimum U (J - 1))))
    (envelopeLaw (prefixMinimum U) (J - 1)) (clippedLaw_Iio_zero _ _) (envelopeLaw_Iio_zero _ _)
    hhalf_witness hhalf_learned hdom ρ (4 ^ J)
  have hmass := zeroSelection_dominated_mass (by norm_num : (1 : ℝ) ≤ 128)
    (clippedLaw_le (lightLaw μ) he0) ρ (4 ^ J)
  have hlight : zeroSelection ((lightLaw μ).map Subtype.val) ρ (4 ^ J) ≤
      32 * EntropyTail.selection μ ρ (4 ^ J) := by
    rw [zeroSelection_map]
    exact selection_lightMultiplier μ ρ (4 ^ J)
  have hslack := learnedSlack_le_oracle μ hρ hρ4 hJ hon U (by
    have h := hbound (J - 1) (by omega)
    rwa [Nat.sub_add_cancel hJ] at h)
  have hsqrt : ENNReal.ofReal (Real.sqrt 3) ≤ 2 := by
    rw [← ENNReal.ofReal_ofNat 2]
    exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩)
  calc zeroSelection (envelopeLaw (prefixMinimum U) (J - 1)) ρ (4 ^ J)
      ≤ ENNReal.ofReal (Real.sqrt 3) * zeroSelection
          (clippedLaw (lightLaw μ) (learnedSlack μ ρ J (prefixMinimum U (J - 1)))) ρ (4 ^ J) :=
        hcoupling
    _ ≤ 2 * (ENNReal.ofReal 128 * zeroSelection ((lightLaw μ).map Subtype.val) ρ (4 ^ J) +
          ENNReal.ofReal (learnedSlack μ ρ J (prefixMinimum U (J - 1)))) := by gcongr
    _ ≤ 2 * (128 * (32 * EntropyTail.selection μ ρ (4 ^ J)) +
          4194304 * EntropyTail.selection μ ρ (4 ^ J)) := by
        rw [ENNReal.ofReal_ofNat]
        gcongr
    _ = (2 * (128 * 32 + 4194304)) * EntropyTail.selection μ ρ (4 ^ J) := by ring
    _ ≤ 16777216 * EntropyTail.selection μ ρ (4 ^ J) := by
        gcongr
        norm_num

/-- (A11) with its finite onset. There is a depth `J₀ ≥ 1`, depending on the
gap law and the rarity only, such that the comparison holds at every target
depth `J ≥ J₀` for all certificates that satisfy the upper half of (A8). -/
theorem learned_selection_eventually (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ}
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) :
    ∃ J₀ : ℕ, 1 ≤ J₀ ∧ ∀ (J : ℕ) (U : ℕ → ℝ), J₀ ≤ J → (∀ i, 0 ≤ U i) → U 0 = 1 →
      (∀ i, i < J → U i ≤ pilotBound μ J ρ (i + 1)) →
      zeroSelection (envelopeLaw (prefixMinimum U) (J - 1)) ρ (4 ^ J) ≤
        16777216 * EntropyTail.selection μ ρ (4 ^ J) := by
  obtain ⟨J₀, hJ₀⟩ := pilotOnset_eventually μ hρ (by linarith : ρ ≤ 1)
  refine ⟨max J₀ 1, le_max_right _ _, fun J U hJ hU0 hU1 hbound => ?_⟩
  exact learned_selection_le μ hρ hρ4 ((le_max_right _ _).trans hJ)
    (hJ₀ J ((le_max_left _ _).trans hJ)) U hU0 hU1 hbound

variable {R : Type} [MeasurableSpace R]

/-- (A11) for the pilot in the learning stage, on an observed word. When the
certificates the stage reads off the word satisfy the upper half of (A8), the
stage's learned law has selection functional at most `2^24` times the
oracle's. -/
theorem pilotStage_selection_le (μ : Measure Gap) [IsProbabilityMeasure μ] (S : LearnedStage R)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) {J : ℕ} (hJ : 1 ≤ J) (hon : PilotOnset μ ρ J)
    (m : ℕ) (xs : List Bool)
    (hbound : ∀ i, i < J → (pilotStage S J m ρ).upper xs i ≤ pilotBound μ J ρ (i + 1)) :
    zeroSelection ((pilotStage S J m ρ).learnedLaw xs) ρ (4 ^ J) ≤
      16777216 * EntropyTail.selection μ ρ (4 ^ J) :=
  learned_selection_le μ hρ hρ4 hJ hon (pilotUpper J m (pilotCoinCap J ρ) xs)
    (pilotUpper_nonneg J m _ xs) (pilotUpper_zero J m _ xs) hbound

/-- (A11) on the pilot event. Under the pilot's onset condition and with
`m ≥ 8 log(2J/ε)` probes at every depth, with probability at least `1 - ε`
on the coin array of the original simulation law, the stage's learned law
dominates the gap law in distribution and its selection functional is at most
`2^24` times the oracle's. -/
theorem original_pilotStage_oracle (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (S : LearnedStage R) (J m : ℕ) {ρ ε : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) (hJ : 1 ≤ J)
    (hon : PilotOnset μ ρ J) (hm : 0 < m) (hε : 0 < ε)
    (hmε : 8 * log (2 * (J : ℝ) / ε) ≤ m) :
    1 - ε ≤
      (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)).real
        {ω | (∀ x : ℝ, (μ.map Subtype.val) (Set.Iic x) ≤
            (pilotStage S J m ρ).learnedLaw (pilotStageWord J m ρ ω) (Set.Iic x)) ∧
          zeroSelection ((pilotStage S J m ρ).learnedLaw (pilotStageWord J m ρ ω)) ρ (4 ^ J) ≤
            16777216 * EntropyTail.selection μ ρ (4 ^ J)} := by
  refine (original_pilotStage_event μ q S J m hρ hJ hm hε hmε).trans (measureReal_mono ?_)
  intro ω hω
  exact ⟨hω.2, pilotStage_selection_le μ S hρ hρ4 hJ hon m _ fun i hi => (hω.1 i hi).2⟩

/-- (A11) on the pilot event, with its finite onset. There is a depth `J₀`,
depending on the gap law and the rarity only, such that for every target
depth `J ≥ J₀`, every sign law, every stage and every `m ≥ 8 log(2J/ε)`, the
event of `original_pilotStage_oracle` has probability at least `1 - ε`. -/
theorem original_pilotStage_oracle_eventually (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ : ℝ}
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) :
    ∃ J₀ : ℕ, ∀ (q : SignLaw) (S : LearnedStage R) (J m : ℕ) {ε : ℝ}, J₀ ≤ J → 0 < m →
      0 < ε → 8 * log (2 * (J : ℝ) / ε) ≤ m →
      1 - ε ≤
        (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)).real
          {ω | (∀ x : ℝ, (μ.map Subtype.val) (Set.Iic x) ≤
              (pilotStage S J m ρ).learnedLaw (pilotStageWord J m ρ ω) (Set.Iic x)) ∧
            zeroSelection ((pilotStage S J m ρ).learnedLaw (pilotStageWord J m ρ ω)) ρ
                (4 ^ J) ≤
              16777216 * EntropyTail.selection μ ρ (4 ^ J)} := by
  obtain ⟨J₀, hJ₀⟩ := pilotOnset_eventually μ hρ (by linarith : ρ ≤ 1)
  refine ⟨max J₀ 1, fun q S J m ε hJ hm hε hmε => ?_⟩
  exact original_pilotStage_oracle μ q S J m hρ hρ4 ((le_max_right _ _).trans hJ)
    (hJ₀ J ((le_max_left _ _).trans hJ)) hm hε hmε

end ThresholdHC.ArbitraryLawAdaptation
