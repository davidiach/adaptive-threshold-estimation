import ThresholdHC.KnownGapRarity.Risk
import Mathlib.Probability.Independence.InfinitePi

/-! Coverage of the computable interval.

The plan's output has the law of the average of `n` independent majority votes,
here realized as the production average on the infinite coin table. Two-sided
Hoeffding gives `P(|Zbar - p| > t) <= 2 exp(-2 n t^2)`, which is `delta` at
`t = sqrt(log(2/delta)/(2n))`. Since `1 - 2f > 0`, the event
`r < |(Zbar - f)/(1-2f) - theta|` with `r = t/(1-2f)` is the event `t < |Zbar - p|`.
For `B < 2m` the raw output is `0` and `r = 1`, so the failure event is empty.
Clipping toward `[0,1]` does not move the output away from `theta`. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ThresholdHC.KnownGapRarity
open ThresholdHC.Tier6 ThresholdHC.FixedPlan ThresholdHC.ObservableSimulation
open ThresholdHC.BlindUpper ThresholdHC.Uniform713

/-- The probability of an output event of the plan with `n'+1` coins, computed on
the infinite coin table. -/
theorem majority_output_preimage (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (k n' : ℕ) {S : Set ℝ} (hS : MeasurableSet S) :
    experimentLaw μ (majorityEstimator k (n'+1)) q
        (populationOutput (majorityEstimator k (n'+1)) ⁻¹' S) =
      Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)
        (productionAverage (majorityVote k) n' ⁻¹' S) := by
  have hf := measurable_finiteAverage _ (measurable_majorityVote k) n'
  have h := congrArg (fun P : Measure ℝ => P S) (majority_output_law μ q k n')
  rw [Measure.map_apply (measurable_populationOutput _) hS, Measure.map_apply hf hS] at h
  rw [h]
  exact ((productionPrefix_preserving (originalPopulationTapeLaw μ q) n').measure_preimage
    (hf hS).nullMeasurableSet).symm

theorem productionAverage_eq_prefixMean (k n' : ℕ) (s : ℕ → ℕ → Bool) :
    productionAverage (majorityVote k) n' s =
      prefixMean (fun i (s : ℕ → ℕ → Bool) => majorityVote k (s i)) (n'+1) s := by
  unfold productionAverage finiteAverage prefixMean productionPrefix
  rw [Fin.sum_univ_eq_sum_range (fun i => majorityVote k (s i)) (n'+1)]
  push_cast
  ring

theorem vote_table_mean (P : Measure (ℕ → Bool)) [IsProbabilityMeasure P] (k i : ℕ) :
    ∫ s, majorityVote k (s i) ∂Measure.infinitePi (fun _ : ℕ => P) = ∫ ω, majorityVote k ω ∂P := by
  rw [← integral_map (measurable_pi_apply i).aemeasurable
    (measurable_majorityVote k).aestronglyMeasurable, Measure.infinitePi_map_eval]

/-- Two-sided Hoeffding for the average of `n'+1` independent majority votes. -/
theorem table_deviation_le (P : Measure (ℕ → Bool)) [IsProbabilityMeasure P] (k n' : ℕ)
    {t : ℝ} (ht : 0 ≤ t) :
    Measure.infinitePi (fun _ : ℕ => P)
        {s | t < |productionAverage (majorityVote k) n' s - ∫ ω, majorityVote k ω ∂P|} ≤
      ENNReal.ofReal (2 * Real.exp (-2 * ((n' : ℝ) + 1) * t^2)) := by
  have hs := prefixMean_subgaussian (μ := Measure.infinitePi (fun _ : ℕ => P))
    (X := fun i s => majorityVote k (s i)) (p := ∫ ω, majorityVote k ω ∂P)
    (fun i => (measurable_majorityVote k).comp (measurable_pi_apply i))
    (fun i => ae_of_all _ (fun s => majorityVote_mem k (s i)))
    (fun i => vote_table_mean P k i)
    (iIndepFun_infinitePi (P := fun _ : ℕ => P) (X := fun _ => majorityVote k)
      (fun _ => measurable_majorityVote k)) (n := n'+1) (by omega)
  have he : -t ^ 2 / (2 * ((1 / (4 * ((n'+1 : ℕ) : ℝ≥0)) : ℝ≥0) : ℝ)) =
      -2 * ((n' : ℝ) + 1) * t ^ 2 := by
    norm_num
    field_simp
    ring
  have h1 := hs.measure_ge_le ht
  have h2 := hs.neg.measure_ge_le ht
  simp only [Pi.neg_apply, neg_sub, he] at h1 h2
  set p := ∫ ω, majorityVote k ω ∂P
  set T := Measure.infinitePi (fun _ : ℕ => P)
  set X : ℕ → (ℕ → ℕ → Bool) → ℝ := fun i s => majorityVote k (s i)
  have hsub : {s | t < |productionAverage (majorityVote k) n' s - p|} ⊆
      {s | t ≤ prefixMean X (n'+1) s - p} ∪ {s | t ≤ p - prefixMean X (n'+1) s} := by
    intro s hs
    simp only [Set.mem_ofPred_eq, Set.mem_union] at hs ⊢
    rw [productionAverage_eq_prefixMean] at hs
    rcases lt_abs.mp hs with h | h
    · left; linarith
    · right; linarith
  calc T {s | t < |productionAverage (majorityVote k) n' s - p|}
      ≤ T ({s | t ≤ prefixMean X (n'+1) s - p} ∪ {s | t ≤ p - prefixMean X (n'+1) s}) :=
        measure_mono hsub
    _ ≤ T {s | t ≤ prefixMean X (n'+1) s - p} + T {s | t ≤ p - prefixMean X (n'+1) s} :=
        measure_union_le _ _
    _ = ENNReal.ofReal (T.real {s | t ≤ prefixMean X (n'+1) s - p}) +
          ENNReal.ofReal (T.real {s | t ≤ p - prefixMean X (n'+1) s}) := by
        rw [ofReal_measureReal, ofReal_measureReal]
    _ ≤ ENNReal.ofReal (Real.exp (-2 * ((n' : ℝ) + 1) * t^2)) +
          ENNReal.ofReal (Real.exp (-2 * ((n' : ℝ) + 1) * t^2)) :=
        add_le_add (ENNReal.ofReal_le_ofReal h1) (ENNReal.ofReal_le_ofReal h2)
    _ = ENNReal.ofReal (2 * Real.exp (-2 * ((n' : ℝ) + 1) * t^2)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        ring_nf

/-- The raw estimator misses `theta` by more than the radius with probability at most `delta`. -/
theorem rawEstimator_confidence (d : Gap) (B : ℝ) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    Confidence.UniformConfidence (Measure.dirac d) (rawEstimator d B) (knownGapRadius d B δ) δ := by
  intro q
  unfold Confidence.failureProbability
  rw [signMean_dirac]
  have hθ0 := (q.property.2 d).1
  have hθ1 := (q.property.2 d).2
  by_cases h : 2 * (flipCount d B : ℝ) ≤ B
  · rw [knownGapRadius_of_le δ h, rawEstimator_of_le h, debiased_experimentLaw]
    obtain ⟨n', hn'⟩ : ∃ n', coinCount d B = n'+1 := ⟨coinCount d B - 1, by
      have := coinCount_pos h; omega⟩
    have hf := one_sub_two_missRate h
    have hc : 0 < 1 - 2 * missRate d B := by linarith
    have hp : ∫ ω, majorityVote (flipIndex d B) ω ∂originalPopulationTapeLaw (Measure.dirac d) q =
        missRate d B + (1 - 2 * missRate d B) * q.val d := vote_mean_dirac (flipIndex d B) d q
    set k := flipIndex d B
    set f := missRate d B
    set t := Real.sqrt (Real.log (2/δ) / (2 * (coinCount d B : ℝ)))
    set p := ∫ ω, majorityVote k ω ∂originalPopulationTapeLaw (Measure.dirac d) q
    have hset : {z | t / (1 - 2*f) <
        |populationOutput (debiased k (coinCount d B) f) z - q.val d|} =
        populationOutput (majorityEstimator k (coinCount d B)) ⁻¹' {x | t < |x - p|} := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_preimage]
      rw [debiased_populationOutput]
      have he : (populationOutput (majorityEstimator k (coinCount d B)) z - f) / (1 - 2*f) - q.val d =
          (populationOutput (majorityEstimator k (coinCount d B)) z - p) / (1 - 2*f) := by
        rw [eq_div_iff hc.ne', sub_mul, div_mul_cancel₀ _ hc.ne', hp]
        ring
      rw [he, abs_div, abs_of_pos hc, div_lt_div_iff_of_pos_right hc]
    rw [hset, hn']
    have hS : MeasurableSet {x : ℝ | t < |x - p|} :=
      measurableSet_lt measurable_const ((measurable_id.sub_const p).abs)
    rw [majority_output_preimage _ _ k n' hS]
    refine (table_deviation_le _ k n' (Real.sqrt_nonneg _)).trans ?_
    apply ENNReal.ofReal_le_ofReal
    have hlog : 0 ≤ Real.log (2/δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ0]; linarith)
    have hn0 : (0 : ℝ) < (n' : ℝ) + 1 := by positivity
    have ht2 : t^2 = Real.log (2/δ) / (2 * ((n' : ℝ) + 1)) := by
      simp only [t]
      rw [Real.sq_sqrt (by rw [hn']; push_cast; positivity), hn']
      push_cast
      ring
    rw [ht2]
    have hx : -2 * ((n' : ℝ) + 1) * (Real.log (2/δ) / (2 * ((n' : ℝ) + 1))) = -Real.log (2/δ) := by
      field_simp
    rw [hx, Real.exp_neg, Real.exp_log (by positivity)]
    rw [inv_div]
    field_simp
    rfl
  · rw [knownGapRadius_of_lt δ (lt_of_not_ge h)]
    have he : {z | 1 < |populationOutput (rawEstimator d B) z - q.val d|} = ∅ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      rw [show populationOutput (rawEstimator d B) z = 0 from
        rawEstimator_output_of_lt (lt_of_not_ge h) _, zero_sub, abs_neg, abs_of_nonneg hθ0]
      exact hθ1
    rw [he, measure_empty]
    exact zero_le

theorem not_mem_interval_iff {x r θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    θ ∉ Set.Icc (x - r) (x + r) ∩ Set.Icc 0 1 ↔ r < |x - θ| := by
  rw [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Icc]
  constructor
  · intro h
    by_contra hc'
    have hc := abs_le.mp (not_lt.mp hc')
    exact h ⟨⟨by linarith, by linarith⟩, h0, h1⟩
  · intro h hc
    rcases hc with ⟨⟨ha, hb⟩, _⟩
    rcases lt_abs.mp h with h' | h' <;> linarith

/-- The interval form of the coverage. -/
theorem rawEstimator_interval (d : Gap) (B : ℝ) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (q : SignLaw) :
    experimentLaw (Measure.dirac d) (rawEstimator d B) q
      {z | signMean (Measure.dirac d) q.val ∉
        Set.Icc (populationOutput (rawEstimator d B) z - knownGapRadius d B δ)
                (populationOutput (rawEstimator d B) z + knownGapRadius d B δ) ∩ Set.Icc 0 1}
        ≤ ENNReal.ofReal δ := by
  have h := rawEstimator_confidence d B hδ0 hδ1 q
  unfold Confidence.failureProbability at h
  obtain ⟨h0, h1⟩ := signMean_bounds (Measure.dirac d) q
  have he : {z | signMean (Measure.dirac d) q.val ∉
        Set.Icc (populationOutput (rawEstimator d B) z - knownGapRadius d B δ)
                (populationOutput (rawEstimator d B) z + knownGapRadius d B δ) ∩ Set.Icc 0 1} =
      {z | knownGapRadius d B δ <
        |populationOutput (rawEstimator d B) z - signMean (Measure.dirac d) q.val|} := by
    ext z
    simp only [Set.mem_ofPred_eq]
    exact not_mem_interval_iff h0 h1
  rw [he]
  exact h

theorem clip_dist_le {x θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    |max 0 (min 1 x) - θ| ≤ |x - θ| := by
  have key : (max 0 (min 1 x) - θ)^2 ≤ (x - θ)^2 := by
    rcases le_total x 0 with hx | hx
    · rw [min_eq_right (by linarith : x ≤ 1), max_eq_left hx]
      nlinarith
    · rcases le_total x 1 with hx1 | hx1
      · rw [min_eq_right hx1, max_eq_right hx]
      · rw [min_eq_left hx1, max_eq_right zero_le_one]
        nlinarith
  exact sq_le_sq.mp key

/-- The interval centred at the clipped output also covers. -/
theorem knownGap_confidence (d : Gap) (B : ℝ) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    Confidence.UniformConfidence (Measure.dirac d) (knownGapEstimator d B) (knownGapRadius d B δ) δ := by
  intro q
  refine le_trans ?_ (rawEstimator_confidence d B hδ0 hδ1 q)
  unfold Confidence.failureProbability
  obtain ⟨h0, h1⟩ := signMean_bounds (Measure.dirac d) q
  change experimentLaw (Measure.dirac d) (rawEstimator d B) q _ ≤ _
  apply measure_mono
  intro z hz
  simp only [Set.mem_ofPred_eq] at hz ⊢
  exact lt_of_lt_of_le hz (clip_dist_le h0 h1)

end ThresholdHC.KnownGapRarity
