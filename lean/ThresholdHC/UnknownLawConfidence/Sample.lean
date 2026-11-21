import ThresholdHC.UnknownLawConfidence.Population

/-! One stage: the three sample fractions over `n` independent fresh items.

The item tapes of a stage-local table are iid with the original population
tape law, so each of the three outcome indicators averages `n` independent
variables in `[0,1]`. A sample fraction exceeds its mean by at least `a` with
probability at most `exp(-2 n a^2) <= delta_j / 3`. Off the union of the three
events, the stage interval contains `theta` and its width is at most
`P(D <= 2r) + 3a + 3tau`. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal
namespace ThresholdHC.UnknownLawConfidence
open ThresholdHC.Tier6 ThresholdHC.HardBudget ThresholdHC.ObservableSimulation
open ThresholdHC.Uniform713

/-- The law of a stage-local coin table. -/
abbrev tableLaw (μ : Measure Gap) (q : SignLaw) : Measure Table :=
  Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)

theorem outcome_independent (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    {A : Set (ℕ → Bool)} (hA : MeasurableSet A) :
    iIndepFun (fun i t => outcome A i t) (tableLaw μ q) :=
  (iIndepFun_infinitePi (P := fun _ : ℕ => originalPopulationTapeLaw μ q)
    (X := fun _ => A.indicator (fun _ => (1 : ℝ)))
    (fun _ => measurable_const.indicator hA)).precomp itemCoin_injective

theorem outcome_mean (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    {A : Set (ℕ → Bool)} (hA : MeasurableSet A) (i : ℕ) :
    ∫ t, outcome A i t ∂tableLaw μ q = (originalPopulationTapeLaw μ q).real A := by
  change ∫ t, A.indicator (fun _ => (1 : ℝ)) (t (itemCoin i)) ∂tableLaw μ q = _
  rw [← integral_map (measurable_pi_apply (itemCoin i)).aemeasurable
    (measurable_const.indicator hA).aestronglyMeasurable, Measure.infinitePi_map_eval,
    integral_indicator_const _ hA, smul_eq_mul, mul_one]

/-- One sample fraction exceeds its mean by at least `a`. -/
def sampleDeviation (μ : Measure Gap) (q : SignLaw) (δ : ℝ) (j : ℕ)
    (A : Set (ℕ → Bool)) : Set Table :=
  {t | sampling δ j ≤
    prefixMean (outcome A) (itemCount j) t - (originalPopulationTapeLaw μ q).real A}

theorem measurableSet_sampleDeviation (μ : Measure Gap) (q : SignLaw) (δ : ℝ) (j : ℕ)
    {A : Set (ℕ → Bool)} (hA : MeasurableSet A) :
    MeasurableSet (sampleDeviation μ q δ j A) :=
  measurableSet_le measurable_const
    ((measurable_prefixMean (fun i => measurable_outcome hA i) _).sub_const _)

theorem sampleDeviation_le (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    {δ : ℝ} (hδ : 0 < δ) (j : ℕ) {A : Set (ℕ → Bool)} (hA : MeasurableSet A) :
    (tableLaw μ q).real (sampleDeviation μ q δ j A) ≤ Anytime.stageFailure δ j / 3 := by
  have hn := itemCount_pos j
  have hs := prefixMean_subgaussian (μ := tableLaw μ q) (X := outcome A)
    (fun i => measurable_outcome hA i) (fun i => ae_of_all _ (outcome_mem_Icc A i))
    (outcome_mean μ q hA) (outcome_independent μ q hA) hn
  have h := hs.measure_ge_le (sampling_nonneg δ j)
  have he : -(sampling δ j) ^ 2 / (2 * ((1 / (4 * itemCount j) : ℝ≥0) : ℝ)) =
      -2 * (itemCount j : ℝ) * (sampling δ j / 1) ^ 2 := by
    norm_num
    have : (itemCount j : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
    ring
  rw [he, div_one] at h
  have hf := Anytime.stageFailure_pos hδ j
  exact h.trans (hoeffding_exp_le hn (by positivity))

/-- Some sample fraction exceeds its mean by at least `a`. -/
def sampleBad (μ : Measure Gap) (q : SignLaw) (δ : ℝ) (j : ℕ) : Set Table :=
  sampleDeviation μ q δ j (posSet j) ∪ sampleDeviation μ q δ j (negSet j) ∪
    sampleDeviation μ q δ j (zeroSet j)

theorem measurableSet_sampleBad (μ : Measure Gap) (q : SignLaw) (δ : ℝ) (j : ℕ) :
    MeasurableSet (sampleBad μ q δ j) :=
  ((measurableSet_sampleDeviation μ q δ j (measurableSet_posSet j)).union
    (measurableSet_sampleDeviation μ q δ j (measurableSet_negSet j))).union
    (measurableSet_sampleDeviation μ q δ j (measurableSet_zeroSet j))

theorem sampleDeviation_le_ofReal (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    {δ : ℝ} (hδ : 0 < δ) (j : ℕ) {A : Set (ℕ → Bool)} (hA : MeasurableSet A) :
    tableLaw μ q (sampleDeviation μ q δ j A) ≤ ENNReal.ofReal (Anytime.stageFailure δ j / 3) := by
  rw [← ofReal_measureReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal (sampleDeviation_le μ q hδ j hA)

/-- The three sample events together have probability at most `delta_j`. -/
theorem sampleBad_le (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    {δ : ℝ} (hδ : 0 < δ) (j : ℕ) :
    tableLaw μ q (sampleBad μ q δ j) ≤ ENNReal.ofReal (Anytime.stageFailure δ j) := by
  have hf := Anytime.stageFailure_pos hδ j
  have h3 : ENNReal.ofReal (Anytime.stageFailure δ j) =
      ENNReal.ofReal (Anytime.stageFailure δ j / 3) +
        ENNReal.ofReal (Anytime.stageFailure δ j / 3) +
        ENNReal.ofReal (Anytime.stageFailure δ j / 3) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  rw [h3]
  unfold sampleBad
  refine (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
    (add_le_add ?_ ?_)) ?_)
  · exact sampleDeviation_le_ofReal μ q hδ j (measurableSet_posSet j)
  · exact sampleDeviation_le_ofReal μ q hδ j (measurableSet_negSet j)
  · exact sampleDeviation_le_ofReal μ q hδ j (measurableSet_zeroSet j)

/-- Off the sample events the stage interval covers `theta` and has width at most
the stage bound. -/
theorem stageInterval_good (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (δ : ℝ) (j : ℕ) {t : Table} (ht : t ∉ sampleBad μ q δ j) :
    (stageInterval δ j (stageWord j t)).1 ≤ signMean μ q.val ∧
      signMean μ q.val ≤ (stageInterval δ j (stageWord j t)).2 ∧
      (stageInterval δ j (stageWord j t)).2 - (stageInterval δ j (stageWord j t)).1 ≤
        widthBound μ δ j := by
  have hp : ¬ sampling δ j ≤ prefixMean (outcome (posSet j)) (itemCount j) t -
      (originalPopulationTapeLaw μ q).real (posSet j) := fun h => ht (Or.inl (Or.inl h))
  have hn : ¬ sampling δ j ≤ prefixMean (outcome (negSet j)) (itemCount j) t -
      (originalPopulationTapeLaw μ q).real (negSet j) := fun h => ht (Or.inl (Or.inr h))
  have hz : ¬ sampling δ j ≤ prefixMean (outcome (zeroSet j)) (itemCount j) t -
      (originalPopulationTapeLaw μ q).real (zeroSet j) := fun h => ht (Or.inr h)
  rw [not_le] at hp hn hz
  have hsum := prefixMean_outcome_sum j t
  have hP := positiveCount_eq j t
  have hN := negativeCount_eq j t
  have hp' := positive_prob_le μ q j
  have hn' := negative_prob_le μ q j
  have hz' := zero_prob_le μ q j
  have hθ := signMean_bounds μ q
  have hτ := (tolerance_pos j).le
  have ha := sampling_nonneg δ j
  unfold stageInterval
  dsimp only
  rw [hP, hN]
  refine ⟨max_le hθ.1 (by linarith), le_min hθ.2 (by linarith), ?_⟩
  have h1 := min_le_right (1 : ℝ) (1 - prefixMean (outcome (negSet j)) (itemCount j) t +
    sampling δ j + tolerance j)
  have h2 := le_max_right (0 : ℝ) (prefixMean (outcome (posSet j)) (itemCount j) t -
    sampling δ j - tolerance j)
  unfold widthBound
  linarith

end ThresholdHC.UnknownLawConfidence
