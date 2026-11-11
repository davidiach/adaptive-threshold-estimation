import ThresholdHC.ArbitraryLawAdaptation.TailPilot
import ThresholdHC.ArbitraryLawAdaptation.TailObservable
import ThresholdHC.ArbitraryLawAdaptation.LearnedStage

/-! The pilot's probability event (A8) and the learned law it produces.

The pilot of target depth `J` runs a common number `m ≥ 8 log(2J/ε)` of probes
at every depth `j = 1, …, J`, with the budgets and the coin cap of (A6). With
probability at least `1 - ε`, at every depth at once,

  `F(2^{-j}) ≤ U_j ≤ 128 (u_j + W_j/b_j + 1/M)`,

which is (A8). The statement is proved for every probability law of positive
gaps and every measurable gap-dependent sign law: for the pilot run alone,
under the law of the original experiment, and for the pilot installed in the
paid learning stage, on the coin array of the original simulation law.

The stage computes the finite law (A9) from the certificates read off the
observed word, with its mass at zero. That law is a probability law on every
word, and on the event (A8) it dominates the gap law in distribution. -/

noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace ThresholdHC.ArbitraryLawAdaptation
open ThresholdHC.Tier2 ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.CriticalEntropy
open ThresholdHC.ObservableSimulation ThresholdHC.HardBudget ThresholdHC.BlindUpper

theorem exists_lt_eq_biUnion {Y : Type*} (Bad : ℕ → Set Y) (n : ℕ) :
    {ω : ℕ → Y | ∃ i, i < n ∧ ω i ∈ Bad i} =
      ⋃ i ∈ Finset.range n, (fun ω : ℕ → Y => ω i) ⁻¹' Bad i := by
  ext ω
  simp

theorem measurableSet_exists_lt {Y : Type*} [MeasurableSpace Y] (Bad : ℕ → Set Y)
    (hmeas : ∀ i, MeasurableSet (Bad i)) (n : ℕ) :
    MeasurableSet {ω : ℕ → Y | ∃ i, i < n ∧ ω i ∈ Bad i} := by
  rw [exists_lt_eq_biUnion]
  exact Finset.measurableSet_biUnion _ fun i _ => (measurable_pi_apply i) (hmeas i)

/-- Finitely many independent blocks. The probability that some block `i < n`
lies in its failure set is at most `n` times a common bound on the failure
probabilities. -/
theorem block_union_bound {Y : Type*} [MeasurableSpace Y] (P : Measure Y)
    [IsProbabilityMeasure P] (Bad : ℕ → Set Y) (hmeas : ∀ i, MeasurableSet (Bad i)) (n : ℕ)
    {e : ℝ} (hbad : ∀ i, i < n → P.real (Bad i) ≤ e) :
    (Measure.infinitePi (fun _ : ℕ => P)).real {ω | ∃ i, i < n ∧ ω i ∈ Bad i} ≤ n * e := by
  rw [exists_lt_eq_biUnion]
  refine (measureReal_biUnion_finset_le _ _).trans ?_
  have hterm : ∀ i ∈ Finset.range n,
      (Measure.infinitePi (fun _ : ℕ => P)).real ((fun ω : ℕ → Y => ω i) ⁻¹' Bad i) ≤ e := by
    intro i hi
    rw [← map_measureReal_apply (measurable_pi_apply i) (hmeas i), Measure.infinitePi_map_eval]
    exact hbad i (Finset.mem_range.mp hi)
  refine (Finset.sum_le_sum hterm).trans_eq ?_
  simp

/-- The coins `Nat.pair 0 i` of a sequence of independent draws are again a
sequence of independent draws. -/
theorem infinitePi_map_first_block {X : Type*} [MeasurableSpace X] (S : Measure X)
    [IsProbabilityMeasure S] :
    (Measure.infinitePi (fun _ : ℕ => S)).map (fun (ω : ℕ → X) (i : ℕ) => ω (Nat.pair 0 i)) =
      Measure.infinitePi (fun _ : ℕ => S) := by
  have hsplit : Measurable (fun (ω : ℕ → X) (j i : ℕ) => ω (Nat.pair j i)) :=
    Measurable.of_eval fun j => Measurable.of_eval fun i => measurable_pi_apply _
  have he : (fun (ω : ℕ → X) (i : ℕ) => ω (Nat.pair 0 i)) =
      (fun z : ℕ → ℕ → X => z 0) ∘ (fun (ω : ℕ → X) (j i : ℕ) => ω (Nat.pair j i)) := rfl
  rw [he, ← Measure.map_map (measurable_pi_apply 0) hsplit, infinitePi_map_blocks S,
    Measure.infinitePi_map_eval]

/-- The bound of (A8) at depth `j`: `128 (u_j + W_j/b_j + 1/M)`. -/
def pilotBound (μ : Measure Gap) (J : ℕ) (ρ : ℝ) (j : ℕ) : ℝ :=
  128 * (tailUnresolvedMass μ j + (∫ d : Gap, tailWorkEnvelope j d ∂μ) / pilotBudget J j +
    1 / pilotCoinCap J ρ)

/-- The capped bound of one depth is at most the bound of (A8). -/
theorem capped_bound_le_pilotBound (μ : Measure Gap) [IsProbabilityMeasure μ] (J : ℕ) (ρ : ℝ)
    (j : ℕ) :
    min 1 (128 * max (max (tailUnresolvedMass μ j)
        ((∫ d : Gap, tailWorkEnvelope j d ∂μ) / pilotBudget J j)) (1 / pilotCoinCap J ρ)) ≤
      pilotBound μ J ρ j := by
  have hu : 0 ≤ tailUnresolvedMass μ j := by
    have h := tail_unresolved_mass_lower μ j
    have h0 : 0 ≤ μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ j} := measureReal_nonneg
    linarith
  have hw : 0 ≤ (∫ d : Gap, tailWorkEnvelope j d ∂μ) / pilotBudget J j := by
    have h := one_le_tailWorkEnvelope_integral μ j
    exact div_nonneg (by linarith) (Nat.cast_nonneg _)
  have hc : (0 : ℝ) ≤ 1 / pilotCoinCap J ρ := by positivity
  refine (min_le_right _ _).trans ?_
  unfold pilotBound
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine max_le (max_le ?_ ?_) ?_ <;> linarith

/-- The event (A8) for the pilot's streams: stream family `z i` feeds the `m`
probes of depth `i + 1`. At every depth the median covers `F(2^{-(i+1)})` for
every choice of the probes' flip budgets and coin caps, and at the pilot's
budgets it is at most the bound of (A8). -/
def PilotGood (μ : Measure Gap) (J m : ℕ) (ρ : ℝ) (z : ℕ → ℕ → ℕ → ℕ → Bool) : Prop :=
  ∀ i, i < J →
    (∀ b' M' : ℕ → ℕ, μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ (i + 1)} ≤
      medianUpper (i + 1) m b' M' (z i)) ∧
    medianUpper (i + 1) m (fun _ => pilotBudget J (i + 1)) (fun _ => pilotCoinCap J ρ) (z i) ≤
      pilotBound μ J ρ (i + 1)

/-- The pilot's failure event: the median fails at some depth. -/
def pilotFailure (μ : Measure Gap) (J m : ℕ) (ρ : ℝ) : Set (ℕ → ℕ → ℕ → ℕ → Bool) :=
  {z | ∃ i, i < J ∧ z i ∈ medianFailure (i + 1) m (pilotBudget J (i + 1)) (pilotCoinCap J ρ)
    (μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ (i + 1)})
    (min 1 (128 * max (max (tailUnresolvedMass μ (i + 1))
      ((∫ d : Gap, tailWorkEnvelope (i + 1) d ∂μ) / pilotBudget J (i + 1)))
      (1 / pilotCoinCap J ρ)))}

theorem measurableSet_pilotFailure (μ : Measure Gap) (J m : ℕ) (ρ : ℝ) :
    MeasurableSet (pilotFailure μ J m ρ) :=
  measurableSet_exists_lt _ (fun _ => measurableSet_medianFailure _ _ _ _ _ _) J

theorem pilotGood_of_not_failure (μ : Measure Gap) [IsProbabilityMeasure μ] {J m : ℕ} {ρ : ℝ}
    {z : ℕ → ℕ → ℕ → ℕ → Bool} (h : z ∉ pilotFailure μ J m ρ) : PilotGood μ J m ρ z := by
  intro i hi
  obtain ⟨h1, h2⟩ := median_good_of_not_failure fun hmem => h ⟨i, hi, hmem⟩
  exact ⟨h1, h2.trans (capped_bound_le_pilotBound μ J ρ (i + 1))⟩

/-- On independent streams, the pilot fails with probability at most
`2 J exp(-m/8)`. -/
theorem original_pilotFailure_le (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (J m : ℕ) {ρ : ℝ} (hρ : 0 < ρ) (hm : 0 < m) :
    (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ =>
        Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)))).real
      (pilotFailure μ J m ρ) ≤ J * (2 * exp (-(m : ℝ) / 8)) :=
  block_union_bound
    (Measure.infinitePi (fun _ : ℕ =>
      Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)))
    (fun i => medianFailure (i + 1) m (pilotBudget J (i + 1)) (pilotCoinCap J ρ)
      (μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ (i + 1)})
      (min 1 (128 * max (max (tailUnresolvedMass μ (i + 1))
        ((∫ d : Gap, tailWorkEnvelope (i + 1) d ∂μ) / pilotBudget J (i + 1)))
        (1 / pilotCoinCap J ρ))))
    (fun _ => measurableSet_medianFailure _ _ _ _ _ _) J
    (fun i _ => original_medianFailure_le μ q (i + 1) m (pilotBudget J (i + 1))
      (pilotCoinCap J ρ) hm (pilotBudget_pos J (i + 1)) (pilotCoinCap_pos J hρ))

/-- The event (A8), for any measurable way of drawing the pilot's streams from
the coin array that makes them independent. With a common number
`m ≥ 8 log(2J/ε)` of probes at every depth, the event has probability at
least `1 - ε`. -/
theorem original_pilot_event (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (J m : ℕ) {ρ ε : ℝ} (hρ : 0 < ρ) (hJ : 1 ≤ J) (hm : 0 < m) (hε : 0 < ε)
    (hmε : 8 * log (2 * (J : ℝ) / ε) ≤ m)
    {f : (ℕ → ℕ → Bool) → ℕ → ℕ → ℕ → ℕ → Bool} (hf : Measurable f)
    (hlaw : (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)).map f =
      Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ =>
        Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)))) :
    1 - ε ≤
      (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)).real
        {ω | PilotGood μ J m ρ (f ω)} := by
  have hJpos : (0 : ℝ) < J := by exact_mod_cast hJ
  have hcal : 2 * exp (-(m : ℝ) / 8) ≤ ε / J := by
    apply two_exp_le_of_log_le (div_pos hε hJpos)
    rw [div_div_eq_mul_div]
    exact hmε
  have hfail : (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ =>
      Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)))).real
      (pilotFailure μ J m ρ) ≤ ε := by
    refine (original_pilotFailure_le μ q J m hρ hm).trans ?_
    calc (J : ℝ) * (2 * exp (-(m : ℝ) / 8)) ≤ J * (ε / J) :=
          mul_le_mul_of_nonneg_left hcal hJpos.le
      _ = ε := by field_simp
  rw [← hlaw] at hfail
  exact one_sub_le_real_preimage
    (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)) hf
    (measurableSet_pilotFailure μ J m ρ) (Good := {z | PilotGood μ J m ρ z})
    (fun z hz => pilotGood_of_not_failure μ hz) hfail

/-- The streams of the pilot run alone: probe `k` of depth `i + 1` reads the
coins `Nat.pair i (Nat.pair k c)`. -/
def pilotStreams (ω : ℕ → ℕ → Bool) : ℕ → ℕ → ℕ → ℕ → Bool :=
  fun i k c => ω (Nat.pair i (Nat.pair k c))

/-- The streams of the pilot in the learning stage, whose pilot reads the
coins `Nat.pair 0 i`: probe `k` of depth `i + 1` reads the coins
`Nat.pair 0 (Nat.pair i (Nat.pair k c))`. -/
def stageStreams (ω : ℕ → ℕ → Bool) : ℕ → ℕ → ℕ → ℕ → Bool :=
  fun i k c => ω (Nat.pair 0 (Nat.pair i (Nat.pair k c)))

theorem measurable_pilotStreams : Measurable pilotStreams :=
  Measurable.of_eval fun _ => Measurable.of_eval fun _ => Measurable.of_eval fun _ =>
    measurable_pi_apply _

theorem measurable_stageStreams : Measurable stageStreams :=
  Measurable.of_eval fun _ => Measurable.of_eval fun _ => Measurable.of_eval fun _ =>
    measurable_pi_apply _

theorem pilotStreams_law (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)).map pilotStreams =
      Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ =>
        Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q))) :=
  infinitePi_map_depth_blocks (originalPopulationTapeLaw μ q)

theorem stageStreams_law (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)).map stageStreams =
      Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ =>
        Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q))) := by
  have hshift : Measurable (fun (ω : ℕ → ℕ → Bool) (i : ℕ) => ω (Nat.pair 0 i)) :=
    Measurable.of_eval fun _ => measurable_pi_apply _
  have he : stageStreams = pilotStreams ∘ (fun (ω : ℕ → ℕ → Bool) (i : ℕ) => ω (Nat.pair 0 i)) :=
    rfl
  rw [he, ← Measure.map_map measurable_pilotStreams hshift,
    infinitePi_map_first_block (originalPopulationTapeLaw μ q), pilotStreams_law]

/-- The pilot run alone as an estimator. It buys the pilot's flips and reports
the certificate of depth `i + 1`; the flips it buys do not depend on `i`. -/
def pilotEstimator (J m : ℕ) (ρ : ℝ) (i : ℕ) : AdaptiveEstimator Unit :=
  wordEstimator (pilotCost J m) (pilotReader J m (pilotCoinCap J ρ))
    (fun w => pilotUpper J m (pilotCoinCap J ρ) w i)

/-- The pilot buys at most `m ∑_j b_j` flips on every path, which is at most
`m 4^J` by `pilotCost_le`. -/
theorem pilotEstimator_cap (J m : ℕ) (ρ : ℝ) (i : ℕ) :
    PathwiseCap (pilotEstimator J m ρ i) (pilotCost J m) :=
  wordEstimator_cap _ _ _

/-- The event (A8) in the original experiment, for the pilot run alone. With
`m ≥ 8 log(2J/ε)` probes at every depth, with probability at least `1 - ε`
the certificate of every depth `j = i + 1 ≤ J` satisfies
`F(2^{-j}) ≤ U_j ≤ 128 (u_j + W_j/b_j + 1/M)`. -/
theorem observable_pilot_event (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (J m i₀ : ℕ) {ρ ε : ℝ} (hρ : 0 < ρ) (hJ : 1 ≤ J) (hm : 0 < m) (hε : 0 < ε)
    (hmε : 8 * log (2 * (J : ℝ) / ε) ≤ m) :
    1 - ε ≤
      (experimentLaw μ (pilotEstimator J m ρ i₀) q).real
        {z | ∀ i, i < J →
          μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ (i + 1)} ≤
            (pilotEstimator J m ρ i).output (z.1.1, z.2) ∧
          (pilotEstimator J m ρ i).output (z.1.1, z.2) ≤ pilotBound μ J ρ (i + 1)} := by
  refine observable_of_array μ q (pilotCost J m) (pilotReader J m (pilotCoinCap J ρ))
    (fun w => pilotUpper J m (pilotCoinCap J ρ) w i₀)
    {w | ∀ i, i < J →
      μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ (i + 1)} ≤ pilotUpper J m (pilotCoinCap J ρ) w i ∧
      pilotUpper J m (pilotCoinCap J ρ) w i ≤ pilotBound μ J ρ (i + 1)} ?_
    (original_pilot_event μ q J m hρ hJ hm hε hmε measurable_pilotStreams
      (pilotStreams_law μ q))
  intro ω hω i hi
  obtain ⟨h1, h2⟩ := hω i hi
  rw [pilotUpper_readBlock J m (pilotCoinCap J ρ) ω hi]
  exact ⟨h1 _ _, h2⟩

variable {R : Type} [MeasurableSpace R]

/-- A learning stage with the capped multi-depth pilot installed. The private
randomness, the continuation and the interval rule are those of `S`. The
stage's index `i` is depth `i + 1`, and its deepest index is `J - 1`. -/
def pilotStage (S : LearnedStage R) (J m : ℕ) (ρ : ℝ) : LearnedStage R :=
  { S with
    pilotCost := pilotCost J m
    depth := J - 1
    pilot := pilotReader J m (pilotCoinCap J ρ)
    upper := pilotUpper J m (pilotCoinCap J ρ)
    upper_nonneg := pilotUpper_nonneg J m (pilotCoinCap J ρ)
    upper_zero := pilotUpper_zero J m (pilotCoinCap J ρ) }

/-- The stage's cap is the pilot's `m ∑_j b_j` flips plus the continuation's. -/
theorem pilotStage_cap (S : LearnedStage R) (J m : ℕ) (ρ : ℝ) :
    (pilotStage S J m ρ).cap = m * pilotSpan J + S.continuationCost := by
  change pilotCost J m + S.continuationCost = _
  rw [pilotCost_eq]

theorem pilotStage_cap_le (S : LearnedStage R) {J : ℕ} (hJ : 1 ≤ J) (m : ℕ) (ρ : ℝ) :
    (pilotStage S J m ρ).cap ≤ m * 4 ^ J + S.continuationCost := by
  rw [pilotStage_cap]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left m (pilotSpan_le hJ)) _

/-- The stage with the pilot buys at most `m ∑_j b_j` flips for the pilot and
the continuation's flips, on every path: failure paths and partially tested
coins included. -/
theorem pilotStage_pathwise (S : LearnedStage R) (J m : ℕ) (ρ : ℝ) (upper : Bool) :
    PathwiseCap ((pilotStage S J m ρ).endpoint upper)
      (m * pilotSpan J + S.continuationCost) := by
  rw [← pilotStage_cap S J m ρ]
  exact LearnedStage.endpoint_cap _ upper

/-- The word the stage's pilot observes on a table of coin tapes: the stage
runs the pilot on the coins `Nat.pair 0 i`. -/
def pilotStageWord (J m : ℕ) (ρ : ℝ) (s : Table) : List Bool :=
  (readBlock (pilotCost J m) (pilotReader J m (pilotCoinCap J ρ)) (fun i => s (Nat.pair 0 i))).1

/-- On every table of coin tapes, the stage's interval is computed from the
law learned from the pilot's word, and its continuation reads the fresh coins
`Nat.pair 1 i`. -/
theorem pilotStage_tableInterval (S : LearnedStage R) (J m : ℕ) (ρ : ℝ) (r : R) (s : Table) :
    (pilotStage S J m ρ).tableInterval r s =
      S.interval ((pilotStage S J m ρ).learnedLaw (pilotStageWord J m ρ s)) r
        (readBlock S.continuationCost
          (S.continuation ((pilotStage S J m ρ).learnedLaw (pilotStageWord J m ρ s)) r)
          (fun i => s (Nat.pair 1 i))).1 := rfl

/-- The certificate of depth `i + 1 ≤ J` that the stage reads off the pilot's
word is the tape-level median of the `m` probes of that depth, probe `k`
reading the coins `Nat.pair 0 (Nat.pair i (Nat.pair k c))`. -/
theorem pilotStage_upper_word (S : LearnedStage R) (J m : ℕ) (ρ : ℝ) (s : Table) {i : ℕ}
    (hi : i < J) :
    (pilotStage S J m ρ).upper (pilotStageWord J m ρ s) i =
      medianUpper (i + 1) m (fun _ => pilotBudget J (i + 1)) (fun _ => pilotCoinCap J ρ)
        (stageStreams s i) :=
  pilotUpper_readBlock J m (pilotCoinCap J ρ) (fun i => s (Nat.pair 0 i)) hi

/-- The learned law (A9) is a probability law on every observed word. -/
theorem pilotStage_learnedLaw_probability (S : LearnedStage R) (J m : ℕ) (ρ : ℝ)
    (xs : List Bool) : IsProbabilityMeasure ((pilotStage S J m ρ).learnedLaw xs) :=
  LearnedStage.learnedLaw_probability _ xs

/-- The learned law is the finite law (A9). With `c` the prefix minima of the
certificates read off the observed word, it puts mass `c_J` at zero and mass
`c_j - c_(j+1)` at `2^{-(j+1)}` for `j = 1, …, J - 1`; index `i` below is
depth `i + 1`. -/
theorem pilotStage_learnedLaw_eq (S : LearnedStage R) (J m : ℕ) (ρ : ℝ) (xs : List Bool) :
    (pilotStage S J m ρ).learnedLaw xs =
      ENNReal.ofReal (prefixMinimum (pilotUpper J m (pilotCoinCap J ρ) xs) (J - 1)) •
          Measure.dirac 0 +
        ∑ i : Fin (J - 1),
          ENNReal.ofReal (prefixMinimum (pilotUpper J m (pilotCoinCap J ρ) xs) i.val -
            prefixMinimum (pilotUpper J m (pilotCoinCap J ρ) xs) (i.val + 1)) •
              Measure.dirac (gridPoint (i.val + 1)) := rfl

/-- The mass of the learned law at zero is the prefix minimum of the
certificates read off the observed word, at the deepest depth. -/
theorem pilotStage_learnedLaw_zero (S : LearnedStage R) (J m : ℕ) (ρ : ℝ) (xs : List Bool) :
    (pilotStage S J m ρ).learnedLaw xs {0} =
      ENNReal.ofReal (prefixMinimum (pilotUpper J m (pilotCoinCap J ρ) xs) (J - 1)) :=
  envelopeLaw_zero _ _

/-- At the grid point `2^{-(j+2)}` the distribution function of the learned
law is the prefix minimum of the certificates up to depth `j + 1`: the atom at
a grid point belongs to the closed half-line. -/
theorem pilotStage_learnedLaw_grid (S : LearnedStage R) (J m : ℕ) (ρ : ℝ) (xs : List Bool)
    {j : ℕ} (hj : j + 1 < J) :
    (pilotStage S J m ρ).learnedLaw xs (Set.Iic (gridPoint (j + 1))) =
      ENNReal.ofReal (prefixMinimum (pilotUpper J m (pilotCoinCap J ρ) xs) j) := by
  change envelopeLaw (prefixMinimum (pilotUpper J m (pilotCoinCap J ρ) xs)) (J - 1)
    (Set.Iic (gridPoint (j + 1))) = _
  rw [envelopeLaw_Iic (prefixMinimum_nonneg (pilotUpper_nonneg J m _ xs))
    (prefixMinimum_antitone _), envelopeCDF_at_grid _ (by omega)]

/-- When the certificates read off a word cover the small-gap masses at every
depth `1, …, J`, the learned law dominates the gap law in distribution, at
every point. -/
theorem pilotStage_dominates (μ : Measure Gap) [IsProbabilityMeasure μ] (S : LearnedStage R)
    {J : ℕ} (hJ : 1 ≤ J) (m : ℕ) (ρ : ℝ) (xs : List Bool)
    (hcover : ∀ i, i < J → μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ (i + 1)} ≤
      pilotUpper J m (pilotCoinCap J ρ) xs i) (x : ℝ) :
    (μ.map Subtype.val) (Set.Iic x) ≤ (pilotStage S J m ρ).learnedLaw xs (Set.Iic x) := by
  have hsupport : (μ.map (Subtype.val : Gap → ℝ)) (Set.Iio 0) = 0 := by
    rw [Measure.map_apply measurable_subtype_coe measurableSet_Iio]
    have he : (Subtype.val : Gap → ℝ) ⁻¹' Set.Iio 0 = ∅ := by
      ext d
      simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_empty_iff_false, iff_false, not_lt]
      exact d.property.1.le
    rw [he, measure_empty]
  refine LearnedStage.learnedLaw_dominates (pilotStage S J m ρ) (μ.map Subtype.val) hsupport xs
    ?_ x
  intro j hj
  have hj' : j ≤ J - 1 := hj
  rw [map_measureReal_apply measurable_subtype_coe measurableSet_Iic]
  exact hcover j (by omega)

/-- The event (A8) for the pilot in the learning stage, on the coin array of
the original simulation law. With `m ≥ 8 log(2J/ε)` probes at every depth,
with probability at least `1 - ε` the certificates the stage reads off the
pilot's word satisfy `F(2^{-j}) ≤ U_j ≤ 128 (u_j + W_j/b_j + 1/M)` at every
depth `j = i + 1 ≤ J`, and the learned law dominates the gap law in
distribution. -/
theorem original_pilotStage_event (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (S : LearnedStage R) (J m : ℕ) {ρ ε : ℝ} (hρ : 0 < ρ) (hJ : 1 ≤ J) (hm : 0 < m)
    (hε : 0 < ε) (hmε : 8 * log (2 * (J : ℝ) / ε) ≤ m) :
    1 - ε ≤
      (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)).real
        {ω | (∀ i, i < J →
            μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ (i + 1)} ≤
              (pilotStage S J m ρ).upper (pilotStageWord J m ρ ω) i ∧
            (pilotStage S J m ρ).upper (pilotStageWord J m ρ ω) i ≤
              pilotBound μ J ρ (i + 1)) ∧
          ∀ x : ℝ, (μ.map Subtype.val) (Set.Iic x) ≤
            (pilotStage S J m ρ).learnedLaw (pilotStageWord J m ρ ω) (Set.Iic x)} := by
  refine (original_pilot_event μ q J m hρ hJ hm hε hmε measurable_stageStreams
    (stageStreams_law μ q)).trans (measureReal_mono ?_)
  intro ω hω
  have hup : ∀ i, i < J →
      μ.real {d : Gap | (d : ℝ) ≤ (1 / 2) ^ (i + 1)} ≤
        (pilotStage S J m ρ).upper (pilotStageWord J m ρ ω) i ∧
      (pilotStage S J m ρ).upper (pilotStageWord J m ρ ω) i ≤ pilotBound μ J ρ (i + 1) := by
    intro i hi
    obtain ⟨h1, h2⟩ := hω i hi
    rw [pilotStage_upper_word S J m ρ ω hi]
    exact ⟨h1 _ _, h2⟩
  exact ⟨hup, pilotStage_dominates μ S hJ m ρ _ fun i hi => (hup i hi).1⟩

end ThresholdHC.ArbitraryLawAdaptation
