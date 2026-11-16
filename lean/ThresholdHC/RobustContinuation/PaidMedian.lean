import ThresholdHC.RobustContinuation.CappedMedian
import ThresholdHC.RobustContinuation.PaidCoverage
import ThresholdHC.ConfidenceProgram.Schedule

/-! Statistical guarantees of the installed paid pilot and its selected
physical-cap median in the original hidden-gap experiment. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace ThresholdHC.RobustContinuation
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.RareAboveTwo
open ThresholdHC.ArbitraryLawAdaptation ThresholdHC.KnownLawPlanner
open ThresholdHC.HardBudget ThresholdHC.ConfidenceProgram ThresholdHC.Confidence
open ThresholdHC.ObservableSimulation ThresholdHC.BlindUpper

theorem learnedLaw_support {R : Type} [MeasurableSpace R]
    (S : LearnedStage R) (xs : List Bool) : S.learnedLaw xs (Set.Icc 0 (1/2))ᶜ = 0 := by
  have hg (i : ℕ) : gridPoint (i+1) ∈ Set.Icc (0 : ℝ) (1/2) := by
    refine ⟨(gridPoint_pos _).le, ?_⟩
    simpa [gridPoint] using gridPoint_antitone (Nat.zero_le (i+1))
  simp only [LearnedStage.learnedLaw, envelopeLaw, Measure.add_apply,
    Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  have h0 : (0 : ℝ) ∉ (Set.Icc 0 (1/2))ᶜ := by norm_num
  rw [Measure.dirac_apply, Set.indicator_of_notMem h0, mul_zero, zero_add]
  apply Finset.sum_eq_zero
  intro i _
  rw [Measure.dirac_apply, Set.indicator_of_notMem
    (show gridPoint (i.val+1) ∉ (Set.Icc 0 (1/2))ᶜ from not_not.mpr (hg i.val)), mul_zero]

theorem learnedLaw_valid {R : Type} [MeasurableSpace R]
    (S : LearnedStage R) (xs : List Bool) {ρ B : ℝ} (m : ℕ)
    (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) :
    ValidReference (S.learnedLaw xs) ρ (medianBaseBudget B m) :=
  ⟨S.learnedLaw_probability xs, learnedLaw_support S xs, hρ, hρ4,
    div_pos hB (by positivity)⟩

theorem medianStage_seed_law (ρ B : ℝ) (m : ℕ) (α : Measure ℝ)
    (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    (originalSimulationLaw μ ((medianStage ρ B m).endpoint false) q).map
      (fun z => (z.1 α, z.2)) =
      originalSimulationLaw μ (cappedMedian (referenceBase α ρ (medianBaseBudget B m))
        m (medianCopyCap B m) ρ) q := by
  change ((Measure.infinitePi (fun α : Measure ℝ =>
    (cappedMedian (referenceBase α ρ (medianBaseBudget B m)) m (medianCopyCap B m) ρ).randomLaw)).prod
      (Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q))).map
      (Prod.map (fun r => r α) id) = _
  rw [← Measure.map_prod_map _ _ (measurable_pi_apply α) measurable_id,
    Measure.infinitePi_map_eval, Measure.map_id]
  rfl

theorem medianStage_fixed_interval_law (ρ B : ℝ) (m : ℕ) (α : Measure ℝ)
    (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    (originalSimulationLaw μ ((medianStage ρ B m).endpoint false) q).map
      (fun z => (medianStage ρ B m).interval α z.1
        (readBlock (medianStage ρ B m).continuationCost
          ((medianStage ρ B m).continuation α z.1) z.2).1) =
      (originalSimulationLaw μ (cappedMedian (referenceBase α ρ (medianBaseBudget B m))
        m (medianCopyCap B m) ρ) q).map (fun z =>
          let v := (cappedMedian (referenceBase α ρ (medianBaseBudget B m))
            m (medianCopyCap B m) ρ).output
              (z.1, populationPath ((cappedMedian (referenceBase α ρ (medianBaseBudget B m))
                m (medianCopyCap B m) ρ).policy z.1) z.2)
          (v - medianRadius α ρ B m, v + medianRadius α ρ B m)) := by
  let A := cappedMedian (referenceBase α ρ (medianBaseBudget B m)) m (medianCopyCap B m) ρ
  let F := fun z : (ℕ → ReferenceSeed α ρ (medianBaseBudget B m)) × Table =>
    let v := A.output (z.1, populationPath (A.policy z.1) z.2)
    (v - medianRadius α ρ B m, v + medianRadius α ρ B m)
  have hv : Measurable (fun z : (ℕ → ReferenceSeed α ρ (medianBaseBudget B m)) × Table =>
      A.output (z.1, populationPath (A.policy z.1) z.2)) :=
    A.output_measurable.comp (measurable_fst.prodMk
      (measurable_seeded_populationPath A.policy
        (fun w => measurable_to_countable' (A.policy_measurable w))))
  have hF : Measurable F := (hv.sub_const _).prodMk (hv.add_const _)
  rw [← medianStage_seed_law ρ B m α μ q, Measure.map_map hF (by fun_prop)]
  congr 1
  funext z
  change (medianWord _ _ _ _ _ _ - _, medianWord _ _ _ _ _ _ + _) = _
  dsimp only [medianStage]
  rw [medianWord_output]
  rfl

theorem failureProbability_simulation {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    (q : SignLaw) (r : ℝ) :
    failureProbability μ A q r = (originalSimulationLaw μ A q)
      {z | r < |A.output (z.1,populationPath (A.policy z.1) z.2)-signMean μ q.val|} := by
  let E := {z : R × ProcessTape | r < |A.output z-signMean μ q.val|}
  have hE : MeasurableSet E := measurableSet_lt measurable_const ((A.output_measurable.sub_const _).abs)
  have h := congrArg (fun P : Measure (R × ProcessTape) => P E) (original_observable_simulation_law μ A q)
  have hm : Measurable (fun z : R × Table => (z.1,populationPath (A.policy z.1) z.2)) :=
    measurable_fst.prodMk (measurable_seeded_populationPath A.policy
      (fun w => measurable_to_countable' (A.policy_measurable w)))
  change (experimentLaw μ A q) ((fun z => (z.1.1,z.2)) ⁻¹' E) =
    (originalSimulationLaw μ A q) ((fun z => (z.1,populationPath (A.policy z.1) z.2)) ⁻¹' E)
  simpa only [Measure.map_apply (measurable_fst.fst.prodMk measurable_snd) hE,
    Measure.map_apply hm hE] using h

theorem medianStage_fixed_failure (ρ B : ℝ) (m : ℕ) (α : Measure ℝ)
    (hv : ValidReference α ρ (medianBaseBudget B m)) (hB : 0 < B)
    (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (hq : RarePrior μ ρ q)
    (hdom : ∀ x, cdf (μ.map Subtype.val) x ≤ cdf α x) :
    ((originalSimulationLaw μ ((medianStage ρ B m).endpoint false) q).map
      (fun z => (medianStage ρ B m).interval α z.1
        (readBlock (medianStage ρ B m).continuationCost
          ((medianStage ρ B m).continuation α z.1) z.2).1))
      (intervalFailure (signMean μ q.val)) ≤ ENNReal.ofReal ((3/4:ℝ)^m/2) := by
  rw [medianStage_fixed_interval_law]
  let A := cappedMedian (referenceBase α ρ (medianBaseBudget B m)) m (medianCopyCap B m) ρ
  have hm : Measurable (fun z : (ℕ → ReferenceSeed α ρ (medianBaseBudget B m)) × Table =>
      A.output (z.1, populationPath (A.policy z.1) z.2)) :=
    A.output_measurable.comp (measurable_fst.prodMk
      (measurable_seeded_populationPath A.policy
        (fun w => measurable_to_countable' (A.policy_measurable w))))
  rw [Measure.map_apply ((hm.sub_const _).prodMk (hm.add_const _))
    (measurableSet_intervalFailure _)]
  have he : (fun z : (ℕ → ReferenceSeed α ρ (medianBaseBudget B m)) × Table =>
      (A.output (z.1,populationPath (A.policy z.1) z.2) - medianRadius α ρ B m,
      A.output (z.1,populationPath (A.policy z.1) z.2) + medianRadius α ρ B m)) ⁻¹'
      intervalFailure (signMean μ q.val) =
      {z | medianRadius α ρ B m < |A.output (z.1,populationPath (A.policy z.1) z.2)-signMean μ q.val|} := by
    ext z
    exact intervalFailure_center _ _ _
  rw [he, ← failureProbability_simulation]
  exact (reference_median_coverage α ρ B m hv hB μ q hq hdom).2

def paidMedianStage (ρ B : ℝ) (m J k : ℕ) : LearnedStage (MedianSeed ρ B m) :=
  pilotStage (medianStage ρ B m) J k ρ

theorem median_reservations_le {B : ℝ} (hB : 0 < B) (m : ℕ) :
    (2*m+1) * medianCopyCap B m ≤ ⌊B⌋₊ := by
  have hc : 0 < 2 * (m : ℝ) + 1 := by positivity
  have hn := Nat.floor_le (div_nonneg hB.le hc.le)
  apply Nat.le_floor
  push_cast
  unfold medianCopyCap
  nlinarith [(le_div_iff₀ hc).mp hn]

/-- The cap includes the paid pilot on every path, whether or not its
certificates cover the true law, and whether or not a copy times out. -/
theorem paidMedianStage_cap {ρ B : ℝ} (hB : 0 < B) (m J k : ℕ) (upper : Bool) :
    PathwiseCap ((paidMedianStage ρ B m J k).endpoint upper) (k * pilotSpan J + ⌊B⌋₊) := by
  intro z x hx
  exact (pilotStage_pathwise (medianStage ρ B m) J k ρ upper z x hx).trans
    (by exact_mod_cast Nat.add_le_add_left (median_reservations_le hB m) (k * pilotSpan J))

/-- The reported radius depends only on the learned pilot law and design
parameters. This identity also holds for failed pilot and continuation paths. -/
theorem paidMedianStage_reported_radius (ρ B : ℝ) (m J k : ℕ)
    (r : MedianSeed ρ B m) (w : List Bool) :
    let S := paidMedianStage ρ B m J k
    (S.historyInterval r w).2 - (S.historyInterval r w).1 =
      2 * medianRadius (S.learnedLaw (w.take S.pilotCost)) ρ B m :=
  medianStage_radius ρ B m _ r _

theorem paidMedianStage_fixed_failure {ρ B : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (hB : 0 < B) (m J k : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (hq : RarePrior μ ρ q) (xs : List Bool)
    (hdom : ∀ x, (μ.map Subtype.val) (Set.Iic x) ≤
      (paidMedianStage ρ B m J k).learnedLaw xs (Set.Iic x)) :
    let S := paidMedianStage ρ B m J k
    ((originalSimulationLaw μ (S.endpoint false) q).map
      (fun z => S.interval (S.learnedLaw xs) z.1
        (readBlock S.continuationCost (S.continuation (S.learnedLaw xs) z.1) z.2).1))
      (intervalFailure (signMean μ q.val)) ≤ ENNReal.ofReal ((3/4:ℝ)^m/2) := by
  let S := paidMedianStage ρ B m J k
  have : IsProbabilityMeasure (S.learnedLaw xs) := S.learnedLaw_probability xs
  have : IsProbabilityMeasure (μ.map Subtype.val) := inferInstance
  apply medianStage_fixed_failure ρ B m (S.learnedLaw xs)
    (learnedLaw_valid S xs m hρ hρ4 hB) hB μ q hq
  intro x
  rw [cdf_eq_real, cdf_eq_real]
  exact ENNReal.toReal_mono (measure_ne_top _ _) (hdom x)

/-- Conditional coverage of the interval actually reported by the paid stage,
given any positive-probability chronological pilot prefix with valid CDF coverage. -/
theorem paidMedianStage_conditional_coverage {ρ B : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (hB : 0 < B) (m J k : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (hq : RarePrior μ ρ q) (xs : List Bool)
    (hdom : ∀ x, (μ.map Subtype.val) (Set.Iic x) ≤
      (paidMedianStage ρ B m J k).learnedLaw xs (Set.Iic x))
    (hxs : (experimentLaw μ ((paidMedianStage ρ B m J k).endpoint false) q)
      {z | (processHistory z.2 (paidMedianStage ρ B m J k).cap).take
        (paidMedianStage ρ B m J k).pilotCost = xs} ≠ 0) :
    let S := paidMedianStage ρ B m J k
    ((((experimentLaw μ (S.endpoint false) q)
      {z | (processHistory z.2 S.cap).take S.pilotCost = xs})⁻¹ •
      (experimentLaw μ (S.endpoint false) q).restrict
        {z | (processHistory z.2 S.cap).take S.pilotCost = xs}).map
      (fun z => ((S.endpoint false).output (z.1.1,z.2), (S.endpoint true).output (z.1.1,z.2))))
      (intervalFailure (signMean μ q.val)) ≤ ENNReal.ofReal ((3/4:ℝ)^m/2) := by
  dsimp only
  rw [original_conditional_interval_law _ μ q xs hxs]
  exact paidMedianStage_fixed_failure hρ hρ4 hB m J k μ q hq xs hdom

theorem paidMedianStage_pilot_failure {ρ B ε : ℝ} (hρ : 0 < ρ) (m J k : ℕ)
    (hJ : 1 ≤ J) (hk : 0 < k) (hε : 0 < ε) (hkε : 8 * Real.log (2 * (J : ℝ) / ε) ≤ k)
    (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) :
    let S := paidMedianStage ρ B m J k
    (originalSimulationLaw μ (S.endpoint false) q)
      {z | ¬∀ x, (μ.map Subtype.val) (Set.Iic x) ≤
        S.learnedLaw (readBlock S.pilotCost S.pilot (z.2 ∘ Nat.pair 0)).1 (Set.Iic x)} ≤
      ENNReal.ofReal ε := by
  let S := paidMedianStage ρ B m J k
  let T := Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q)
  let good := fun xs => ∀ x, (μ.map Subtype.val) (Set.Iic x) ≤ S.learnedLaw xs (Set.Iic x)
  let E := {ω : Table | good (pilotStageWord J k ρ ω)}
  have hE : MeasurableSet E := (Set.to_countable {xs | good xs}).measurableSet.preimage
    ((measurable_pilot_word (pilotCost J k) (pilotReader J k (pilotCoinCap J ρ))).comp (by fun_prop))
  have hp : 1 - ε ≤ T.real E :=
    (original_pilotStage_event μ q (medianStage ρ B m) J k hρ hJ hk hε hkε).trans
      (measureReal_mono (fun _ h => h.2))
  have he : T Eᶜ ≤ ENNReal.ofReal ε := by
    apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal hε.le]
    change T.real Eᶜ ≤ ε
    rw [measureReal_compl hE]
    simpa using (show 1 - T.real E ≤ ε by linarith)
  change (S.randomLaw.prod T) (Prod.snd ⁻¹' Eᶜ) ≤ _
  rw [← Measure.map_apply measurable_snd hE.compl, Measure.map_snd_prod]
  simpa only [show S.randomLaw univ = 1 from S.probability.measure_univ,
    one_smul] using he

/-- The actual installed paid stage fails with probability at most the sum
of the pilot's error and the amplified continuation error. -/
theorem paidMedianStage_coverage {ρ B ε : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (hB : 0 < B) (m J k : ℕ) (hJ : 1 ≤ J) (hk : 0 < k) (hε : 0 < ε)
    (hkε : 8 * Real.log (2 * (J : ℝ) / ε) ≤ k)
    (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (hq : RarePrior μ ρ q) :
    let S := paidMedianStage ρ B m J k
    ((experimentLaw μ (S.endpoint false) q).map (fun z =>
      ((S.endpoint false).output (z.1.1,z.2), (S.endpoint true).output (z.1.1,z.2))))
      (intervalFailure (signMean μ q.val)) ≤ ENNReal.ofReal ε + ENNReal.ofReal ((3/4:ℝ)^m/2) := by
  let S := paidMedianStage ρ B m J k
  apply (learnedStage_failure_le μ S q
    (fun xs => ∀ x, (μ.map Subtype.val) (Set.Iic x) ≤ S.learnedLaw xs (Set.Iic x))
    (signMean μ q.val) (ENNReal.ofReal ((3/4:ℝ)^m/2))
    (paidMedianStage_fixed_failure hρ hρ4 hB m J k μ q hq)).trans
  exact add_le_add (paidMedianStage_pilot_failure (B := B) hρ m J k hJ hk hε hkε μ q) le_rfl

theorem paidMedianStage_at_level {ρ B ε δ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (hB : 0 < B) (hδ : 0 < δ) (J k : ℕ) (hJ : 1 ≤ J) (hk : 0 < k) (hε : 0 < ε)
    (hkε : 8 * Real.log (2 * (J : ℝ) / ε) ≤ k)
    (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (hq : RarePrior μ ρ q) :
    let S := paidMedianStage ρ B (groups δ) J k
    PathwiseCap (S.endpoint false) (k * pilotSpan J + ⌊B⌋₊) ∧
    ((experimentLaw μ (S.endpoint false) q).map (fun z =>
      ((S.endpoint false).output (z.1.1,z.2), (S.endpoint true).output (z.1.1,z.2))))
      (intervalFailure (signMean μ q.val)) ≤ ENNReal.ofReal (ε + δ) := by
  refine ⟨paidMedianStage_cap hB _ _ _ false, ?_⟩
  apply (paidMedianStage_coverage hρ hρ4 hB (groups δ) J k hJ hk hε hkε μ q hq).trans
  rw [ENNReal.ofReal_add hε.le hδ.le]
  exact add_le_add le_rfl (ENNReal.ofReal_le_ofReal (schedule_failure hδ))

end ThresholdHC.RobustContinuation
