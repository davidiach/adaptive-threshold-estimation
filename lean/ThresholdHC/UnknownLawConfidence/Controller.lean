import ThresholdHC.UnknownLawConfidence.Sample

/-! The ladder of stages in the original observable experiment.

Every stage buys `n m <= c_j` flips, so the controller at budget `B` respects
the cap `B`; controllers at different budgets agree on shared prefixes and
report nested intervals inside `[0,u]`. The failure allowances `delta_j` sum
to `delta`, so one event of probability at least `1 - delta` protects every
stage at once: there each stage interval covers `theta` and has width at most
its stage bound, and so do all running intersections. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal
namespace ThresholdHC.UnknownLawConfidence
open ThresholdHC.Tier6 ThresholdHC.HardBudget ThresholdHC.ObservableSimulation
open ThresholdHC.ArbitraryLawAdaptation ThresholdHC.ArbitraryLawController

theorem stage_cap (δ : ℝ) (j : ℕ) : (stage δ j).cap ≤ stageCap j := by
  change 0 + itemCount j * flipCount j ≤ stageCap j
  rw [zero_add]
  exact itemCount_mul_flipCount_le j

theorem controller_cap (δ u : ℝ) (B : ℕ) (upper : Bool) :
    PathwiseCap (controller δ u B upper) B := by
  simpa only [Nat.floor_natCast, controller] using
    endpoint_budget_cap (R := fun _ => Unit) (stage δ) u (stage_cap δ) (B : ℝ) upper

theorem count_mono {B C : ℕ} (h : B ≤ C) : stageCount (B : ℝ) ≤ stageCount (C : ℝ) := by
  have hf : paid (stageCount (B : ℝ)) ≤ ⌊(C : ℝ)⌋₊ := by
    simpa only [Nat.floor_natCast] using (paid_fits (B : ℝ)).trans (by simpa using h)
  exact Nat.le_findGreatest ((index_le_paid _).trans hf) hf

theorem controller_compatible (δ u : ℝ) {B C : ℕ} (h : B ≤ C)
    (upper upper' : Bool) (r : Seed) (xs : List Bool)
    (hx : xs.length < spent (R := fun _ => Unit) (stage δ) (stageCount (B : ℝ))) :
    (controller δ u C upper').policy r xs = (controller δ u B upper).policy r xs :=
  endpoint_policy_compatible _ _ (count_mono h) upper upper' r xs hx

theorem interval_eq (δ u : ℝ) (B : ℕ) (z : Seed × Table) :
    interval δ u B z =
      ArbitraryLawController.tableInterval (R := fun _ => Unit) (stage δ) u z.1 z.2
        (stageCount (B : ℝ)) :=
  observedInterval_eq _ _ _ _

theorem interval_nested (δ u : ℝ) {B C : ℕ} (h : B ≤ C) (z : Seed × Table) :
    (interval δ u B z).1 ≤ (interval δ u C z).1 ∧
      (interval δ u C z).2 ≤ (interval δ u B z).2 := by
  rw [interval_eq, interval_eq]
  exact tableInterval_nested _ _ _ _ (count_mono h)

theorem interval_range (δ u : ℝ) (B : ℕ) (z : Seed × Table) :
    0 ≤ (interval δ u B z).1 ∧ (interval δ u B z).2 ≤ u := by
  rw [interval_eq]
  exact tableInterval_nested (R := fun _ => Unit) (stage δ) u z.1 z.2 (Nat.zero_le _)

theorem controller_original_law (μ : Measure Gap) (q : SignLaw) (δ u : ℝ)
    (B : ℕ) (upper : Bool) :
    originalSimulationLaw μ (controller δ u B upper) q = streamLaw μ q δ := rfl

instance streamLaw_probability (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (δ : ℝ) : IsProbabilityMeasure (streamLaw μ q δ) := by
  unfold streamLaw
  infer_instance

/-- The sample events of stage `j`, on its seed and stage-local table. -/
def stageBad (μ : Measure Gap) (q : SignLaw) (δ : ℝ) (j : ℕ) : Set (Unit × Table) :=
  Prod.snd ⁻¹' sampleBad μ q δ j

theorem measurableSet_stageBad (μ : Measure Gap) (q : SignLaw) (δ : ℝ) (j : ℕ) :
    MeasurableSet (stageBad μ q δ j) :=
  measurable_snd (measurableSet_sampleBad μ q δ j)

theorem stage_failure (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    {δ : ℝ} (hδ : 0 < δ) (j : ℕ) :
    originalSimulationLaw μ ((stage δ j).endpoint false) q (stageBad μ q δ j) ≤
      ENNReal.ofReal (Anytime.stageFailure δ j) := by
  change ((Measure.dirac ()).prod (tableLaw μ q)) (Prod.snd ⁻¹' sampleBad μ q δ j) ≤ _
  rw [← Set.univ_prod, Measure.prod_prod, measure_univ, one_mul]
  exact sampleBad_le μ q hδ j

/-- No stage sees a sample event. -/
def goodEvent (μ : Measure Gap) (q : SignLaw) (δ : ℝ) : Set (Seed × Table) :=
  {z | ∀ j, stageInputs (R := fun _ => Unit) z j ∉ stageBad μ q δ j}

theorem goodEvent_failure (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    {δ : ℝ} (hδ : 0 < δ) :
    streamLaw μ q δ (goodEvent μ q δ)ᶜ ≤ ENNReal.ofReal δ := by
  let E (j : ℕ) := {z : Seed × Table | stageInputs (R := fun _ => Unit) z j ∈ stageBad μ q δ j}
  have he : (goodEvent μ q δ)ᶜ = ⋃ j, E j := by
    ext z
    simp only [goodEvent, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_not,
      Set.mem_iUnion, E]
  rw [he]
  apply Anytime.simultaneous_coverage _ E hδ.le
  intro j
  let base := fun j => (stage δ j).endpoint false
  let P := fun j => originalSimulationLaw μ (base j) q
  let _ (j : ℕ) : IsProbabilityMeasure (P j) := by
    dsimp [P, originalSimulationLaw]; infer_instance
  have hp := stageInputs_preserving (R := fun _ => Unit) base 0 0 μ q
  have hcoord := (measurePreserving_eval_infinitePi P j).comp hp
  change (originalSimulationLaw μ (estimator base 0 0) q)
    ((Function.eval j ∘ stageInputs) ⁻¹' stageBad μ q δ j) ≤ _
  rw [hcoord.measure_preimage (measurableSet_stageBad μ q δ j).nullMeasurableSet]
  exact stage_failure μ q hδ j

theorem goodEvent_probability (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    {δ : ℝ} (hδ : 0 < δ) :
    1 - ENNReal.ofReal δ ≤ streamLaw μ q δ (goodEvent μ q δ) := by
  have hb := goodEvent_failure μ q hδ
  have hu : streamLaw μ q δ Set.univ ≤
      streamLaw μ q δ (goodEvent μ q δ) + streamLaw μ q δ (goodEvent μ q δ)ᶜ := by
    rw [← Set.union_compl_self (goodEvent μ q δ)]
    exact measure_union_le _ _
  rw [measure_univ] at hu
  exact tsub_le_iff_right.mpr (hu.trans (add_le_add le_rfl hb))

theorem goodEvent_stage (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (δ : ℝ)
    {z : Seed × Table} (hz : z ∈ goodEvent μ q δ) (j : ℕ) :
    ((stage δ j).tableInterval (z.1 j) (z.2 ∘ Nat.pair j)).1 ≤ signMean μ q.val ∧
      signMean μ q.val ≤ ((stage δ j).tableInterval (z.1 j) (z.2 ∘ Nat.pair j)).2 ∧
      ((stage δ j).tableInterval (z.1 j) (z.2 ∘ Nat.pair j)).2 -
        ((stage δ j).tableInterval (z.1 j) (z.2 ∘ Nat.pair j)).1 ≤ widthBound μ δ j :=
  stageInterval_good μ q δ j (t := z.2 ∘ Nat.pair j) (hz j)

theorem goodEvent_coverage (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    {δ u : ℝ} (hu : signMean μ q.val ≤ u) {z : Seed × Table} (hz : z ∈ goodEvent μ q δ)
    (B : ℕ) :
    (interval δ u B z).1 ≤ signMean μ q.val ∧ signMean μ q.val ≤ (interval δ u B z).2 := by
  rw [interval_eq]
  apply tableInterval_coverage _ _ _ _ _ ⟨(signMean_bounds μ q).1, hu⟩
  intro j
  exact ⟨(goodEvent_stage μ q δ hz j).1, (goodEvent_stage μ q δ hz j).2.1⟩

theorem halfWidth_le_of_nested {I J : ℝ × ℝ} (h1 : J.1 ≤ I.1) (h2 : I.2 ≤ J.2) :
    Anytime.halfWidth I ≤ Anytime.halfWidth J := by
  unfold Anytime.halfWidth
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply max_le_max_left
  linarith

theorem widthBound_nonneg (μ : Measure Gap) (δ : ℝ) (j : ℕ) : 0 ≤ widthBound μ δ j := by
  have h1 := measureReal_nonneg (μ := μ) (s := {d : Gap | (d : ℝ) ≤ 2 * radius j})
  have h2 := sampling_nonneg δ j
  have h3 := (tolerance_pos j).le
  unfold widthBound
  positivity

theorem goodEvent_width (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (δ u : ℝ) {z : Seed × Table} (hz : z ∈ goodEvent μ q δ) (B j : ℕ)
    (hj : j < stageCount (B : ℝ)) :
    2 * Anytime.halfWidth (interval δ u B z) ≤ widthBound μ δ j := by
  rw [interval_eq]
  have hn := tableInterval_nested (R := fun _ => Unit) (stage δ) u z.1 z.2
    (show j + 1 ≤ stageCount (B : ℝ) by omega)
  have h1 := halfWidth_le_of_nested hn.1 hn.2
  have h2 := tableInterval_width (R := fun _ => Unit) (stage δ) u z.1 z.2 j
  have h3 := (goodEvent_stage μ q δ hz j).2.2
  have h4 : 2 * Anytime.halfWidth ((stage δ j).tableInterval (z.1 j) (z.2 ∘ Nat.pair j)) ≤
      widthBound μ δ j := by
    unfold Anytime.halfWidth
    rw [mul_div_cancel₀ _ two_ne_zero]
    exact max_le (widthBound_nonneg μ δ j) h3
  linarith

theorem goodEvent_subset (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    {δ u : ℝ} (hu : signMean μ q.val ≤ u) : goodEvent μ q δ ⊆ successEvent μ q δ u :=
  fun _ hz => ⟨goodEvent_coverage μ q hu hz, goodEvent_width μ q δ u hz⟩

theorem successEvent_probability (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    {δ u : ℝ} (hδ : 0 < δ) (hu : signMean μ q.val ≤ u) :
    1 - ENNReal.ofReal δ ≤ streamLaw μ q δ (successEvent μ q δ u) :=
  (goodEvent_probability μ q hδ).trans (measure_mono (goodEvent_subset μ q hu))

end ThresholdHC.UnknownLawConfidence
