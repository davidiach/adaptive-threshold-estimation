import ThresholdHC.LawAdaptation.Controller
import ThresholdHC.LawAdaptation.Transfer

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.LawAdaptation
open ThresholdHC.Tier6 ThresholdHC.HardBudget ThresholdHC.Anytime
open ThresholdHC.ObservableSimulation

variable {ι : Type} [Nonempty ι] {R : ι → ℕ → Type}
  [∀ i j, MeasurableSpace (R i j)]

/-- The same seed and physical coin table serve every observation budget. -/
def familyStreamLaw (μ : Measure Gap) (base : ∀ i j, AdaptiveEstimator (R i j))
    (q : SignLaw) : Measure ((∀ i j, R i j) × Table) :=
  (familySeedLaw base).prod (pilotTableLaw μ q)

instance familyStreamLaw_probability (μ : Measure Gap) [IsProbabilityMeasure μ]
    (base : ∀ i j, AdaptiveEstimator (R i j)) (q : SignLaw) :
    IsProbabilityMeasure (familyStreamLaw μ base q) := by
  unfold familyStreamLaw
  infer_instance

def branchInputs (n : ℕ) (i : ι) (z : (∀ i j, R i j) × Table) :
    (∀ j, R i j) × Table := (z.1 i,z.2 ∘ Nat.add n)

omit [Nonempty ι] in
/-- Each candidate's continuation sees its own oracle seed and untouched
population coins. No distribution conditional on selection is asserted. -/
theorem branchInputs_preserving (μ : Measure Gap) [IsProbabilityMeasure μ]
    (base : ∀ i j, AdaptiveEstimator (R i j)) (q : SignLaw) (n : ℕ) (i : ι) :
    MeasurePreserving (branchInputs (R := R) n i)
      (familyStreamLaw μ base q) (streamLaw μ (base i) q) := by
  have hs := measurePreserving_eval_infinitePi
    (fun i => Measure.infinitePi (fun j => (base i j).randomLaw)) i
  have ht : MeasurePreserving (fun s : Table => s ∘ Nat.add n)
      (pilotTableLaw μ q) (pilotTableLaw μ q) := by
    refine ⟨by fun_prop,?_⟩
    exact Measure.map_infinitePi_infinitePi_of_inj (fun _ _ h => Nat.add_left_cancel h)
  exact hs.prod ht

theorem family_pilot_error (laws : ι → Measure Gap) [∀ i, IsProbabilityMeasure (laws i)]
    (base : ∀ i j, AdaptiveEstimator (R i j)) (truth : ι) (q : SignLaw)
    {m n : ℕ} (hn : 0 < n) {η : ℝ} (hη : 0 < η)
    (hdist : ∀ i j, i ≠ j → ∃ k : Fin m,
      η ≤ |evenMoment (laws i) (k.val+1)-evenMoment (laws j) (k.val+1)|) :
    (familyStreamLaw (laws truth) base q)
      {z | chosenTable laws n m η z.2 ≠ truth} ≤
      ENNReal.ofReal (2*(m:ℝ)*Real.exp (-(n:ℝ)*η^2/32)) := by
  have hp : MeasurePreserving Prod.snd (familyStreamLaw (laws truth) base q)
      (pilotTableLaw (laws truth) q) :=
    measurePreserving_snd (μ := familySeedLaw base) (ν := pilotTableLaw (laws truth) q)
  have h := Measure.le_map_apply (μ := familyStreamLaw (laws truth) base q) hp.measurable.aemeasurable
    {s | chosenTable laws n m η s ≠ truth}
  rw [hp.map_eq] at h
  exact h.trans (original_pilot_error laws truth q hn hη hdist)

/-- All stages of the physically selected continuation cover simultaneously,
except on pilot error or true-law oracle error. There is no union over laws. -/
theorem post_all_stage_coverage
    (laws : ι → Measure Gap) [∀ i, IsProbabilityMeasure (laws i)]
    (base : ∀ i j, AdaptiveEstimator (R i j)) (truth : ι) (q : SignLaw)
    {m n : ℕ} (hn : 0 < n) {η : ℝ} (hη : 0 < η)
    (hdist : ∀ i j, i ≠ j → ∃ k : Fin m,
      η ≤ |evenMoment (laws i) (k.val+1)-evenMoment (laws j) (k.val+1)|)
    (M : ℝ) (rad : ι → ℕ → ℝ) {δ : ℝ} (hd : 0 ≤ δ)
    (hθ : 0 ≤ signMean (laws truth) q.val ∧ signMean (laws truth) q.val ≤ M)
    (hcap : ∀ j, PathwiseCap (base truth j) (stageCap j))
    (hf : ∀ j, ThresholdHC.Confidence.failureProbability (laws truth) (base truth j) q
      (rad truth j) ≤ ENNReal.ofReal (stageFailure δ j)) :
    (familyStreamLaw (laws truth) base q) {z | ∃ k,
      ¬ ((postTableInterval laws n m η M base rad z.1 z.2 k).1 ≤ signMean (laws truth) q.val ∧
        signMean (laws truth) q.val ≤ (postTableInterval laws n m η M base rad z.1 z.2 k).2)} ≤
      ENNReal.ofReal (2*(m:ℝ)*Real.exp (-(n:ℝ)*η^2/32)) + ENNReal.ofReal δ := by
  let good (i : ι) (z : (∀ i j, R i j) × Table) :=
    ∀ k, (tableInterval (base i) M (rad i) (z.1 i) (z.2 ∘ Nat.add n) k).1 ≤
      signMean (laws truth) q.val ∧ signMean (laws truth) q.val ≤
      (tableInterval (base i) M (rad i) (z.1 i) (z.2 ∘ Nat.add n) k).2
  have hp := family_pilot_error laws base truth q hn hη hdist
  have ho : (familyStreamLaw (laws truth) base q) {z | ¬ good truth z} ≤ ENNReal.ofReal δ := by
    have hpres := branchInputs_preserving (laws truth) base q n truth
    let E := {z : (∀ j, R truth j) × Table | ∃ k,
      ¬ ((tableInterval (base truth) M (rad truth) z.1 z.2 k).1 ≤ signMean (laws truth) q.val ∧
        signMean (laws truth) q.val ≤ (tableInterval (base truth) M (rad truth) z.1 z.2 k).2)}
    have h := Measure.le_map_apply (μ := familyStreamLaw (laws truth) base q)
      hpres.measurable.aemeasurable E
    rw [hpres.map_eq] at h
    have he : {z | ¬ good truth z} = branchInputs n truth ⁻¹' E := by
      ext z
      simp only [good,E,branchInputs,Set.mem_preimage,Set.mem_ofPred_eq,not_forall]
    rw [he]
    exact h.trans (all_stage_coverage (laws truth) (base truth) q M (rad truth) hd hθ hcap hf)
  have h := selected_failure_bound (familyStreamLaw (laws truth) base q)
    (fun z => chosenTable laws n m η z.2) truth good hp ho
  simpa only [good,postTableInterval,not_forall] using h

end ThresholdHC.LawAdaptation

