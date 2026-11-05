import ThresholdHC.Anytime.Coverage
import ThresholdHC.Anytime.Compatibility
import ThresholdHC.Anytime.Width

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.Anytime
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.EntropyTail
open ThresholdHC.HardBudget ThresholdHC.ObservableSimulation

variable {R : ℕ → Type} [∀ j, MeasurableSpace (R j)]

/-- Two observable statistics of the same stopped history. -/
def observedInterval (base : ∀ j, AdaptiveEstimator (R j)) (M : ℝ) (radius : ℕ → ℝ)
    (k : ℕ) (z : (∀ j, R j) × Table) : ℝ × ℝ :=
  let x := populationPath ((endpointEstimator base M radius k false).policy z.1) z.2
  ((endpointEstimator base M radius k false).output (z.1,x),
    (endpointEstimator base M radius k true).output (z.1,x))

theorem measurable_observedInterval (base : ∀ j, AdaptiveEstimator (R j)) (M : ℝ) (radius : ℕ → ℝ) (k : ℕ) :
    Measurable (observedInterval base M radius k) := by
  let A := endpointEstimator base M radius k false
  have hm : Measurable (fun z : (∀ j, R j) × Table => (z.1,populationPath (A.policy z.1) z.2)) :=
    measurable_fst.prodMk (measurable_seeded_populationPath A.policy
      (fun xs => measurable_to_countable' (A.policy_measurable xs)))
  exact (A.output_measurable.comp hm).prodMk ((endpointEstimator base M radius k true).output_measurable.comp hm)

theorem observedInterval_eq (base : ∀ j, AdaptiveEstimator (R j)) (M : ℝ) (radius : ℕ → ℝ)
    (k : ℕ) (z : (∀ j, R j) × Table) :
    observedInterval base M radius k z = tableInterval base M radius z.1 z.2 k := by
  dsimp only [observedInterval]
  rw [endpoint_output,show (endpointEstimator base M radius k false).policy = (endpointEstimator base M radius k true).policy from rfl,
    endpoint_output]
  rfl

theorem endpoint_budget_cap (base : ∀ j, AdaptiveEstimator (R j)) (M : ℝ) (radius : ℕ → ℝ)
    (B : ℝ) (upper : Bool) :
    PathwiseCap (endpointEstimator base M radius (stageCount B) upper) ⌊B⌋₊ := by
  intro r x hx
  exact (endpoint_cap base M radius (stageCount B) upper r x hx).trans (Nat.cast_le.mpr (paid_fits B))

theorem selected_budget_coverage (μ : Measure Gap) [IsProbabilityMeasure μ]
    (base : ∀ j, AdaptiveEstimator (R j)) (q : SignLaw) (M : ℝ) (radius : ℕ → ℝ) {δ : ℝ}
    (hd : 0 ≤ δ) (hθ : 0 ≤ signMean μ q.val ∧ signMean μ q.val ≤ M)
    (hcap : ∀ j, PathwiseCap (base j) (stageCap j))
    (hf : ∀ j, ThresholdHC.Confidence.failureProbability μ (base j) q (radius j) ≤ ENNReal.ofReal (stageFailure δ j))
    (τ : ((∀ j, R j) × Table) → ℝ) :
    (streamLaw μ base q) {z | ¬ ((observedInterval base M radius (stageCount (τ z)) z).1 ≤ signMean μ q.val ∧
      signMean μ q.val ≤ (observedInterval base M radius (stageCount (τ z)) z).2)} ≤ ENNReal.ofReal δ := by
  simp_rw [observedInterval_eq]
  exact stopped_stage_coverage μ base q M radius hd hθ hcap hf (fun z => stageCount (τ z))

theorem simultaneous_probability (μ : Measure Gap) [IsProbabilityMeasure μ]
    (base : ∀ j, AdaptiveEstimator (R j)) (q : SignLaw) (M : ℝ) (radius : ℕ → ℝ) {δ : ℝ}
    (hd : 0 ≤ δ) (hθ : 0 ≤ signMean μ q.val ∧ signMean μ q.val ≤ M)
    (hcap : ∀ j, PathwiseCap (base j) (stageCap j))
    (hf : ∀ j, ThresholdHC.Confidence.failureProbability μ (base j) q (radius j) ≤ ENNReal.ofReal (stageFailure δ j)) :
    1-ENNReal.ofReal δ ≤ (streamLaw μ base q) {z | ∀ k,
      (observedInterval base M radius k z).1 ≤ signMean μ q.val ∧
      signMean μ q.val ≤ (observedInterval base M radius k z).2} := by
  let G := {z : (∀ j, R j) × Table | ∀ k, (observedInterval base M radius k z).1 ≤ signMean μ q.val ∧
      signMean μ q.val ≤ (observedInterval base M radius k z).2}
  have hG : MeasurableSet G := by
    simp only [G,Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro k
    exact (measurableSet_le (measurable_observedInterval base M radius k).fst measurable_const).inter
      (measurableSet_le measurable_const (measurable_observedInterval base M radius k).snd)
  have hb := all_stage_coverage μ base q M radius hd hθ hcap hf
  have he : Gᶜ = {z | ∃ k, ¬ ((tableInterval base M radius z.1 z.2 k).1 ≤ signMean μ q.val ∧
      signMean μ q.val ≤ (tableInterval base M radius z.1 z.2 k).2)} := by
    ext z
    simp only [G,Set.mem_compl_iff,Set.mem_ofPred_eq,not_forall,observedInterval_eq]
  rw [← he,measure_compl hG (measure_ne_top _ _),measure_univ] at hb
  change 1-ENNReal.ofReal δ ≤ (streamLaw μ base q) G
  apply tsub_le_iff_left.mpr
  simpa only [add_comm] using tsub_le_iff_left.mp hb

/-- One stage family supplies simultaneous coverage, valid data-dependent
stopping and the iterated-logarithm width. The controller's cap and
history compatibility are unconditional pathwise theorems above. -/
theorem known_anytime (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ δ : ℝ}
    (hr : 0 < ρ) (hu : ρ ≤ 1/4) (hd : 0 < δ) (hd' : δ ≤ 1/4) :
    ∃ (R : ℕ → Type) (_ : ∀ j, MeasurableSpace (R j)) (base : ∀ j, AdaptiveEstimator (R j)),
      (∀ B : ℝ, ∀ upper : Bool, PathwiseCap (endpointEstimator base ρ (radius μ ρ δ) (stageCount B) upper) ⌊B⌋₊) ∧
      (∀ q : SignLaw, RarePrior μ ρ q →
        (streamLaw μ base q) {z | ∃ k, ¬ ((observedInterval base ρ (radius μ ρ δ) k z).1 ≤ signMean μ q.val ∧
          signMean μ q.val ≤ (observedInterval base ρ (radius μ ρ δ) k z).2)} ≤ ENNReal.ofReal δ) ∧
      (∀ q : SignLaw, RarePrior μ ρ q → ∀ τ : ((∀ j, R j) × Table) → ℝ,
        (streamLaw μ base q) {z | ¬ ((observedInterval base ρ (radius μ ρ δ) (stageCount (τ z)) z).1 ≤ signMean μ q.val ∧
          signMean μ q.val ≤ (observedInterval base ρ (radius μ ρ δ) (stageCount (τ z)) z).2)} ≤ ENNReal.ofReal δ) ∧
      (∀ B : ℝ, 1 ≤ B → ∀ z : (∀ j, R j) × Table,
        halfWidth (observedInterval base ρ (radius μ ρ δ) (stageCount B) z) ≤
          1500002*(selection μ ρ (B/inflation B δ)).toReal) := by
  obtain ⟨R,mR,base,h⟩ := known_stages μ hr hu hd hd'
  let (j : ℕ) := mR j
  refine ⟨R,mR,base,endpoint_budget_cap base ρ (radius μ ρ δ),?_,?_,?_⟩
  · intro q hq
    simp_rw [observedInterval_eq]
    exact all_stage_coverage μ base q ρ (radius μ ρ δ) hd.le ⟨(signMean_bounds μ q).1,hq⟩
      (fun j => (h j).1) (fun j => (h j).2 q hq)
  · intro q hq τ
    exact selected_budget_coverage μ base q ρ (radius μ ρ δ) hd.le ⟨(signMean_bounds μ q).1,hq⟩
      (fun j => (h j).1) (fun j => (h j).2 q hq) τ
  · intro B hB z
    rw [observedInterval_eq]
    exact all_budget_width μ base hr hu hB hd hd' z.1 z.2

end ThresholdHC.Anytime
