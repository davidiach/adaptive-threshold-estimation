import ThresholdHC.UnknownLawConfidence.Limit

/-! The unknown-law confidence sequence of `docs/UNKNOWN_LAW_CONFIDENCE.md`.

The procedure uses neither the gap law nor a bound on its small-gap tail. For
every probability law of positive gaps and every measurable gap-dependent
sign law, and for a supplied bound `u >= theta` (or for `u = 1`), one event of
probability at least `1 - delta` gives coverage at every integer budget and
the stage bound `P(D <= 2r) + 3a + 3tau` at every completed stage, and the
reported width tends to zero on that event. The event is measurable
(`measurableSet_successEvent`), so its probability is a measure, not an outer
measure. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
namespace ThresholdHC.UnknownLawConfidence
open ThresholdHC.Tier6

/-- The success event is measurable. -/
theorem measurableSet_successEvent (μ : Measure Gap) (q : SignLaw) (δ u : ℝ) :
    MeasurableSet (successEvent μ q δ u) := by
  have hm (B : ℕ) : Measurable (interval δ u B) :=
    ThresholdHC.ArbitraryLawController.measurable_observedInterval _ _ _
  have hw (B : ℕ) : Measurable (fun z => ThresholdHC.Anytime.halfWidth (interval δ u B z)) := by
    unfold ThresholdHC.Anytime.halfWidth
    exact (measurable_const.max ((hm B).snd.sub (hm B).fst)).div_const 2
  unfold successEvent
  simp only [Set.ofPred_and, Set.ofPred_forall]
  apply MeasurableSet.inter
  · apply MeasurableSet.iInter
    intro B
    exact (measurableSet_le (hm B).fst measurable_const).inter
      (measurableSet_le measurable_const (hm B).snd)
  · apply MeasurableSet.iInter
    intro B
    apply MeasurableSet.iInter
    intro j
    apply MeasurableSet.iInter
    intro _
    exact measurableSet_le ((hw B).const_mul 2) measurable_const

theorem unknown_law_confidence : UnknownLawConfidenceStatement := by
  intro δ u hδ hδ1
  refine ⟨controller_cap δ u, fun _ _ h => controller_compatible δ u h,
    fun _ _ h => interval_nested δ u h, interval_range δ u, ?_, ?_, ?_⟩
  · intro μ _ q
    exact ⟨controller_original_law μ q δ u, fun hu => successEvent_probability μ q hδ hu,
      successEvent_probability μ q hδ (signMean_bounds μ q).2⟩
  · intro μ _
    exact widthBound_tendsto μ hδ hδ1.le
  · intro μ _ q z hz
    exact successEvent_halfWidth_tendsto μ q hδ hδ1.le hz

theorem unknown_law_stopping : UnknownLawStoppingStatement :=
  fun _ _ _ _ _ hz τ => ⟨hz.1 (τ _), hz.2 (τ _)⟩

end ThresholdHC.UnknownLawConfidence
