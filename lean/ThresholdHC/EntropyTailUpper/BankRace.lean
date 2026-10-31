import ThresholdHC.EntropyTailUpper.ParityRace
import ThresholdHC.EntropyTailUpper.ReferenceLikelihood

/-! The weighted bank instantiated in the finite observable race. -/

noncomputable section
open MeasureTheory Set Real
open scoped ENNReal NNReal

namespace ThresholdHC.EntropyTailUpper
open ThresholdHC ThresholdHC.Tier2 ThresholdHC.Tier6 ThresholdHC.ObservableSimulation
open ThresholdHC.BlindUpper ThresholdHC.CriticalEntropy

def negativeBankTest (weights : ℕ → ℝ≥0) (ε : ℝ) : PrefixTest :=
  fun _ w => ∃ j, streamProb (1/2) w ≤
    (ε*(weights j:ℝ))*streamProb (1/2-EntropyTail.bandEdge j/2) w

def positiveBankTest (μ : Measure Gap) (weights : ℕ → ℝ≥0) (u : ℝ) : PrefixTest :=
  fun n w => allNegativeLaw μ (tapePrefix n ⁻¹' {w}) ≤
    ENNReal.ofReal u * positiveBankLaw weights (tapePrefix n ⁻¹' {w})

theorem ever_negativeBankTest (weights : ℕ → ℝ≥0) (ε : ℝ) :
    everPrefixHit (negativeBankTest weights ε) = negativeBankEvent weights ε := by
  ext ω
  simp only [everPrefixHit, negativeBankTest, negativeBankEvent, mem_iUnion, mem_ofPred_eq]
  exact exists_comm

theorem ever_positiveBankTest (μ : Measure Gap) (weights : ℕ → ℝ≥0) (u : ℝ) :
    everPrefixHit (positiveBankTest μ weights u) = positiveBankEvent μ weights u := rfl

def bankRace (μ : Measure Gap) (weights : ℕ → ℝ≥0) (ε u : ℝ) (L : ℕ) : StoppedProcedure Unit ℝ :=
  raceProcedure (negativeBankTest weights ε) (positiveBankTest μ weights u) L

theorem integrable_raceCost (neg pos : PrefixTest) (L : ℕ) (p : unitInterval) :
    Integrable (fun ω => (raceCost neg pos L ω : ℝ)) (tapeMeasure p) := by
  apply Integrable.of_bound
    ((measurable_of_countable (fun n : ℕ => (n:ℝ))).comp (measurable_raceCost neg pos L)).aestronglyMeasurable
    (2*(2^L))
  refine ae_of_all _ (fun ω => ?_)
  change ‖(raceCost neg pos L ω : ℝ)‖ ≤ 2*(2^L)
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast raceCost_le neg pos L ω

theorem parityTape_integral (b : Fin 2) (p : unitInterval) (F : (ℕ → Bool) → ℝ) (hF : Measurable F) :
    (∫ ω, F (parityTape b ω) ∂tapeMeasure p) = ∫ ω, F ω ∂tapeMeasure p := by
  rw [← integral_map (measurable_parityTape b).aemeasurable hF.aestronglyMeasurable,
    (parityTape_measurePreserving b p).map_eq]

theorem race_expected_work_le_ordinary (neg pos : PrefixTest) (L : ℕ) (d : Gap) (s : Bool) :
    (∫ ω, (raceCost neg pos L ω : ℝ) ∂tapeMeasure (gapParameter s d)) ≤
      2*ordinaryWorkKernel (ThresholdHC.Uniform713.cap L) (d:ℝ) := by
  have ho : Integrable (fun ω => (classifierStop L ω : ℝ)) (tapeMeasure (gapParameter s d)) := by
    apply Integrable.of_bound
      ((measurable_of_countable (fun n : ℕ => (n:ℝ))).comp (measurable_classifierStop L)).aestronglyMeasurable (2^L)
    refine ae_of_all _ (fun ω => ?_)
    change ‖(classifierStop L ω : ℝ)‖ ≤ 2^L
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast classifierStop_le L ω
  have hcomp := (parityTape_measurePreserving 1 (gapParameter s d)).integrable_comp_of_integrable ho
  have h := integral_mono (integrable_raceCost neg pos L _) (hcomp.const_mul 2)
    (fun ω => show (raceCost neg pos L ω : ℝ) ≤ 2*(classifierStop L (parityTape 1 ω) : ℝ) by
      exact_mod_cast Nat.mul_le_mul_left 2 (raceRounds_le_ordinary neg pos L ω))
  rw [integral_const_mul] at h
  dsimp only [Function.comp_apply] at h
  rw [parityTape_integral 1 _ (fun ω => (classifierStop L ω : ℝ))
    ((measurable_of_countable (fun n : ℕ => (n:ℝ))).comp (measurable_classifierStop L))] at h
  exact h.trans (mul_le_mul_of_nonneg_left (ordinary_conditional_work L d s) (by norm_num))

theorem bank_raceRounds_le_score (μ : Measure Gap) (weights : ℕ → ℝ≥0) {ε : ℝ}
    (hε : 0 < ε) (u : ℝ) (j L : ℕ) (hw : 0 < (weights j:ℝ)) (ω : ℕ → Bool) :
    raceRounds (negativeBankTest weights ε) (positiveBankTest μ weights u) L ω ≤
      scoreStop (negativeBitScore (EntropyTail.bandEdge j/2)) (log (ε*(weights j:ℝ))⁻¹)
        (2^L) (parityTape 0 ω) := by
  let f := negativeBitScore (EntropyTail.bandEdge j/2)
  let b := log (ε*(weights j:ℝ))⁻¹
  rcases (boundedFirst_spec (fun n => scoreTest f b n (tapePrefix n (parityTape 0 ω))) (2^L)).2 with h | h
  · apply raceRounds_le_bank
    apply Or.inl
    refine ⟨j, ?_⟩
    exact negative_score_crossing (by positivity [EntropyTail.bandEdge_pos j])
      (by linarith [bandEdge_le_half j]) (mul_pos hε hw) _ h
  · change scoreStop f b (2^L) (parityTape 0 ω) = 2^L at h
    change _ ≤ scoreStop f b (2^L) (parityTape 0 ω)
    rw [h]
    exact raceRounds_le _ _ L ω

theorem bank_race_negative_work (μ : Measure Gap) (weights : ℕ → ℝ≥0) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (u : ℝ) (j L : ℕ) (hw : 0 < (weights j:ℝ))
    (hw1 : (weights j:ℝ) ≤ 1) (d : Gap) (hd : d ∈ EntropyTail.band j) :
    (∫ ω, (raceCost (negativeBankTest weights ε) (positiveBankTest μ weights u) L ω : ℝ)
      ∂tapeMeasure (gapParameter false d)) ≤
      (3/(2*(d:ℝ)^2))*(1+log (ε*(weights j:ℝ))⁻¹) := by
  let f := negativeBitScore (EntropyTail.bandEdge j/2)
  let b := log (ε*(weights j:ℝ))⁻¹
  have hi := (parityTape_measurePreserving 0 (gapParameter false d)).integrable_comp_of_integrable
    (integrable_scoreStop (gapParameter false d) f b (2^L))
  have h := integral_mono (integrable_raceCost _ _ L _) (hi.const_mul 2)
    (fun ω => show (raceCost _ _ L ω : ℝ) ≤ 2*(scoreStop f b (2^L) (parityTape 0 ω) : ℝ) by
      exact_mod_cast Nat.mul_le_mul_left 2 (bank_raceRounds_le_score μ weights hε u j L hw ω))
  rw [integral_const_mul] at h
  dsimp only [Function.comp_apply] at h
  rw [parityTape_integral 0 _ (fun ω => (scoreStop f b (2^L) ω : ℝ))
    ((measurable_of_countable (fun n : ℕ => (n:ℝ))).comp (measurable_prefixSearchCost (scoreTest f b) (2^L)))] at h
  have hprod : ε*(weights j:ℝ) ≤ 1 :=
    (mul_le_mul_of_nonneg_right hε1 hw.le).trans (by simpa using hw1)
  have hb : 0 ≤ b := log_nonneg (one_le_inv₀ (mul_pos hε hw) |>.mpr hprod)
  have hwk := negative_scoreStop_work d (r := EntropyTail.bandEdge j/2)
    (by positivity [EntropyTail.bandEdge_pos j]) (by linarith [bandEdge_le_half j])
    (by linarith [hd.2]) hd.1.le hb (2^L)
  calc
    _ ≤ 2*(∫ ω, (scoreStop f b (2^L) ω : ℝ) ∂tapeMeasure (gapParameter false d)) := h
    _ ≤ 2*((3/(4*(d:ℝ)^2))*(1+b)) := mul_le_mul_of_nonneg_left hwk (by norm_num)
    _ = _ := by dsimp [b]; ring

end ThresholdHC.EntropyTailUpper
