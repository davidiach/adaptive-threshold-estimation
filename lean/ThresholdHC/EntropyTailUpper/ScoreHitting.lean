import ThresholdHC.EntropyTailUpper.PredictableWald
import ThresholdHC.EntropyTailUpper.ReferenceDrift
import ThresholdHC.ObservableSimulation.OriginalExperiment

/-! Expected work of a capped likelihood-score crossing, obtained by bounded
Wald and a pathwise overshoot bound. This avoids an integrability assumption
on the uncapped crossing time. -/

noncomputable section
open MeasureTheory Real
open scoped BigOperators

namespace ThresholdHC.EntropyTailUpper
open ThresholdHC.Tier2 ThresholdHC.Tier6 ThresholdHC.ObservableSimulation

def scoreTest (f : Bool → ℝ) (b : ℝ) (n : ℕ) (w : Fin n → Bool) : Prop :=
  b ≤ ∑ i, f (w i)

def scoreStop (f : Bool → ℝ) (b : ℝ) (M : ℕ) : (ℕ → Bool) → ℕ :=
  prefixSearchCost (scoreTest f b) M

theorem scoreTest_prefix (f : Bool → ℝ) (b : ℝ) (n : ℕ) (ω : ℕ → Bool) :
    scoreTest f b n (tapePrefix n ω) ↔ b ≤ ∑ i ∈ Finset.range n, f (ω i) := by
  simp only [scoreTest, tapePrefix, ← Fin.sum_univ_eq_sum_range]

theorem scoreStop_overshoot (f : Bool → ℝ) {b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hf : ∀ x, f x ≤ c) (M : ℕ) (ω : ℕ → Bool) :
    (∑ i ∈ Finset.range (scoreStop f b M ω), f (ω i)) ≤ b+c := by
  cases hτ : scoreStop f b M ω with
  | zero => simp only [Finset.range_zero, Finset.sum_empty]; positivity
  | succ k =>
    have hbefore := boundedFirst_before
      (fun n => scoreTest f b n (tapePrefix n ω)) M k
      (show k < scoreStop f b M ω by omega)
    rw [scoreTest_prefix] at hbefore
    rw [Finset.sum_range_succ]
    exact add_le_add (le_of_lt (lt_of_not_ge hbefore)) (hf _)

theorem integrable_scoreStop (p : unitInterval) (f : Bool → ℝ) (b : ℝ) (M : ℕ) :
    Integrable (fun ω => (scoreStop f b M ω : ℝ)) (tapeMeasure p) := by
  apply Integrable.of_bound
    ((measurable_of_countable (fun n : ℕ => (n:ℝ))).comp
      (measurable_prefixSearchCost (scoreTest f b) M)).aestronglyMeasurable M
  refine ae_of_all _ (fun ω => ?_)
  change ‖(scoreStop f b M ω : ℝ)‖ ≤ (M:ℝ)
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast prefixSearchCost_le (scoreTest f b) M ω

theorem integrable_stopped_score (p : unitInterval) (f : Bool → ℝ) (b : ℝ) (M : ℕ) :
    Integrable (fun ω => ∑ i ∈ Finset.range (scoreStop f b M ω), f (ω i)) (tapeMeasure p) := by
  simp_rw [stopped_sum_eq f (scoreStop f b M) M (prefixSearchCost_le (scoreTest f b) M)]
  exact integrable_finsetSum _ (fun i _ => integrable_survives_score p f
    (prefixSearchCost_ext (scoreTest f b) M) i)

theorem scoreStop_expected_mul_drift_le (p : unitInterval) (f : Bool → ℝ) {b c : ℝ}
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hf : ∀ x, f x ≤ c) (M : ℕ) :
    (∫ ω, (scoreStop f b M ω : ℝ) ∂tapeMeasure p) * bitScoreMean p f ≤ b+c := by
  rw [← bounded_wald p f (scoreStop f b M) M (prefixSearchCost_le (scoreTest f b) M)
    (prefixSearchCost_ext (scoreTest f b) M)]
  simpa using integral_mono (integrable_stopped_score p f b M) (integrable_const (b+c))
    (scoreStop_overshoot f hb hc hf M)

def negativeBitScore (r : ℝ) (x : Bool) : ℝ :=
  if x then log (1-2*r) else log (1+2*r)

theorem negativeBitScore_le_one {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1/4) (x : Bool) :
    negativeBitScore r x ≤ 1 := by
  cases x
  · exact (reference_log_overshoot hr0 hr1).le
  · apply le_trans (log_nonpos (by linarith : 0 ≤ 1-2*r) (by linarith))
    norm_num

theorem negativeBitScore_mean (d : Gap) (r : ℝ) :
    bitScoreMean (gapParameter false d) (negativeBitScore r) = negativeReferenceDrift d r := by
  simp only [bitScoreMean, gapParameter, Bool.false_eq_true, ite_false, negativeBitScore, ite_true,
    negativeReferenceDrift]
  ring

theorem negative_scoreStop_work (d : Gap) {r b : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1/4)
    (hdr : (d:ℝ)/2 ≤ r) (hrd : r ≤ (d:ℝ)) (hb : 0 ≤ b) (M : ℕ) :
    (∫ ω, (scoreStop (negativeBitScore r) b M ω : ℝ) ∂tapeMeasure (gapParameter false d)) ≤
      (3/(4*(d:ℝ)^2))*(1+b) := by
  have hw := scoreStop_expected_mul_drift_le (gapParameter false d) (negativeBitScore r)
    hb (by norm_num : (0:ℝ) ≤ 1) (negativeBitScore_le_one hr0 hr1) M
  rw [negativeBitScore_mean] at hw
  have hm := negativeReferenceDrift_lower d.property.1.le hr0 hr1 hdr hrd
  have hn : 0 ≤ ∫ ω, (scoreStop (negativeBitScore r) b M ω : ℝ)
      ∂tapeMeasure (gapParameter false d) := integral_nonneg (fun _ => Nat.cast_nonneg _)
  have hs := mul_le_mul_of_nonneg_left hm hn
  have hd2 : 0 < (d:ℝ)^2 := sq_pos_of_pos d.property.1
  calc
    _ ≤ (3*(1+b))/(4*(d:ℝ)^2) := (le_div_iff₀ (by positivity)).mpr (by nlinarith)
    _ = _ := by ring

end ThresholdHC.EntropyTailUpper
