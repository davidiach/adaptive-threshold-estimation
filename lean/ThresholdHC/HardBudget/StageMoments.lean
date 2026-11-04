import ThresholdHC.HardBudget.Controller

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.HardBudget
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.ObservableSimulation ThresholdHC.BlindUpper
open ThresholdHC.StoppingProgram

abbrev Outcome := Bool × ℝ

def observed {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (n : ℕ) (M : ℝ)
    (z : R × ProcessTape) : Outcome := ((A.policy z.1 (processHistory z.2 n)).isSome,clipEstimate M (A.output z))

def outcome {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (n : ℕ) (M : ℝ)
    (z : R × Table) : Outcome := observed A n M (z.1,populationPath (A.policy z.1) z.2)

def timedOut (v : Outcome) : ℝ≥0∞ := if v.1 then 1 else 0
def loss (θ x : ℝ) : ℝ≥0∞ := ENNReal.ofReal ((x-θ)^2)

theorem measurable_observed {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (n : ℕ) (M : ℝ) :
    Measurable (observed A n M) := by
  have h : Measurable (fun z : R × List Bool => A.policy z.1 z.2) := measurable_from_prod_countable_left
    (fun w => measurable_to_countable' (A.policy_measurable w))
  exact ((measurable_of_countable Option.isSome).comp (h.comp
    (measurable_fst.prodMk ((measurable_processHistory_fixed n).comp measurable_snd)))).prodMk
    ((measurable_clip M).comp A.output_measurable)

theorem measurable_outcome {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (n : ℕ) (M : ℝ) :
    Measurable (outcome A n M) :=
  (measurable_observed A n M).comp (measurable_fst.prodMk
    (measurable_seeded_populationPath A.policy (fun xs => measurable_to_countable' (A.policy_measurable xs))))

theorem measurable_timedOut : Measurable timedOut :=
  (measurable_of_countable (fun b : Bool => if b then (1:ℝ≥0∞) else 0)).comp measurable_fst

theorem measurable_loss (θ : ℝ) : Measurable (loss θ) := by unfold loss; fun_prop

theorem clip_loss_le (M θ x : ℝ) (hθ : 0 ≤ θ ∧ θ ≤ M) : loss θ (clipEstimate M x) ≤ loss θ x := by
  apply ENNReal.ofReal_le_ofReal
  by_cases hx : x < 0
  · rw [clipEstimate,min_eq_right (hx.le.trans (hθ.1.trans hθ.2)),max_eq_left hx.le]
    nlinarith [mul_nonneg (neg_nonneg.mpr hx.le) hθ.1,sq_nonneg x]
  · by_cases hx' : x ≤ M
    · rw [clipEstimate,min_eq_right hx',max_eq_right (le_of_not_gt hx)]
    · rw [clipEstimate,min_eq_left (le_of_not_ge hx'),max_eq_right (hθ.1.trans hθ.2)]
      nlinarith [mul_nonneg (sub_nonneg.mpr (le_of_not_ge hx')) (sub_nonneg.mpr hθ.2),sq_nonneg (x-M)]

theorem stage_loss_le {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (A : AdaptiveEstimator R) (M θ : ℝ) (hθ : 0 ≤ θ ∧ θ ≤ M) (n : ℕ) :
    (∫⁻ z, loss θ (outcome A n M z).2 ∂originalSimulationLaw μ A q) ≤
      squaredRisk (experimentLaw μ A q) (populationOutput A) θ := by
  have h := original_observable_lintegral μ A q (fun z => loss θ (observed A n M z).2)
    ((measurable_loss θ).comp (measurable_observed A n M).snd)
  change (∫⁻ z, loss θ (outcome A n M z).2 ∂originalSimulationLaw μ A q) ≤ _
  rw [← show _ = (∫⁻ z, loss θ (outcome A n M z).2 ∂originalSimulationLaw μ A q) from h]
  exact lintegral_mono (fun z => clip_loss_le _ _ _ hθ)

theorem timeout_work {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (A : AdaptiveEstimator R) (M : ℝ) (n : ℕ) :
    ((n:ℝ≥0∞)+1)*(∫⁻ z, timedOut (outcome A n M z) ∂originalSimulationLaw μ A q) ≤ expectedWork μ A q := by
  let F (z : R × ProcessTape) := timedOut (observed A n M z)
  have h := original_observable_lintegral μ A q F (measurable_timedOut.comp (measurable_observed A n M))
  change ((n:ℝ≥0∞)+1)*(∫⁻ z, F (z.1,populationPath (A.policy z.1) z.2) ∂originalSimulationLaw μ A q) ≤ _
  rw [← h,← lintegral_const_mul' _ _ (by finiteness)]
  apply lintegral_mono_ae
  filter_upwards [original_path_valid μ A q] with z hz
  cases hp : A.policy z.1.1 (processHistory z.2 n) with
  | none => simp [F,timedOut,observed,hp]
  | some i =>
    have hv := valid_path_continuation_work (A.policy z.1.1) z.2 hz n (by simp [hp])
    simpa [F,timedOut,observed,hp,ENNReal.ofReal_add (Nat.cast_nonneg n) zero_le_one] using hv

theorem timeout_quarter {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (A : AdaptiveEstimator R) (M : ℝ) (j : ℕ) (hw : expectedWork μ A q ≤ stageAllowance j) :
    (∫⁻ z, timedOut (outcome A (stageCap j) M z) ∂originalSimulationLaw μ A q) ≤ 1/4 := by
  let n := stageCap j
  have hbound : (n:ℝ≥0∞)*(∫⁻ z, timedOut (outcome A n M z) ∂originalSimulationLaw μ A q) ≤ expectedWork μ A q :=
    (mul_le_mul_left (le_self_add : (n:ℝ≥0∞) ≤ n+1) _).trans (timeout_work μ q A M n)
  have hn0 : n ≠ 0 := by dsimp [n,stageCap,stageAllowance]; positivity
  have eq : (stageAllowance j : ℝ≥0∞)/(n:ℝ≥0∞) = 1/4 := by
    have hb : (stageAllowance j:ℝ≥0∞) ≠ 0 := by dsimp [stageAllowance]; positivity
    change (stageAllowance j:ℝ≥0∞)/((4*stageAllowance j:ℕ):ℝ≥0∞) = _
    push_cast
    calc (stageAllowance j:ℝ≥0∞)/(4*stageAllowance j) =
          ((stageAllowance j:ℝ≥0∞)*1)/((stageAllowance j:ℝ≥0∞)*4) := by rw [mul_one,mul_comm 4]
         _ = _ := ENNReal.mul_div_mul_left _ _ hb (ENNReal.natCast_ne_top _)
  rw [← eq]
  apply (ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast hn0)) (Or.inl (ENNReal.natCast_ne_top n))).2
  simpa only [mul_comm] using hbound.trans hw

end ThresholdHC.HardBudget
