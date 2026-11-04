import ThresholdHC.Confidence.Model
import ThresholdHC.ConfidenceProgram.Single
import ThresholdHC.ConfidenceProgram.Majority

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace ThresholdHC.ConfidenceProgram
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.ObservableSimulation ThresholdHC.BlindUpper
open ThresholdHC.HardBudget ThresholdHC.Confidence

private theorem failure_simulation {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (q : SignLaw) (r : ℝ) :
    failureProbability μ A q r = (originalSimulationLaw μ A q)
      {z | r < |A.output (z.1,populationPath (A.policy z.1) z.2)-signMean μ q.val|} := by
  let E := {z : R × ProcessTape | r < |A.output z-signMean μ q.val|}
  have hE : MeasurableSet E := measurableSet_lt measurable_const ((A.output_measurable.sub_const _).abs)
  have h := congrArg (fun P : Measure (R × ProcessTape) => P E) (original_observable_simulation_law μ A q)
  have hm : Measurable (fun z : R × Table => (z.1,populationPath (A.policy z.1) z.2)) :=
    measurable_fst.prodMk (measurable_seeded_populationPath A.policy (fun w => measurable_to_countable' (A.policy_measurable w)))
  change (experimentLaw μ A q) ((fun z => (z.1.1,z.2)) ⁻¹' E) =
    (originalSimulationLaw μ A q) ((fun z => (z.1,populationPath (A.policy z.1) z.2)) ⁻¹' E)
  simpa only [Measure.map_apply (measurable_fst.fst.prodMk measurable_snd) hE,Measure.map_apply hm hE] using h

/-- Each of 2m+1 copies receives exactly N reservations. The statistical
step works for any original observable base estimator at this gap law and sign. -/
theorem capped_median_failure {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (q : SignLaw) (m N : ℕ) (M r : ℝ)
    (hθ : 0 ≤ signMean μ q.val ∧ signMean μ q.val ≤ M) (hr : 0 ≤ r)
    (hw : expectedWork μ A q ≤ ENNReal.ofReal (((N:ℝ)+1)/8))
    (hR : squaredRisk (experimentLaw μ A q) (populationOutput A) (signMean μ q.val) ≤ ENNReal.ofReal (r^2)) :
    failureProbability μ (cappedMedian A m N M) q (Real.sqrt 8*r) ≤ ENNReal.ofReal ((3/4:ℝ)^m/2) := by
  let θ := signMean μ q.val
  let P := originalSimulationLaw μ A q
  let _ : IsProbabilityMeasure P := by dsimp [P,originalSimulationLaw]; infer_instance
  let ν := Measure.infinitePi (fun _ : ℕ => P)
  let X (z : R × Table) := localValue M (outcome A N M z)
  have hX : Measurable X := (measurable_localValue M).comp (measurable_outcome A N M)
  let f (i : MedianIndex m) (u : ℕ → R × Table) := X (u i.val)
  have hm (i) : Measurable (f i) := hX.comp (measurable_pi_apply i.val)
  have hind : iIndepFun f ν := (iIndepFun_infinitePi (P := fun _ : ℕ => P) (fun _ => hX)).precomp Fin.val_injective
  have hsingle := single_capped_failure μ q A N M θ r hθ hr hw hR
  have hf (i : MedianIndex m) : ν {u | Real.sqrt 8*r < |f i u-θ|} ≤ 1/4 := by
    let E := {z : R × Table | Real.sqrt 8*r < |X z-θ|}
    have hE : MeasurableSet E := measurableSet_lt measurable_const ((hX.sub_const _).abs)
    change ν ((fun u => u i.val) ⁻¹' E) ≤ _
    rw [← Measure.map_apply (measurable_pi_apply i.val) hE,Measure.infinitePi_map_eval]
    exact hsingle
  have hout := quarter_majority ν m f hm hind θ (Real.sqrt 8*r) hf
  have hp : MeasurePreserving stageInputs (originalSimulationLaw μ (cappedMedian A m N M) q) ν :=
    stageInputs_preserving (fun _ => A) M 0 μ q
  let E := {u | Real.sqrt 8*r < |median m (fun i => f i u)-θ|}
  have hE : MeasurableSet E := measurableSet_lt measurable_const (((measurable_median m f hm).sub_const _).abs)
  change ν E ≤ _ at hout
  rw [← hp.map_eq,Measure.map_apply hp.measurable hE] at hout
  rw [failure_simulation]
  apply le_trans _ hout
  apply measure_mono; intro z hz
  change Real.sqrt 8*r < |median m (fun i => f i (stageInputs z))-θ|
  change Real.sqrt 8*r < |(cappedMedian A m N M).output
    (z.1,populationPath ((cappedMedian A m N M).policy z.1) z.2)-θ| at hz
  rw [cappedMedian_output] at hz
  exact hz

theorem median_budget_cap {R : Type} [MeasurableSpace R] (A : AdaptiveEstimator R) (m : ℕ)
    {B : ℝ} (hB : 0 < B) (M : ℝ) :
    PathwiseCap (cappedMedian A m ⌊B/(2*(m:ℝ)+1)⌋₊ M) ⌊B⌋₊ := by
  let c := 2*(m:ℝ)+1
  have hc : 0 < c := by dsimp [c]; positivity
  let n := ⌊B/c⌋₊
  have hn : (n:ℝ) ≤ B/c := Nat.floor_le (div_nonneg hB.le hc.le)
  intro z x hx
  apply (cappedMedian_cap A m n M z x hx).trans
  apply Nat.cast_le.mpr
  apply Nat.le_floor
  push_cast
  calc _ = (n:ℝ)*c := by dsimp [c]; ring
       _ ≤ _ := (le_div_iff₀ hc).mp hn

/-- The median only uses the observations it reserves, including with a cap
of zero. Rounding the per-copy cap does not weaken the Markov bound. -/
theorem hard_median_transfer {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (q : SignLaw) (m : ℕ) {B M r : ℝ} (hB : 0 < B)
    (hθ : 0 ≤ signMean μ q.val ∧ signMean μ q.val ≤ M) (hr : 0 ≤ r)
    (hw : expectedWork μ A q ≤ ENNReal.ofReal (B/(8*(2*(m:ℝ)+1))))
    (hR : rootMeanRisk (experimentLaw μ A q) (populationOutput A) (signMean μ q.val) ≤ ENNReal.ofReal r) :
    let n := ⌊B/(2*(m:ℝ)+1)⌋₊
    PathwiseCap (cappedMedian A m n M) ⌊B⌋₊ ∧
      failureProbability μ (cappedMedian A m n M) q (Real.sqrt 8*r) ≤ ENNReal.ofReal ((3/4:ℝ)^m/2) := by
  let c := 2*(m:ℝ)+1
  let n := ⌊B/c⌋₊
  have hn' : B/c < (n:ℝ)+1 := Nat.lt_floor_add_one _
  constructor
  · exact median_budget_cap A m hB M
  · apply capped_median_failure μ A q m n M r hθ hr _ (square_from_rms _ _ _ _ hr hR)
    apply hw.trans; apply ENNReal.ofReal_le_ofReal
    change B/(8*c) ≤ ((n:ℝ)+1)/8
    rw [show B/(8*c) = (B/c)/8 by ring]
    exact div_le_div_of_nonneg_right hn'.le (by norm_num)

/-- In particular the paper's least odd repetition count satisfying this
inequality gives the requested failure level. -/
theorem capped_median_at_level {R : Type} [MeasurableSpace R] (μ : Measure Gap) [IsProbabilityMeasure μ]
    (A : AdaptiveEstimator R) (q : SignLaw) (m : ℕ) {B M r δ : ℝ} (hb : 0 < B) (hd : 0 ≤ δ)
    (hm : (3/4:ℝ)^(2*m+1) ≤ δ^2) (hθ : 0 ≤ signMean μ q.val ∧ signMean μ q.val ≤ M) (hr : 0 ≤ r)
    (hw : expectedWork μ A q ≤ ENNReal.ofReal (B/(8*(2*(m:ℝ)+1))))
    (hR : rootMeanRisk (experimentLaw μ A q) (populationOutput A) (signMean μ q.val) ≤ ENNReal.ofReal r) :
    let n := ⌊B/(2*(m:ℝ)+1)⌋₊
    PathwiseCap (cappedMedian A m n M) ⌊B⌋₊ ∧
      failureProbability μ (cappedMedian A m n M) q (Real.sqrt 8*r) ≤ ENNReal.ofReal δ := by
  obtain ⟨hcap,hfail⟩ := hard_median_transfer μ A q m hb hθ hr hw hR
  refine ⟨hcap,hfail.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  have he : (3/4:ℝ)^(2*m+1) = ((3/4:ℝ)^m)^2*(3/4) := by rw [pow_succ,Nat.mul_comm 2 m,pow_mul]
  rw [he] at hm
  nlinarith only [hm,hd,sq_nonneg ((3/4:ℝ)^m),pow_nonneg (by norm_num : (0:ℝ) ≤ 3/4) m]

end ThresholdHC.ConfidenceProgram
