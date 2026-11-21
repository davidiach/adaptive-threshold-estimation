import ThresholdHC.CreationCharge.Count

/-! The fee factor `1 + c` and the charged minimax sandwich.

Since created coins are almost surely at most the work, the charged cost
`W + c*C` lies between `W` and `(1 + c)*W` pointwise almost surely, hence in
expectation. Integration uses only monotonicity and `lintegral_const_mul'`, so
no measurability of `totalCreated` is needed. -/
noncomputable section
namespace ThresholdHC.CreationCharge
open MeasureTheory Filter ThresholdHC.Tier3 ThresholdHC.Tier6
open scoped ENNReal

/-- The charged expected cost is at least the expected work. -/
theorem expectedWork_le_charged {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (q : SignLaw)
    (c : ℝ) : expectedWork μ A q ≤ chargedExpectedWork μ A q c := by
  unfold expectedWork chargedExpectedWork
  exact lintegral_mono fun z => le_self_add

/-- `W + c*C ≤ (1 + c)*W` when `C ≤ W` and `c ≥ 0`. -/
theorem charged_pointwise_le {W C : ℝ≥0∞} {c : ℝ} (hc : 0 ≤ c) (h : C ≤ W) :
    W + ENNReal.ofReal c * C ≤ ENNReal.ofReal (1 + c) * W := by
  rw [ENNReal.ofReal_add zero_le_one hc, ENNReal.ofReal_one, add_mul, one_mul]
  gcongr

/-- The charged expected cost is at most `1 + c` times the expected work. -/
theorem charged_le_expectedWork {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) (q : SignLaw)
    {c : ℝ} (hc : 0 ≤ c) :
    chargedExpectedWork μ A q c ≤ ENNReal.ofReal (1 + c) * expectedWork μ A q := by
  unfold expectedWork chargedExpectedWork
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [createdObserved_holds R μ A q] with z hz
  exact charged_pointwise_le hc hz.2

theorem chargedWork_holds : ChargedWorkStatement := by
  intro R _ μ _ A q c hc
  exact ⟨expectedWork_le_charged μ A q c, charged_le_expectedWork μ A q hc⟩

/-- A charged budget is an ordinary budget. -/
theorem uniformBudget_of_charged {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) {c B : ℝ}
    (h : ChargedUniformBudget μ A c B) : UniformBudget μ A B :=
  fun q => (expectedWork_le_charged μ A q c).trans (h q)

/-- An ordinary budget `B` gives the charged budget `(1 + c)*B`. -/
theorem chargedBudget_of_budget {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) {c B : ℝ}
    (hc : 0 ≤ c) (h : UniformBudget μ A B) : ChargedUniformBudget μ A c ((1 + c) * B) := by
  intro q
  refine (charged_le_expectedWork μ A q hc).trans ?_
  rw [ENNReal.ofReal_mul (by linarith)]
  gcongr
  exact h q

/-- An ordinary budget `B/(1 + c)` gives the charged budget `B`. -/
theorem chargedBudget_of_budget_div {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R) {c B : ℝ}
    (hc : 0 ≤ c) (h : UniformBudget μ A (B / (1 + c))) : ChargedUniformBudget μ A c B := by
  have h1 : (1 + c) * (B / (1 + c)) = B := by
    have : (1 + c) ≠ 0 := by linarith
    field_simp
  have h2 := chargedBudget_of_budget μ A hc h
  rwa [h1] at h2

theorem chargedMinimax_holds : ChargedMinimaxStatement := by
  intro μ _ c B hc
  constructor
  · apply sInf_le_sInf
    rintro _ ⟨R, mR, A, hb, rfl⟩
    exact ⟨R, mR, A, uniformBudget_of_charged μ A hb, rfl⟩
  · apply sInf_le_sInf
    rintro _ ⟨R, mR, A, hb, rfl⟩
    exact ⟨R, mR, A, chargedBudget_of_budget_div μ A hc hb, rfl⟩

end ThresholdHC.CreationCharge
