
import ThresholdHC.AnytimeLower.Intervals
import ThresholdHC.AnytimeLower.FiniteFamily
import ThresholdHC.AnytimeLower.FiniteCoefficient
import ThresholdHC.AnytimeLower.Spacing
noncomputable section
set_option linter.unusedVariables false
open MeasureTheory InformationTheory Real Set Filter
open scoped ENNReal Topology
open ThresholdHC.AnytimeLower ThresholdHC.Tier3 ThresholdHC.Tier6
open ThresholdHC.StoppingProgram ThresholdHC.Genie

example : ∀ {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    (H : ∀ n, R × Prefix n → ℝ) (hH : ∀ n, Measurable (H n))
    {ρ δ : ℝ} (hd : 0 ≤ δ ∧ δ ≤ 1/2) (t : ℕ → ℝ)
    (hacc : OnlineAccuracy μ A H ρ δ t)
    (Q : FourPriors) (hQ : Admissible μ ρ Q)
    {J : ℝ} (hJ : 0 < J) (hI : infiniteInformationRatio μ Q ≤ ENNReal.ofReal J)
    (hgap : 0 < signMean μ Q.high.val-signMean μ Q.low.val),
    ∃ᶠ k in atTop, centralShift k*(signMean μ Q.high.val-signMean μ Q.low.val)/18 ≤
      t (testingBudget δ (certificateScale J) k) := @certificate_scheduled_frequently

example : ∀ (x : ℕ → ℝ) (hx : ∀ k, 0 ≤ x k)
    (hlarge : ∃ᶠ k : ℕ in atTop, (k:ℝ)^2 < x k),
    ∃ᶠ k in atTop, sqrt (x k) ≤ x (k+1)-x k := @frequently_long_blocks

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ τ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hm : μ.real {d : Gap | (d:ℝ) ≤ τ} < ρ) (B : ℝ),
    ENNReal.ofReal (profileMass μ τ (ThresholdHC.EntropyTailQuantile.budgetScale B)) ≤
      ThresholdHC.EntropyTail.selection μ ρ B := @profile_le_selection

example : ∀ (μ : Measure Gap) [IsFiniteMeasure μ]
    (hI : ¬Integrable (fun d : Gap => (d:ℝ)⁻¹) μ) {τ : ℝ} (hτ : 0 < τ) (C : ℝ),
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h ≤ h₀ → C*h ≤ profileMass μ τ h :=
      @profileMass_dominates_linear

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hb : BddAbove (selectionCoefficients μ ρ)),
    ∃ B : ℝ, 0 < B ∧ selectionCoefficient μ ρ/2 < normalizedSelection μ ρ B :=
      @exists_coefficient_witness

example : ∀ {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ]
    (hI : ¬Integrable (fun d : Gap => (d:ℝ)⁻¹) μ)
    (A : AdaptiveEstimator R) (H : ∀ n, R × Prefix n → ℝ)
    (hH : ∀ n, Measurable (H n))
    {τ ρ δ : ℝ} (hτ : 0 < τ) (hτq : τ ≤ 1/4)
    (hμ : 0 < μ {d : Gap | (d:ℝ) ≤ τ})
    (hrare : μ.real {d : Gap | (d:ℝ) ≤ τ} ≤ ρ)
    (hd : 0 ≤ δ ∧ δ ≤ 1/2) (t : ℕ → ℝ) (hacc : OnlineAccuracy μ A H ρ δ t)
    (hdense : ∀ᶠ k in atTop, (tailDropIndex μ hτ hμ k:ℝ) ≤ ((k:ℝ)+2)^2) (M : ℕ),
    ∃ n : ℕ, M ≤ n ∧ ENNReal.ofReal (1/2560) *
      ThresholdHC.EntropyTail.selection μ ρ ((n:ℝ)/budgetInflation δ n) ≤ ENNReal.ofReal (t n) :=
      @dense_tail_matching

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4)
    (hb : BddAbove (selectionCoefficients μ ρ)),
    ∃ (Q : FourPriors) (J : ℝ), Admissible μ ρ Q ∧ 0 < J ∧
      infiniteInformationRatio μ Q ≤ ENNReal.ofReal J ∧
      0 < signMean μ Q.high.val-signMean μ Q.low.val ∧
      (((10:ℝ)⁻¹^17)*selectionCoefficient μ ρ/2)^2*J ≤
        (signMean μ Q.high.val-signMean μ Q.low.val)^2 := @coefficient_certificate

example : ∀ {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ δ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hb : BddAbove (selectionCoefficients μ ρ))
    (A : AdaptiveEstimator R) (H : ∀ n, R × Prefix n → ℝ) (hH : ∀ n, Measurable (H n))
    (hd : 0 ≤ δ ∧ δ ≤ 1/2) (t : ℕ → ℝ) (hacc : OnlineAccuracy μ A H ρ δ t) (M : ℕ),
    ∃ n : ℕ, M ≤ n ∧ ENNReal.ofReal ((10:ℝ)⁻¹^22) *
      ThresholdHC.EntropyTail.selection μ ρ ((n:ℝ)/budgetInflation δ n) ≤ ENNReal.ofReal (t n) :=
      @finite_coefficient_matching

example : ∀ {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    (H : ∀ n, R × Prefix n → ℝ) (hH : ∀ n, Measurable (H n))
    {τ ρ δ ε : ℝ} (hτq : τ ≤ 1/4) (hε : 0 ≤ ε)
    (hrare : μ.real {d : Gap | (d:ℝ) ≤ τ} ≤ ρ)
    (hd : δ ≤ 1/4) (t : ℕ → ℝ) (hacc : OnlineAccuracy μ A H ρ δ t)
    (n : ℕ) (hn : (n:ℝ)*ε^2 < 1/2),
    profileMass μ τ ε/64 ≤ t n := @tail_fixed_radius

example : ∀ {δ τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1),
    ∀ᶠ j : ℕ in atTop, 0 < sparseBudget τ j ∧
      0 < budgetInflation δ (sparseBudget τ j) ∧
      inflatedScale δ (sparseBudget τ j) ≤ geometricScale τ j := @sparse_inflatedScale_bound

example : ∀ {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ]
    (hI : ¬Integrable (fun d : Gap => (d:ℝ)⁻¹) μ)
    (A : AdaptiveEstimator R) (H : ∀ n, R × Prefix n → ℝ) (hH : ∀ n, Measurable (H n))
    {τ ρ δ : ℝ} (hτ : 0 < τ) (hτq : τ ≤ 1/4)
    (hμ : 0 < μ {d : Gap | (d:ℝ) ≤ τ})
    (hrare : μ.real {d : Gap | (d:ℝ) ≤ τ} ≤ ρ)
    (hd : δ ≤ 1/4) (t : ℕ → ℝ) (hacc : OnlineAccuracy μ A H ρ δ t)
    (hsparse : ∃ᶠ k in atTop, sqrt (tailDropIndex μ hτ hμ k:ℝ) ≤
      (tailDropIndex μ hτ hμ (k+1):ℝ)-tailDropIndex μ hτ hμ k) (M : ℕ),
    ∃ n : ℕ, M ≤ n ∧ ENNReal.ofReal (1/512) *
      ThresholdHC.EntropyTail.selection μ ρ ((n:ℝ)/budgetInflation δ n) ≤ ENNReal.ofReal (t n) :=
      @sparse_tail_matching

example : ∀ {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ δ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hd : 0 < δ ∧ δ ≤ 1/4)
    (A : AdaptiveEstimator R) (H : ∀ n, R × Prefix n → ℝ) (hH : ∀ n, Measurable (H n))
    (t : ℕ → ℝ) (hacc : OnlineAccuracy μ A H ρ δ t) (M : ℕ),
    ∃ n : ℕ, M ≤ n ∧ ENNReal.ofReal ((10:ℝ)⁻¹^22) *
      ThresholdHC.EntropyTail.selection μ ρ ((n:ℝ)/budgetInflation δ n) ≤ ENNReal.ofReal (t n) :=
      @law_dependent_online_lower

example : ∀ {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    (L U : ∀ n, R × Prefix n → ℝ) {ρ δ : ℝ} (t : ℕ → ℝ)
    (hc : OnlineIntervalCoverage μ A L U ρ δ t),
    OnlineAccuracy μ A (fun n x => (L n x+U n x)/2) ρ δ t := @interval_midpoint_accuracy

example : ∀ {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ δ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hd : 0 < δ ∧ δ ≤ 1/4)
    (A : AdaptiveEstimator R) (L U : ∀ n, R × Prefix n → ℝ)
    (hL : ∀ n, Measurable (L n)) (hU : ∀ n, Measurable (U n))
    (t : ℕ → ℝ) (ht : ∀ n, 0 ≤ t n) (hc : OnlineIntervalCoverage μ A L U ρ δ t)
    (M : ℕ), ∃ n : ℕ, max M 3 ≤ n ∧
      ((10:ℝ)⁻¹^22)*(ThresholdHC.EntropyTail.selection μ ρ
        ((n:ℝ)/budgetInflation δ n)).toReal ≤ t n := @law_dependent_interval_lower
#print axioms ThresholdHC.AnytimeLower.certificate_scheduled_frequently
#print axioms ThresholdHC.AnytimeLower.coefficient_certificate
#print axioms ThresholdHC.AnytimeLower.dense_tail_matching
#print axioms ThresholdHC.AnytimeLower.exists_coefficient_witness
#print axioms ThresholdHC.AnytimeLower.finite_coefficient_matching
#print axioms ThresholdHC.AnytimeLower.frequently_long_blocks
#print axioms ThresholdHC.AnytimeLower.interval_midpoint_accuracy
#print axioms ThresholdHC.AnytimeLower.law_dependent_interval_lower
#print axioms ThresholdHC.AnytimeLower.law_dependent_online_lower
#print axioms ThresholdHC.AnytimeLower.profileMass_dominates_linear
#print axioms ThresholdHC.AnytimeLower.profile_le_selection
#print axioms ThresholdHC.AnytimeLower.sparse_inflatedScale_bound
#print axioms ThresholdHC.AnytimeLower.sparse_tail_matching
#print axioms ThresholdHC.AnytimeLower.tail_fixed_radius
