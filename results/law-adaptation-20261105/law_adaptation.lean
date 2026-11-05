
import ThresholdHC.LawAdaptation.Parity
import ThresholdHC.LawAdaptation.Pilot
import ThresholdHC.LawAdaptation.Transfer
import ThresholdHC.LawAdaptation.Rate
noncomputable section
set_option linter.unusedVariables false
open MeasureTheory ProbabilityTheory Real
open scoped BigOperators ENNReal NNReal Classical
open ThresholdHC.LawAdaptation
open ThresholdHC.Tier6 ThresholdHC.EntropyTail ThresholdHC.Anytime

example : ∀ (p : ℝ) (n : ℕ),
    ∑ w : Fin n → Bool, wordMass p w * parity w = (2*p-1)^n := @parity_mean

example : ∀ (d : ℝ) (positive : Bool) (k : ℕ),
    ∑ w : Fin (2*k) → Bool,
      wordMass (if positive then 1/2+d else 1/2-d) w * parity w = (2*d)^(2*k) :=
  @even_parity_mean

example : ∀ (d q : ℝ) (k : ℕ),
    q * (∑ w : Fin (2*k) → Bool, wordMass (1/2+d) w * parity w) +
      (1-q) * (∑ w : Fin (2*k) → Bool, wordMass (1/2-d) w * parity w) =
      (2*d)^(2*k) := @mixed_even_parity

example : ∀ {n : ℕ} (w : Fin n → Bool), |parity w| = 1 := @parity_abs

example : ∀ {ι κ : Type*} (signature : ι → κ → ℝ)
    (observed : κ → ℝ) {ε η : ℝ} (hsep : 2*ε < η)
    (hdist : ∀ i j, i ≠ j → ∃ k, η ≤ |signature i k - signature j k|)
    {i j : ι} (hi : Compatible signature observed ε i)
    (hj : Compatible signature observed ε j), i = j := @compatible_unique

example : ∀ {ι κ : Type*} [Nonempty ι] (signature : ι → κ → ℝ)
    (observed : κ → ℝ) {ε η : ℝ} (hsep : 2*ε < η)
    (hdist : ∀ i j, i ≠ j → ∃ k, η ≤ |signature i k - signature j k|)
    (truth : ι) (hgood : Compatible signature observed ε truth),
    identify signature observed ε = truth := @identify_correct

example : ∀ {Ω ι κ : Type*} [MeasurableSpace Ω]
    [Nonempty ι] [Fintype κ] (P : Measure Ω) (signature : ι → κ → ℝ)
    (observed : Ω → κ → ℝ) (truth : ι) {ε η : ℝ} (hsep : 2*ε < η)
    (hdist : ∀ i j, i ≠ j → ∃ k, η ≤ |signature i k - signature j k|)
    (failure : κ → ℝ≥0∞)
    (hcoord : ∀ k, P {ω | ε < |observed ω k-signature truth k|} ≤ failure k),
    P {ω | identify signature (observed ω) ε ≠ truth} ≤ ∑ k, failure k :=
  @identify_error_bound

example : ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hm : AEMeasurable X P)
    (hb : ∀ᵐ ω ∂P, X ω ∈ Set.Icc (-1:ℝ) 1),
    HasSubgaussianMGF (fun ω => X ω - ∫ x, X x ∂P) 1 P := @centered_subgaussian

example : ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) (X : Fin n → Ω → ℝ)
    (hm : ∀ i, AEMeasurable (X i) P)
    (hb : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Set.Icc (-1:ℝ) 1)
    (hi : iIndepFun X P) {a ε : ℝ} (hmean : ∀ i, ∫ ω, X i ω ∂P = a)
    (hε : 0 ≤ ε),
    P.real {ω | ε < |(∑ i, X i ω)/(n:ℝ)-a|} ≤ 2*exp (-(n:ℝ)*ε^2/2) :=
  @bounded_average_tail

example : ∀ {Ω ι : Type*} [MeasurableSpace Ω] [Nonempty ι]
    (P : Measure Ω) [IsProbabilityMeasure P] {m n : ℕ} (hn : 0 < n)
    (signature : ι → Fin m → ℝ) (truth : ι) (X : Fin m → Fin n → Ω → ℝ)
    {η : ℝ} (hη : 0 < η)
    (hdist : ∀ i j, i ≠ j → ∃ k, η ≤ |signature i k-signature j k|)
    (hm : ∀ k t, AEMeasurable (X k t) P)
    (hb : ∀ k t, ∀ᵐ ω ∂P, X k t ω ∈ Set.Icc (-1:ℝ) 1)
    (hi : ∀ k, iIndepFun (X k) P)
    (hmean : ∀ k t, ∫ ω, X k t ω ∂P = signature truth k),
    P {ω | identify signature (fun k => (∑ t, X k t ω)/(n:ℝ)) (η/4) ≠ truth} ≤
      ENNReal.ofReal (2*(m:ℝ)*exp (-(n:ℝ)*η^2/32)) := @pilot_error

example : ∀ {m n : ℕ} (hm : 0 < m) {η δ : ℝ} (hd : 0 < δ)
    (hsize : log (2*(m:ℝ)/δ) ≤ (n:ℝ)*η^2/32),
    2*(m:ℝ)*exp (-(n:ℝ)*η^2/32) ≤ δ := @pilot_calibration

example : ∀ {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (chosen : Ω → ι) (truth : ι) (good : ι → Ω → Prop)
    {δpilot δoracle : ℝ≥0∞}
    (hp : P {ω | chosen ω ≠ truth} ≤ δpilot)
    (ho : P {ω | ¬ good truth ω} ≤ δoracle),
    P {ω | ¬ good (chosen ω) ω} ≤ δpilot + δoracle := @selected_failure_bound

example : ∀ {Ω ι T : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (chosen : Ω → ι) (truth : ι) (property : ι → T → Ω → Prop)
    {δpilot δoracle : ℝ≥0∞}
    (hp : P {ω | chosen ω ≠ truth} ≤ δpilot)
    (ho : P {ω | ¬ ∀ t, property truth t ω} ≤ δoracle),
    P {ω | ¬ ∀ t, property (chosen ω) t ω} ≤ δpilot + δoracle :=
  @selected_simultaneous

example : ∀ (H B flips : ℕ) (h : flips ≤ B-H), min H B + flips ≤ B := @paid_pilot_cap

example : ∀ {b B δ : ℝ} (hb : 0 ≤ b) (hle : b ≤ B),
    inflation b δ ≤ inflation B δ := @inflation_mono_budget

example : ∀ {B δ : ℝ} (hB : 0 ≤ B) (hd : 0 < δ) (hd' : δ ≤ 1/4),
    inflation B (δ/2) ≤ 2*inflation B δ := @inflation_half_failure

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ : ℝ)
    {H B δ : ℝ} (hH : 0 ≤ H) (hB : 0 < B) (hHB : 2*H ≤ B)
    (hd : 0 < δ) (hd' : δ ≤ 1/4),
    selection μ ρ ((B-H)/inflation (B-H) (δ/2)) ≤
      2 * selection μ ρ (B/inflation B δ) := @delayed_selection
#print axioms ThresholdHC.LawAdaptation.bounded_average_tail
#print axioms ThresholdHC.LawAdaptation.centered_subgaussian
#print axioms ThresholdHC.LawAdaptation.compatible_unique
#print axioms ThresholdHC.LawAdaptation.delayed_selection
#print axioms ThresholdHC.LawAdaptation.even_parity_mean
#print axioms ThresholdHC.LawAdaptation.identify_correct
#print axioms ThresholdHC.LawAdaptation.identify_error_bound
#print axioms ThresholdHC.LawAdaptation.inflation_half_failure
#print axioms ThresholdHC.LawAdaptation.inflation_mono_budget
#print axioms ThresholdHC.LawAdaptation.mixed_even_parity
#print axioms ThresholdHC.LawAdaptation.paid_pilot_cap
#print axioms ThresholdHC.LawAdaptation.parity_abs
#print axioms ThresholdHC.LawAdaptation.parity_mean
#print axioms ThresholdHC.LawAdaptation.pilot_calibration
#print axioms ThresholdHC.LawAdaptation.pilot_error
#print axioms ThresholdHC.LawAdaptation.selected_failure_bound
#print axioms ThresholdHC.LawAdaptation.selected_simultaneous
