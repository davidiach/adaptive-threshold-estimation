
import ThresholdHC.FiniteCapTruncation.Risk
noncomputable section
set_option linter.unusedVariables false
open MeasureTheory
open scoped ENNReal
open ThresholdHC.Tier6 ThresholdHC.StoppingProgram ThresholdHC.Genie ThresholdHC.RareAboveTwo
open ThresholdHC.FiniteCapTruncation

example : ∀ {M N : ℕ} (hN : 0 < N) (hNM : N ≤ M) (f : Flow M)
    (hf : FlowCone f), FlowCone (capFlow N f) := @capFlow_cone

example : ∀ {M : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (N : ℕ) (f : Flow M) (hf : FlowCone f),
    ((N:ℝ)+1) * discardedMean μ q N f.stopWeight ≤
      countMean μ q f.continueWeight := @discarded_mass_work

example : ∀ {M : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (N : ℕ) (f : Flow M) (hf : FlowCone f)
    {B V : ℝ} (hB : 0 ≤ B) (hV : 0 ≤ V)
    (hw : countMean μ q f.continueWeight ≤ B)
    (hv : countMean μ q f.momentWeight ≤ V),
    |discardedMean μ q N f.outputWeight| ≤ Real.sqrt (B*V/((N:ℝ)+1)) :=
  @discarded_output_bound

example : ∀ {M N : ℕ} (hN : 0 < N) (hNM : N ≤ M)
    (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ B : ℝ} (hB : 0 ≤ B)
    (C : Certificate M) (hC : Feasible μ ρ B C),
    Feasible μ ρ B (capCertificate N B C) := @capCertificate_feasible

example : ∀ {M : ℕ} (N : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (C : Certificate M) (hV : 0 ≤ C.variance),
    certificateSquared (capCertificate N B C) ≤
      ENNReal.ofReal ((1+Real.sqrt (B/((N:ℝ)+1)))^2) * certificateSquared C :=
  @capCertificate_squared

example : ∀ {M N : ℕ} (hN : 0 < N) (hNM : N ≤ M)
    (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ : ℝ) {B : ℝ} (hB : 0 ≤ B),
    programSquared μ ρ B N ≤
      ENNReal.ofReal ((1+Real.sqrt (B/((N:ℝ)+1)))^2) * programSquared μ ρ B M :=
  @programSquared_cap_le

example : ∀ {M N : ℕ} (hN : 0 < N) (hNM : N ≤ M)
    (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ : ℝ) {B : ℝ} (hB : 0 ≤ B),
    programValue μ ρ B N ≤
      ENNReal.ofReal (1+Real.sqrt (B/((N:ℝ)+1))) * programValue μ ρ B M :=
  @programValue_cap_le

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (ρ : ℝ)
    {B : ℝ} (hB : 0 ≤ B) (N : ℕ) (hN : 0 < N),
    infiniteProgramValue μ ρ B ≤ programValue μ ρ B N ∧
      programValue μ ρ B N ≤
        ENNReal.ofReal (1+Real.sqrt (B/((N:ℝ)+1))) * infiniteProgramValue μ ρ B :=
  @ordinary_cap_rate

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B : ℝ} (hρ : 0 < ρ) (hρhalf : ρ ≤ 1/2) (hB : 0 < B)
    (N : ℕ) (hN : 0 < N),
    rareMinimaxRisk μ ρ B ≤ programValue μ ρ B N ∧
      programValue μ ρ B N ≤ ENNReal.ofReal (8*(1+Real.sqrt (B/((N:ℝ)+1)))) *
        rareMinimaxRisk μ ρ B := @ordinary_cap_minimax

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B : ℝ} (hρ : 0 < ρ) (hρhalf : ρ ≤ 1/2) (hB : 0 < B)
    (N : ℕ) (hN : 0 < N) (hcap : B ≤ (N:ℝ)+1),
    programValue μ ρ B N ≤ 16 * rareMinimaxRisk μ ρ B := @ordinary_linear_cap
#print axioms ThresholdHC.FiniteCapTruncation.capCertificate_feasible
#print axioms ThresholdHC.FiniteCapTruncation.capCertificate_squared
#print axioms ThresholdHC.FiniteCapTruncation.capFlow_cone
#print axioms ThresholdHC.FiniteCapTruncation.discarded_mass_work
#print axioms ThresholdHC.FiniteCapTruncation.discarded_output_bound
#print axioms ThresholdHC.FiniteCapTruncation.ordinary_cap_minimax
#print axioms ThresholdHC.FiniteCapTruncation.ordinary_cap_rate
#print axioms ThresholdHC.FiniteCapTruncation.ordinary_linear_cap
#print axioms ThresholdHC.FiniteCapTruncation.programSquared_cap_le
#print axioms ThresholdHC.FiniteCapTruncation.programValue_cap_le
