
import ThresholdHC.ArbitraryLawAdaptation.IncreasingSelection
noncomputable section
set_option linter.unusedVariables false
open MeasureTheory
open scoped ENNReal
open ThresholdHC.ArbitraryLawAdaptation ThresholdHC.EntropyTail
open ThresholdHC.Tier6 (Gap)

example : ∀ (π : Measure (Gap × Gap)) (σ : Measure Gap), selectionLift π σ =
    π.withDensity (fun z => σ.rnDeriv (π.map Prod.fst) z.1) := fun _ _ => rfl
example : ∀ (π : Measure (Gap × Gap)) (σ : Measure Gap), transportedSelection π σ =
    (selectionLift π σ).map Prod.snd := fun _ _ => rfl
example {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] :
    ∀ (π : Measure Ω) {g : Ω → E} (hg : Measurable g) {w : E → ℝ≥0∞} (hw : Measurable w),
    (π.withDensity (fun z => w (g z))).map g = (π.map g).withDensity w :=
  @map_withDensity_comp Ω E _ _
example : ∀ (π : Measure (Gap × Gap)) [IsFiniteMeasure π] {σ : Measure Gap}
    (hσ : σ ≤ π.map Prod.fst), (selectionLift π σ).map Prod.fst = σ := @selectionLift_first
example : ∀ (π : Measure (Gap × Gap)) [IsFiniteMeasure π] {σ : Measure Gap}
    (hσ : σ ≤ π.map Prod.fst), selectionLift π σ ≤ π := @selectionLift_le
example : ∀ (π : Measure (Gap × Gap)) [IsFiniteMeasure π] {σ : Measure Gap}
    (hσ : σ ≤ π.map Prod.fst), transportedSelection π σ ≤ π.map Prod.snd :=
  @transportedSelection_le
example : ∀ (π : Measure (Gap × Gap)) [IsFiniteMeasure π] {σ : Measure Gap}
    (hσ : σ ≤ π.map Prod.fst), transportedSelection π σ Set.univ = σ Set.univ :=
  @transportedSelection_mass
example {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] :
    ∀ {π ξ : Measure Ω} [IsFiniteMeasure ξ] (hξ : ξ ≤ π) {g : Ω → E} (hg : Measurable g),
    (π-ξ).map g = π.map g-ξ.map g := @map_sub_of_le Ω E _ _
example : ∀ (π : Measure (Gap × Gap)) (hup : ∀ᵐ z ∂π, (z.1 : ℝ) ≤ (z.2 : ℝ))
    {h : ℝ} (hh : 0 ≤ h), tailCost (π.map Prod.snd) h ≤ tailCost (π.map Prod.fst) h :=
  @tailCost_increasing_coupling
example : ∀ (π : Measure (Gap × Gap)) [IsFiniteMeasure π]
    (hup : ∀ᵐ z ∂π, (z.1 : ℝ) ≤ (z.2 : ℝ)) {σ : Measure Gap}
    (hσ : σ ≤ π.map Prod.fst) {h : ℝ} (hh : 0 ≤ h),
    gamma (transportedSelection π σ) ≤ 3*gamma σ ∧
      tailCost (π.map Prod.snd-transportedSelection π σ) h ≤ tailCost (π.map Prod.fst-σ) h :=
  @transportedSelection_costs
example : (1 : ℝ) ≤ Real.sqrt 3 := one_le_sqrt_three
example : ∀ (π : Measure (Gap × Gap)) [IsFiniteMeasure π]
    (hup : ∀ᵐ z ∂π, (z.1 : ℝ) ≤ (z.2 : ℝ)) {σ : Measure Gap}
    (hσ : σ ≤ π.map Prod.fst) (ρ B : ℝ),
    selectionObjective (π.map Prod.snd) ρ B (transportedSelection π σ) ≤
      ENNReal.ofReal (Real.sqrt 3)*selectionObjective (π.map Prod.fst) ρ B σ :=
  @transportedSelection_objective
example : ∀ (π : Measure (Gap × Gap)) [IsFiniteMeasure π]
    (hup : ∀ᵐ z ∂π, (z.1 : ℝ) ≤ (z.2 : ℝ)) (ρ B : ℝ),
    selection (π.map Prod.snd) ρ B ≤
      ENNReal.ofReal (Real.sqrt 3)*selection (π.map Prod.fst) ρ B :=
  @selection_le_sqrt_three_of_increasing_coupling
#print axioms ThresholdHC.ArbitraryLawAdaptation.map_sub_of_le
#print axioms ThresholdHC.ArbitraryLawAdaptation.map_withDensity_comp
#print axioms ThresholdHC.ArbitraryLawAdaptation.one_le_sqrt_three
#print axioms ThresholdHC.ArbitraryLawAdaptation.selectionLift
#print axioms ThresholdHC.ArbitraryLawAdaptation.selectionLift_first
#print axioms ThresholdHC.ArbitraryLawAdaptation.selectionLift_le
#print axioms ThresholdHC.ArbitraryLawAdaptation.selection_le_sqrt_three_of_increasing_coupling
#print axioms ThresholdHC.ArbitraryLawAdaptation.tailCost_increasing_coupling
#print axioms ThresholdHC.ArbitraryLawAdaptation.transportedSelection
#print axioms ThresholdHC.ArbitraryLawAdaptation.transportedSelection_costs
#print axioms ThresholdHC.ArbitraryLawAdaptation.transportedSelection_le
#print axioms ThresholdHC.ArbitraryLawAdaptation.transportedSelection_mass
#print axioms ThresholdHC.ArbitraryLawAdaptation.transportedSelection_objective
