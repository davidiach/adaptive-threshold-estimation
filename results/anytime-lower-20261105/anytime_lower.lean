
import ThresholdHC.AnytimeLower.Quartet
import ThresholdHC.AnytimeLower.TailInformation
noncomputable section
set_option linter.unusedVariables false
open MeasureTheory InformationTheory
open scoped ENNReal
open ThresholdHC.AnytimeLower ThresholdHC.Tier3 ThresholdHC.Tier6
open ThresholdHC.RareAboveTwo ThresholdHC.StoppingProgram ThresholdHC.ConfidenceTransfer
open ThresholdHC.ObservableSimulation ThresholdHC.Genie

example : ∀ {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q r : SignLaw) (a b : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1)
    (hm : 1/2 ≤ a+b ∧ a+b ≤ 3/2) (i : CountState N),
    (1/2)*countCoefficient μ (midpointPrior q r) i ≤
      countCoefficient μ (midpointPrior (mixPrior q r a ha) (mixPrior q r b hb)) i :=
  @segment_midpoint_coefficient

example : ∀ {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q r : SignLaw) (a b : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1)
    (i : CountState N),
    countCoefficient μ (mixPrior q r b hb) i-countCoefficient μ (mixPrior q r a ha) i =
      (a-b)*(countCoefficient μ r i-countCoefficient μ q i) :=
  @segment_contrast

example : ∀ {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q r : SignLaw) (a b : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1)
    (hm : 1/2 ≤ a+b ∧ a+b ≤ 3/2) (f : Flow N),
    flowInformation μ (midpointFourPriors (mixPrior q r a ha) (mixPrior q r b hb)) f ≤
      ENNReal.ofReal (2*(a-b)^2)*flowInformation μ (midpointFourPriors q r) f :=
  @segment_information

example : ∀ {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q r : SignLaw) (a b : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1)
    (hm : 1/2 ≤ a+b ∧ a+b ≤ 3/2) (f : Flow N) (hf : FlowCone f),
    (1/2)*countMean μ (midpointPrior q r) f.continueWeight ≤
      countMean μ (midpointPrior (mixPrior q r a ha) (mixPrior q r b hb)) f.continueWeight :=
  @segment_work

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ]
    (N : ℕ) (q r : SignLaw) (a b : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1)
    (hm : 1/2 ≤ a+b ∧ a+b ≤ 3/2),
    informationRatio μ N (midpointFourPriors (mixPrior q r a ha) (mixPrior q r b hb)) ≤
      ENNReal.ofReal (4*(a-b)^2)*informationRatio μ N (midpointFourPriors q r) :=
  @segment_informationRatio

example : ∀ (q r : SignLaw) (x y : ℝ)
    (hx : 3/8 ≤ x ∧ x ≤ 5/8) (hy : 3/8 ≤ y ∧ y ≤ 5/8),
    smoothedSign
      (mixPrior q r ((3*x-y)/2) ⟨by linarith,by linarith⟩)
      (mixPrior q r ((3*y-x)/2) ⟨by linarith,by linarith⟩) =
      mixPrior q r x ⟨by linarith,by linarith⟩ :=
  @segment_quarter_identity

example : ∀ {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    (q : SignLaw) (n : ℕ),
    (∫ z, ThresholdHC.workOf (processPrefix n z.2) ∂experimentLaw μ A q) ≤ n :=
  @prefix_expected_work_le

example : ∀ {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    (q r : SignLaw) (J : ℝ) (hJ : 0 ≤ J)
    (hI : ∀ m, informationRatio μ m (midpointFourPriors q r) ≤ ENNReal.ofReal J)
    (x y : ℝ) (hx : 3/8 ≤ x ∧ x ≤ 5/8) (hy : 3/8 ≤ y ∧ y ≤ 5/8) (n : ℕ),
    klDiv (observablePrefixLaw μ A (mixPrior q r x ⟨by linarith,by linarith⟩) n)
      (observablePrefixLaw μ A (mixPrior q r y ⟨by linarith,by linarith⟩) n) ≤
        ENNReal.ofReal ((64/3)*J*(x-y)^2*n) :=
  @segment_prefix_kl

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ : ℝ} (Q : FourPriors) (hQ : Admissible μ ρ Q)
    (x : ℝ) (hx : 3/8 ≤ x ∧ x ≤ 5/8), RarePrior μ ρ (centralPrior Q x hx) :=
  @centralPrior_rare

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ]
    (Q : FourPriors) (x y : ℝ) (hx : 3/8 ≤ x ∧ x ≤ 5/8) (hy : 3/8 ≤ y ∧ y ≤ 5/8),
    signMean μ (centralPrior Q x hx).val-signMean μ (centralPrior Q y hy).val =
      (y-x)*(signMean μ Q.high.val-signMean μ Q.low.val)/3 :=
  @centralPrior_mean_difference

example : ∀ {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ] (A : AdaptiveEstimator R)
    (Q : FourPriors) (J : ℝ) (hJ : 0 ≤ J)
    (hI : infiniteInformationRatio μ Q ≤ ENNReal.ofReal J)
    (x y : ℝ) (hx : 3/8 ≤ x ∧ x ≤ 5/8) (hy : 3/8 ≤ y ∧ y ≤ 5/8) (n : ℕ),
    klDiv (observablePrefixLaw μ A (centralPrior Q x hx) n)
      (observablePrefixLaw μ A (centralPrior Q y hy) n) ≤
        ENNReal.ofReal ((64/3)*J*(x-y)^2*n) :=
  @quartet_prefix_kl

example : ∀ {q A B : ℝ} (hq : 1/4 ≤ q ∧ q ≤ 3/4)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hs : 0 < A+B),
    0 ≤ posteriorMass q A B ∧ posteriorMass q A B ≤ 1 :=
  @posteriorMass_bounds

example : ∀ {q r A B : ℝ}
    (hq : 1/4 ≤ q ∧ q ≤ 3/4) (hr : 1/4 ≤ r ∧ r ≤ 3/4)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hs : 0 < A+B),
    |posteriorMass q A B-posteriorMass r A B| ≤ 4*|q-r| :=
  @posteriorMass_lipschitz

example : ∀ {q A B d : ℝ} (hq : 1/4 ≤ q ∧ q ≤ 3/4)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hs : 0 < A+B) (hd : 0 ≤ d ∧ d ≤ 1/4),
    1/4 ≤ predictiveHead q A B d ∧ predictiveHead q A B d ≤ 3/4 :=
  @predictiveHead_bounds

example : ∀ {q r A B d ε : ℝ}
    (hq : 1/4 ≤ q ∧ q ≤ 3/4) (hr : 1/4 ≤ r ∧ r ≤ 3/4)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hs : 0 < A+B) (hd : 0 ≤ d ∧ d ≤ 1/4)
    (he : 0 ≤ ε) (hcontrast : d*|q-r| ≤ ε/32),
    ThresholdHC.klB (predictiveHead q A B d) (predictiveHead r A B d) ≤ ε^2 :=
  @predictiveHead_kl
#print axioms ThresholdHC.AnytimeLower.centralPrior_mean_difference
#print axioms ThresholdHC.AnytimeLower.centralPrior_rare
#print axioms ThresholdHC.AnytimeLower.posteriorMass_bounds
#print axioms ThresholdHC.AnytimeLower.posteriorMass_lipschitz
#print axioms ThresholdHC.AnytimeLower.predictiveHead_bounds
#print axioms ThresholdHC.AnytimeLower.predictiveHead_kl
#print axioms ThresholdHC.AnytimeLower.prefix_expected_work_le
#print axioms ThresholdHC.AnytimeLower.quartet_prefix_kl
#print axioms ThresholdHC.AnytimeLower.segment_contrast
#print axioms ThresholdHC.AnytimeLower.segment_information
#print axioms ThresholdHC.AnytimeLower.segment_informationRatio
#print axioms ThresholdHC.AnytimeLower.segment_midpoint_coefficient
#print axioms ThresholdHC.AnytimeLower.segment_prefix_kl
#print axioms ThresholdHC.AnytimeLower.segment_quarter_identity
#print axioms ThresholdHC.AnytimeLower.segment_work
