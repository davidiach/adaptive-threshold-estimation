import SharpAttainment
import SharpEntropy
import SharpPrefixCost

open MeasureTheory InformationTheory
open scoped ENNReal
open ThresholdHC ThresholdHC.Tier3 ThresholdHC.Tier5 ThresholdHC.Tier6 ThresholdHC.SharpRMS

example : ∀ (μ : Measure Gap) [IsProbabilityMeasure μ], UniformBudget μ fourFlips 4 :=
  @four_flips_budget

example : ∀ q : SignLaw, squaredRisk (experimentLaw (Measure.dirac endpointGap) fourFlips q)
    (populationOutput fourFlips) (signMean (Measure.dirac endpointGap) q.val) =
    ENNReal.ofReal (1/36 : ℝ) := four_flips_squared_risk

example : minimaxRisk (Measure.dirac endpointGap) 4 ≤ ENNReal.ofReal (1/6:ℝ) :=
  endpoint_minimax_upper

example : ∀ {Ω : Type} [MeasurableSpace Ω] (P Qp Qm : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Qp] [IsProbabilityMeasure Qm]
    (X : Ω → ℝ), Measurable X →
    klDiv P Qp + klDiv P Qm ≤ ENNReal.ofReal (2*3283/3150:ℝ) →
    ENNReal.ofReal (1/9:ℝ) ≤ max (squaredRisk P X 0)
      (max (squaredRisk Qp X (7/10)) (squaredRisk Qm X (-(7/10)))) :=
  @three_bias_risk

example : ∀ {n : ℕ} (pol : List Bool → Option ℕ) (w : Prefix n) (d t : ℕ → ℝ),
    (∀ i, 0 ≤ d i ∧ d i ≤ 1/2) →
    creationLaw pol d (fun i => (1+t i)/2) w =
      creationLaw pol d (fun _ => 1/2) w *
        ∏ i : Fin (coinCap n pol), (1+t i.val*
          posterior (capPolicy (coinCap n pol) pol) w (fun j => d j.val) i) :=
  @creation_tilt

example : ∀ {n : ℕ} (pol : List Bool → Option ℕ) (s : ℝ), 0 ≤ s → s ≤ 1 →
    (∑ w : Prefix n, creationLaw pol (fun _ => s/2) (fun _ => 1/2) w *
      ∑ i : Fin (coinCap n pol), posterior (capPolicy (coinCap n pol) pol) w (fun _ => s/2) i *
        netCount (capPolicy (coinCap n pol) pol) w i) =
      s * ∑ w : Prefix n, creationLaw pol (fun _ => s/2) (fun _ => 1/2) w * workOf w :=
  @creation_wald

example : ∀ {n : ℕ} (pol : List Bool → Option ℕ) (s B : ℝ),
    0 < s → s ≤ 2/5 → s^2*B = 4 →
    (∑ w : Prefix n, creationLaw pol (fun _ => s/2) (fun _ => 1/2) w * workOf w) ≤ B →
    pairedCost (n := n) (creationLaw pol (fun _ => s/2) (fun _ => 1/2))
      (creationLaw pol (fun _ => s/2) (fun _ => (1+7/10)/2))
      (creationLaw pol (fun _ => s/2) (fun _ => (1+ -(7/10))/2)) ≤ 2*3283/3150 :=
  @creation_paired_cost

#print axioms creation_paired_cost
#print axioms four_flips_budget
#print axioms four_flips_squared_risk
#print axioms endpoint_minimax_upper
#print axioms three_bias_risk
#print axioms creation_tilt
#print axioms creation_wald
