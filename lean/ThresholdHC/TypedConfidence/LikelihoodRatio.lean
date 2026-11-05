import ThresholdHC.TypedConfidence.ParameterHybrid
import ThresholdHC.Tier5.PriorRatio

noncomputable section
open MeasureTheory
namespace ThresholdHC.TypedConfidence
open ThresholdHC ThresholdHC.Proofs ThresholdHC.CriticalEntropy ThresholdHC.ConfidenceTransfer
open ThresholdHC.Tier3 ThresholdHC.Tier5

theorem coinMass_eq_one_of_not_queried {m n : ℕ}
    (pol : List Bool → Option (Fin m)) (w : Prefix n) (i : Fin m)
    (hi : i ∉ queriedCoins pol w) (κ : Measure unitInterval) [IsProbabilityMeasure κ] :
    coinMass pol w i κ = 1 := by
  simp [coinMass,coinLike_eq_one_of_not_queried pol w i hi]

/-- The likelihood-ratio bound depends on the observation horizon, even if the
policy addresses arbitrarily large labels. -/
theorem parameter_quarter_ratio {m n : ℕ}
    (κ τ : Fin m → Measure unitInterval)
    [∀ i, IsProbabilityMeasure (κ i)] [∀ i, IsProbabilityMeasure (τ i)]
    (pol : List Bool → Option (Fin m)) (w : Prefix n) :
    parameterWeight (fun i => quarterMix (κ i) (τ i)) pol w ≤
      3^n * parameterWeight (fun i => quarterMix (τ i) (κ i)) pol w := by
  classical
  let P := fun i => coinMass pol w i (quarterMix (κ i) (τ i))
  let Q := fun i => coinMass pol w i (quarterMix (τ i) (κ i))
  have hp (i) : 0 ≤ P i := coinMass_nonneg _ _ _ _
  have hq (i) : 0 ≤ Q i := coinMass_nonneg _ _ _ _
  have hpoint (i) : P i ≤ (if i ∈ queriedCoins pol w then 3 else 1) * Q i := by
    by_cases hi : i ∈ queriedCoins pol w
    · simp only [hi,ite_true]
      dsimp [P,Q]
      rw [coinMass_quarter,coinMass_quarter]
      linarith [coinMass_nonneg pol w i (κ i),coinMass_nonneg pol w i (τ i)]
    · simp [P,Q,hi,coinMass_eq_one_of_not_queried pol w i hi]
  have hprod : (∏ i, P i) ≤ 3^(queriedCoins pol w).card * ∏ i, Q i := by
    calc
      _ ≤ ∏ i, (if i ∈ queriedCoins pol w then 3 else 1)*Q i :=
        Finset.prod_le_prod₀ (fun i _ => hp i) (fun i _ => hpoint i)
      _ = _ := by rw [Finset.prod_mul_distrib]; simp
  have hb := hprod.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 3) (queriedCoins_card_le pol w))
    (Finset.prod_nonneg fun i _ => hq i))
  rw [parameter_weight_factor,parameter_weight_factor]
  change pathValidity pol w * (∏ i, P i) ≤ 3^n * (pathValidity pol w * ∏ i, Q i)
  nlinarith [mul_le_mul_of_nonneg_left hb (pathValidity_nonneg pol w)]

end ThresholdHC.TypedConfidence
