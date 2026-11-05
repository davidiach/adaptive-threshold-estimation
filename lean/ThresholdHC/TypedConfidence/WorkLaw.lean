import ThresholdHC.TypedConfidence.ParameterWork
import ThresholdHC.Tier3.StoppingBase

noncomputable section

namespace ThresholdHC.TypedConfidence
open ThresholdHC.CriticalEntropy
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
local instance populationWorkLawSymbolSpace : MeasurableSpace (Option Bool) := ⊤

theorem parameter_work_law {m n : ℕ}
    (κ : Fin m → Measure unitInterval) [∀ i, IsProbabilityMeasure (κ i)]
    (pol : List Bool → Option (Fin m)) :
    parameterExpectedWork κ pol n =
      ∑ w : Fin n → Option Bool, ENNReal.ofReal
        (parameterWeight κ pol w)*ENNReal.ofReal (ThresholdHC.workOf w) := by
  let F (w : Fin n → Option Bool) := ENNReal.ofReal (ThresholdHC.workOf w)
  have hm : Measurable F := measurable_of_countable F
  have hwork (w : Fin n → Option Bool) :
      ((∑ t : Fin n, if (w t).isSome then 1 else 0 : ℕ) : ℝ≥0∞) = F w := by
    dsimp only [F]
    rw [ThresholdHC.Proofs.workOf_eq_sum,
      ENNReal.ofReal_sum_of_nonneg (fun t ht => by split_ifs <;> norm_num)]
    simp only [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro t ht
    split_ifs <;> norm_num
  calc
    _ = ∫⁻ s, F ((populationSimulation pol n s).2) ∂Measure.pi (fun i : Fin m => parameterTapeLaw (κ i)) :=
      lintegral_congr (fun s => hwork _)
    _ = ∫⁻ w, F w ∂(Measure.pi (fun i : Fin m => parameterTapeLaw (κ i))).map
        (fun s => (populationSimulation pol n s).2) :=
      (lintegral_map hm (measurable_populationSimulation_word n pol)).symm
    _ = _ := by
      rw [parameter_word_law κ pol n,parameterWordLaw,lintegral_fintype]
      simp only [finiteWeightMeasure_singleton,F,mul_comm]

theorem parameter_work_real {m n : ℕ}
    (κ : Fin m → Measure unitInterval) [∀ i, IsProbabilityMeasure (κ i)]
    (pol : List Bool → Option (Fin m)) :
    (parameterExpectedWork κ pol n).toReal =
      ∑ w : Fin n → Option Bool, parameterWeight κ pol w*ThresholdHC.workOf w := by
  rw [parameter_work_law κ pol,
    ENNReal.toReal_sum (fun w _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
  apply Finset.sum_congr rfl
  intro w _
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (parameter_weight_nonneg κ pol w),
    ENNReal.toReal_ofReal (ThresholdHC.Tier3.workOf_nonneg w)]

end ThresholdHC.TypedConfidence
