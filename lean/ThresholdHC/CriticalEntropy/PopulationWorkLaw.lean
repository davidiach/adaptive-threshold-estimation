import ThresholdHC.CriticalEntropy.PopulationTransfer
import ThresholdHC.Tier3.StoppingBase

noncomputable section

namespace ThresholdHC.CriticalEntropy
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
local instance populationWorkLawSymbolSpace : MeasurableSpace (Option Bool) := ⊤

theorem finitePopulation_work_law {D : Type} [MeasurableSpace D] {m n : ℕ}
    (μ : Measure D) [IsProbabilityMeasure μ] (p₀ p₁ q : D → unitInterval)
    (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q)
    (d : D → ℝ) (h₀d : ∀ᵐ x ∂μ, (p₀ x : ℝ) = 1/2-d x)
    (h₁d : ∀ᵐ x ∂μ, (p₁ x : ℝ) = 1/2+d x)
    (pol : List Bool → Option (Fin m)) :
    finitePopulationExpectedWork μ p₀ p₁ q pol n =
      ∑ w : Fin n → Option Bool, ENNReal.ofReal
        (finitePopulationWeight μ pol d (fun _ x => (q x : ℝ)) w)*ENNReal.ofReal (ThresholdHC.workOf w) := by
  let τ := parameterTapeLaw (populationParameterLaw μ p₀ p₁ q)
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
    _ = ∫⁻ s, F ((populationSimulation pol n s).2) ∂Measure.pi (fun _ : Fin m => τ) :=
      lintegral_congr (fun s => hwork _)
    _ = ∫⁻ w, F w ∂(Measure.pi (fun _ : Fin m => τ)).map
        (fun s => (populationSimulation pol n s).2) :=
      (lintegral_map hm (measurable_populationSimulation_word n pol)).symm
    _ = _ := by
      rw [population_tape_word_law μ p₀ p₁ h₀ h₁ (fun _ : Fin m => q) (fun _ => hq)
        d h₀d h₁d pol,lintegral_fintype]
      simp only [finiteWeightMeasure_singleton,F,mul_comm]

theorem finitePopulation_work_real {D : Type} [MeasurableSpace D] {m n : ℕ}
    (μ : Measure D) [IsProbabilityMeasure μ] (p₀ p₁ q : D → unitInterval)
    (h₀ : Measurable p₀) (h₁ : Measurable p₁) (hq : Measurable q)
    (d : D → ℝ) (hdm : Measurable d) (hd : ∀ x, 0 ≤ d x ∧ d x ≤ 1/2)
    (h₀d : ∀ᵐ x ∂μ, (p₀ x : ℝ) = 1/2-d x)
    (h₁d : ∀ᵐ x ∂μ, (p₁ x : ℝ) = 1/2+d x)
    (pol : List Bool → Option (Fin m)) :
    (finitePopulationExpectedWork μ p₀ p₁ q pol n).toReal =
      ∑ w : Fin n → Option Bool,
        finitePopulationWeight μ pol d (fun _ x => (q x : ℝ)) w*ThresholdHC.workOf w := by
  have hn := (finite_population_total μ pol d (fun _ x => (q x : ℝ)) hdm
    (fun _ => measurable_subtype_coe.comp hq) hd (fun _ x => (q x).property) (n := n)).1
  rw [finitePopulation_work_law μ p₀ p₁ q h₀ h₁ hq d h₀d h₁d pol,
    ENNReal.toReal_sum (fun w hw => ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
  apply Finset.sum_congr rfl
  intro w hw
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (hn w),
    ENNReal.toReal_ofReal (ThresholdHC.Tier3.workOf_nonneg w)]

end ThresholdHC.CriticalEntropy
