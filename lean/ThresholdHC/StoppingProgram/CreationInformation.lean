import ThresholdHC.StoppingProgram.FinitePopulationInformation
import ThresholdHC.CriticalEntropy.CreationPopulation
import ThresholdHC.CriticalEntropy.PopulationWorkLaw

/-! Deterministic policies may use any natural-number coin labels. The finite
label bound is derived from the decision tree, separately for each policy. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.StoppingProgram
open ThresholdHC.CriticalEntropy ThresholdHC.ObservableSimulation
open ThresholdHC.Tier6 (Gap SignLaw)

theorem creation_population_information (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q r : SignLaw) (pol : List Bool → Option ℕ) (N : ℕ) :
    1-realFiniteAffinity
      (creationPopulationWeight (n := N) μ pol (fun d : Gap => (d : ℝ)) q.val)
      (creationPopulationWeight μ pol (fun d : Gap => (d : ℝ)) r.val) ≤
      (informationRatio μ N (midpointFourPriors q r)).toReal/4 *
        ∑ w : Fin N → Option Bool,
          creationPopulationWeight μ pol (fun d : Gap => (d : ℝ))
            (midpointPrior q r).val w*ThresholdHC.workOf w := by
  let cpol := ThresholdHC.Tier5.capPolicy (ThresholdHC.Tier5.coinCap N pol) pol
  have h := finite_population_information (N := N) μ q r cpol
  rw [finitePopulation_work_real μ _ _ _ (measurable_gapParameter false)
    (measurable_gapParameter true) (measurable_signUnit (midpointPrior q r))
    (fun d : Gap => (d : ℝ)) measurable_subtype_coe
    (fun d => ⟨d.property.1.le,d.property.2⟩)
    (ae_of_all _ (fun d => by simp [gapParameter,sub_eq_add_neg]))
    (ae_of_all _ (fun d => by simp [gapParameter])) cpol] at h
  have he (u : SignLaw) :
      creationPopulationWeight (n := N) μ pol (fun d : Gap => (d : ℝ)) u.val =
        finitePopulationWeight μ cpol (fun d : Gap => (d : ℝ)) (fun _ => u.val) := by
    funext w
    exact creationPopulationWeight_eq_finite μ pol _ u.val measurable_subtype_coe u.property.1 w
  rw [he q,he r,he (midpointPrior q r)]
  exact h

end ThresholdHC.StoppingProgram
