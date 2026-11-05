import ThresholdHC.LawAdaptation.Full

noncomputable section
open MeasureTheory
namespace ThresholdHC.LawAdaptation
open ThresholdHC.Tier3 ThresholdHC.Tier6 ThresholdHC.HardBudget ThresholdHC.Anytime
open ThresholdHC.ObservableSimulation

variable {ι : Type} [Nonempty ι] {R : ι → ℕ → Type}
  [∀ i j, MeasurableSpace (R i j)]

theorem budgetInterval_nested (laws : ι → Measure Gap) (n m : ℕ) (η M : ℝ)
    (base : ∀ i j, AdaptiveEstimator (R i j)) (rad : ι → ℕ → ℝ)
    {B C : ℕ} (hBC : B ≤ C) (z : (∀ i j, R i j) × Table) :
    (budgetInterval laws n m η M base rad B z).1 ≤
      (budgetInterval laws n m η M base rad C z).1 ∧
    (budgetInterval laws n m η M base rad C z).2 ≤
      (budgetInterval laws n m η M base rad B z).2 := by
  rw [budgetInterval_eq,budgetInterval_eq]
  by_cases hB : pilotCost n m ≤ B
  · have hC := hB.trans hBC
    simp only [ite_eq_left hB,ite_eq_left hC,postTableInterval]
    exact interval_nested _ _ _ _ _
      (stageCount_nat_mono (Nat.sub_le_sub_right hBC _))
  · simp only [ite_eq_right hB]
    by_cases hC : pilotCost n m ≤ C
    · simp only [ite_eq_left hC,postTableInterval]
      exact interval_nested _ _ _ _ _ (Nat.zero_le _)
    · simp only [ite_eq_right hC,le_refl,and_self]

/-- At each physical budget, both reported endpoints have exactly their law
in the original observable experiment, jointly, with the same policy. -/
theorem original_budget_interval_law (μ : Measure Gap) [IsProbabilityMeasure μ]
    (laws : ι → Measure Gap) (n m : ℕ) (η M : ℝ)
    (base : ∀ i j, AdaptiveEstimator (R i j)) (rad : ι → ℕ → ℝ)
    (B : ℕ) (q : SignLaw) :
    (experimentLaw μ (budgetEndpoint laws n m η M base rad B false) q).map
      (fun z => ((budgetEndpoint laws n m η M base rad B false).output (z.1.1,z.2),
        (budgetEndpoint laws n m η M base rad B true).output (z.1.1,z.2))) =
      (familyStreamLaw μ base q).map (budgetInterval laws n m η M base rad B) := by
  let A := budgetEndpoint laws n m η M base rad B false
  let U := budgetEndpoint laws n m η M base rad B true
  let F (z : (∀ i j, R i j) × ProcessTape) := (A.output z,U.output z)
  have hF : Measurable F := A.output_measurable.prodMk U.output_measurable
  have hg : Measurable (fun z : PopulationSeed (∀ i j, R i j) × ProcessTape => (z.1.1,z.2)) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hp : Measurable (fun z : (∀ i j, R i j) × Table =>
      (z.1,populationPath (A.policy z.1) z.2)) :=
    measurable_fst.prodMk (measurable_seeded_populationPath A.policy
      (fun xs => measurable_to_countable' (A.policy_measurable xs)))
  have he : originalSimulationLaw μ A q = familyStreamLaw μ base q := by
    unfold originalSimulationLaw familyStreamLaw
    have hs : A.randomLaw = familySeedLaw base := by
      dsimp [A,budgetEndpoint]
      split_ifs <;> rfl
    rw [hs]
    rfl
  change (experimentLaw μ A q).map (F ∘ fun z => (z.1.1,z.2)) = _
  rw [← Measure.map_map hF hg,original_observable_simulation_law,Measure.map_map hF hp,he]
  rfl

end ThresholdHC.LawAdaptation

