import ThresholdHC.FixedPlan.Tail
import ThresholdHC.EntropyTailExecution.ActualPlan
import ThresholdHC.RareAboveTwo.PopulationError

/-! The fixed plan in the original adaptive experiment. Its work is exactly
`n(2k+1)`, and its output has the law of the average of `n` independent majority
votes of coins drawn from the original population tape law. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ThresholdHC.FixedPlan
open ThresholdHC.Tier6 ThresholdHC.Tier2 ThresholdHC.CriticalEntropy
open ThresholdHC.ObservableSimulation ThresholdHC.EntropyTailExecution ThresholdHC.BlindUpper

theorem list_range_map_sum (N : ℕ) (f : ℕ → ℝ) :
    ((List.range N).map f).sum = ∑ i ∈ Finset.range N, f i := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

theorem plannedCost_majority (k n : ℕ) (s : ℕ → ℕ → Bool) :
    plannedCost (fun _ => majorityCall k n) (List.range n) s = n*(2*k+1) := by
  simp [plannedCost, majorityCall]

theorem plannedValue_majority (k n' : ℕ) (s : ℕ → ℕ → Bool) :
    plannedValue (fun _ => majorityCall k (n'+1)) (List.range (n'+1)) s =
      productionAverage (majorityVote k) n' s := by
  change ((List.range (n'+1)).map (fun j => ((n'+1 : ℕ) : ℝ)⁻¹ * majorityVote k (s j))).sum =
    ((n' : ℝ)+1)⁻¹ * ∑ i : Fin (n'+1), majorityVote k (s i)
  rw [list_range_map_sum, ← Finset.mul_sum, Finset.sum_range (fun j => majorityVote k (s j))]
  push_cast
  rfl

/-- The plan spends exactly `n(2k+1)` flips. -/
theorem majority_expectedWork (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (k n : ℕ) :
    expectedWork μ (majorityEstimator k n) q = ((n*(2*k+1) : ℕ) : ℝ≥0∞) := by
  unfold majorityEstimator
  rw [finitePlan_expectedWork _ _ _ (fun _ => List.nodup_range) μ q]
  simp only [plannedCost_majority]
  rw [lintegral_const, measure_univ, mul_one]

theorem majority_output_lintegral (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (k n' : ℕ) (G : ℝ → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ z, G (populationOutput (majorityEstimator k (n'+1)) z)
      ∂experimentLaw μ (majorityEstimator k (n'+1)) q) =
      ∫⁻ x, G (finiteAverage (majorityVote k) n' x)
        ∂Measure.pi (fun _ : Fin (n'+1) => originalPopulationTapeLaw μ q) := by
  have he := original_observable_lintegral μ (majorityEstimator k (n'+1)) q
    (G ∘ (majorityEstimator k (n'+1)).output) (hG.comp (majorityEstimator k (n'+1)).output_measurable)
  refine he.trans ?_
  have hz : ∀ z : Unit × (ℕ → ℕ → Bool),
      (G ∘ (majorityEstimator k (n'+1)).output)
        (z.1, populationPath ((majorityEstimator k (n'+1)).policy z.1) z.2) =
      G (productionAverage (majorityVote k) n' z.2) := fun z => by
    change G (finitePlanOutput (fun _ => majorityCall k (n'+1)) (fun _ => List.range (n'+1))
      (z.1, populationPath (finitePlanPolicy (fun _ => majorityCall k (n'+1))
        (fun _ => List.range (n'+1)) z.1) z.2)) = _
    rw [finitePlan_population_output _ _ z.1 z.2 List.nodup_range, plannedValue_majority]
  rw [lintegral_congr hz]
  have hm := measurable_productionAverage (majorityVote k) (measurable_majorityVote k) n'
  have hm' := measurable_finiteAverage (majorityVote k) (measurable_majorityVote k) n'
  calc
    (∫⁻ z, G (productionAverage (majorityVote k) n' z.2)
        ∂originalSimulationLaw μ (majorityEstimator k (n'+1)) q) =
        ∫⁻ s, G (productionAverage (majorityVote k) n' s)
          ∂Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q) :=
      (measurePreserving_snd (μ := Measure.dirac ())
        (ν := Measure.infinitePi (fun _ : ℕ => originalPopulationTapeLaw μ q))).lintegral_comp
        (f := fun s => G (productionAverage (majorityVote k) n' s)) (hG.comp hm)
    _ = _ :=
      (productionPrefix_preserving (originalPopulationTapeLaw μ q) n').lintegral_comp
        (f := fun x => G (finiteAverage (majorityVote k) n' x)) (hG.comp hm')

/-- The output law is the law of the average of `n` independent majority votes. -/
theorem majority_output_law (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (k n' : ℕ) :
    (experimentLaw μ (majorityEstimator k (n'+1)) q).map (populationOutput (majorityEstimator k (n'+1))) =
      (Measure.pi (fun _ : Fin (n'+1) => originalPopulationTapeLaw μ q)).map
        (finiteAverage (majorityVote k) n') := by
  apply Measure.ext_of_lintegral
  intro G hG
  rw [lintegral_map hG (measurable_populationOutput _),
    lintegral_map hG (measurable_finiteAverage _ (measurable_majorityVote k) n')]
  exact majority_output_lintegral μ q k n' G hG

theorem memLp_majorityVote (k : ℕ) (P : Measure (ℕ → Bool)) [IsFiniteMeasure P] :
    MemLp (majorityVote k) 2 P :=
  memLp_of_bounded (ae_of_all _ (majorityVote_mem k)) (measurable_majorityVote k).aestronglyMeasurable 2

theorem majority_output_mean (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (k n' : ℕ) :
    (∫ z, populationOutput (majorityEstimator k (n'+1)) z ∂experimentLaw μ (majorityEstimator k (n'+1)) q) =
      ∫ ω, majorityVote k ω ∂originalPopulationTapeLaw μ q := by
  have ho := measurable_populationOutput (majorityEstimator k (n'+1))
  have hf := measurable_finiteAverage (majorityVote k) (measurable_majorityVote k) n'
  calc
    _ = ∫ x : ℝ, x ∂(experimentLaw μ (majorityEstimator k (n'+1)) q).map
        (populationOutput (majorityEstimator k (n'+1))) :=
      (integral_map ho.aemeasurable measurable_id.aestronglyMeasurable).symm
    _ = ∫ x, finiteAverage (majorityVote k) n' x
        ∂Measure.pi (fun _ : Fin (n'+1) => originalPopulationTapeLaw μ q) := by
      rw [majority_output_law]
      exact integral_map hf.aemeasurable measurable_id.aestronglyMeasurable
    _ = _ := finiteAverage_mean _ _ (memLp_majorityVote k _) n'

theorem majority_output_evariance (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (k n' : ℕ) :
    evariance (populationOutput (majorityEstimator k (n'+1))) (experimentLaw μ (majorityEstimator k (n'+1)) q) =
      ENNReal.ofReal (variance (majorityVote k) (originalPopulationTapeLaw μ q) / ((n' : ℝ)+1)) := by
  have hL := memLp_majorityVote k (originalPopulationTapeLaw μ q)
  have hfm := measurable_finiteAverage (majorityVote k) (measurable_majorityVote k) n'
  rw [evariance_eq_lintegral_ofReal, majority_output_mean]
  rw [majority_output_lintegral μ q k n'
    (fun x => ENNReal.ofReal ((x - ∫ ω, majorityVote k ω ∂originalPopulationTapeLaw μ q)^2))
    ((measurable_id.sub measurable_const).pow_const 2).ennreal_ofReal]
  rw [← finiteAverage_mean _ _ hL n', ← finiteAverage_variance _ _ hL n',
    ofReal_variance (finiteAverage_memLp _ _ hL n'), evariance_eq_lintegral_ofReal]

theorem majority_output_squaredRisk (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (k n' : ℕ) (a : ℝ) :
    squaredRisk (experimentLaw μ (majorityEstimator k (n'+1)) q)
      (populationOutput (majorityEstimator k (n'+1))) a =
      ENNReal.ofReal (variance (majorityVote k) (originalPopulationTapeLaw μ q) / ((n' : ℝ)+1) +
        ((∫ ω, majorityVote k ω ∂originalPopulationTapeLaw μ q) - a)^2) := by
  have hL := memLp_majorityVote k (originalPopulationTapeLaw μ q)
  unfold squaredRisk
  rw [majority_output_lintegral μ q k n' (fun x => ENNReal.ofReal ((x - a)^2))
    ((measurable_id.sub measurable_const).pow_const 2).ennreal_ofReal]
  have hi : Integrable (fun x => (finiteAverage (majorityVote k) n' x - a)^2)
      (Measure.pi (fun _ : Fin (n'+1) => originalPopulationTapeLaw μ q)) :=
    ((finiteAverage_memLp _ _ hL n').sub (memLp_const a)).integrable_sq
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun x => sq_nonneg _)),
    finiteAverage_mse _ _ hL n' a]

/-- Mean vote of a coin from the original population. -/
theorem majorityVote_population_mean (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw) (k : ℕ) :
    (∫ ω, majorityVote k ω ∂originalPopulationTapeLaw μ q) =
      ∫ d, q.val d * (1 - majorityMiss k d) + (1 - q.val d) * majorityMiss k d ∂μ := by
  rw [RareAboveTwo.originalTape_integral_mixture μ q (majorityVote k) (measurable_majorityVote k) 1
    (fun ω => by
      rcases majorityVote_binary k ω with h | h <;> rw [h] <;> norm_num)]
  simp_rw [majorityVote_integral_true, majorityVote_integral_false]

theorem majorityVote_variance_le (k : ℕ) (P : Measure (ℕ → Bool)) [IsProbabilityMeasure P] :
    variance (majorityVote k) P ≤ 1/4 := by
  have h := variance_le_sq_of_bounded (ae_of_all P (majorityVote_mem k))
    (measurable_majorityVote k).aemeasurable
  norm_num at h
  linarith

end ThresholdHC.FixedPlan
