import ThresholdHC.StoppingProgram.TableCall
import ThresholdHC.EntropyTailUpper.PopulationErrors
import ThresholdHC.CriticalEntropy.FiniteObservation

/-! Exact finite-prefix probabilities and moments under the original
observable population-tape law, including endpoint Bernoulli parameters. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier2
open ThresholdHC.Tier6 (Gap SignLaw)
open ThresholdHC.ObservableSimulation ThresholdHC.CriticalEntropy
open ThresholdHC.RareAboveTwo ThresholdHC.EntropyTailUpper

theorem gap_tape_prefix_real (s : Bool) (d : Gap) (n : ℕ) (w : Fin n → Bool) :
    (tapeMeasure (gapParameter s d)).real (tapePrefix n ⁻¹' {w}) = prefixLikelihood s n (wordHeads w) d := by
  rw [Measure.real,tape_prefix_mass,ENNReal.toReal_ofReal (streamProb_nonneg_of_unit _ _),streamProb_heads]
  cases s <;> simp only [gapParameter,prefixLikelihood,Bool.false_eq_true,ite_false,ite_true]
  · congr 2; ring
  · congr 2; ring

theorem population_tape_prefix_real (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (n : ℕ) (w : Fin n → Bool) :
    (originalPopulationTapeLaw μ q).real (tapePrefix n ⁻¹' {w}) = prefixCoefficient μ q n (wordHeads w) := by
  let E := tapePrefix n ⁻¹' {w}
  have hE : MeasurableSet E := (measurableSet_singleton w).preimage (measurable_prefix n)
  have h := originalTape_integral_mixture μ q (E.indicator (fun _ => (1:ℝ)))
    (measurable_const.indicator hE) 1 (fun ω => by by_cases hω : ω ∈ E <;> simp [Set.indicator,hω])
  simp only [integral_indicator_const _ hE,smul_eq_mul,mul_one] at h
  change (originalPopulationTapeLaw μ q).real E = _
  rw [h]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun d => by
    dsimp only [E]
    rw [gap_tape_prefix_real,gap_tape_prefix_real]))

theorem population_prefix_integral (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (n : ℕ) (F : (Fin n → Bool) → ℝ) :
    (∫ ω, F (tapePrefix n ω) ∂originalPopulationTapeLaw μ q) =
      ∑ w : Fin n → Bool, prefixCoefficient μ q n (wordHeads w)*F w := by
  have hi : Integrable F ((originalPopulationTapeLaw μ q).map (tapePrefix n)) :=
    Integrable.of_bound (measurable_of_countable F).aestronglyMeasurable (∑ w, ‖F w‖)
      (Filter.Eventually.of_forall (fun w => Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ w)))
  rw [← integral_map (measurable_prefix n).aemeasurable (measurable_of_countable F).aestronglyMeasurable,
    integral_fintype hi]
  apply Finset.sum_congr rfl
  intro w _
  rw [Measure.real,Measure.map_apply (measurable_prefix n) (measurableSet_singleton w)]
  change (originalPopulationTapeLaw μ q).real (tapePrefix n ⁻¹' {w})*F w = _
  rw [population_tape_prefix_real]

theorem tableValue_full_prefix {N : ℕ} (b : CountState N → Bool) (y : CountState N → ℝ)
    (ω : ℕ → Bool) :
    tableValue b y ω = tableValue b y (completePrefix N (tapePrefix N ω)) := by
  exact (prefixSearchValue_ext (tableHit b) (fun n w => arrayAt y n (wordHeads w)) N ω _
    (prefix_eq_restrict (tapePrefix_completePrefix N _).symm (prefixSearchCost_le (tableHit b) N ω))).symm

theorem tableValue_integral_full_prefix {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) (b : CountState N → Bool) (y : CountState N → ℝ) :
    (∫ ω, tableValue b y ω ∂originalPopulationTapeLaw μ q) =
      ∑ w : Fin N → Bool, prefixCoefficient μ q N (wordHeads w)*tableValue b y (completePrefix N w) := by
  have he : tableValue b y = fun ω => tableValue b y (completePrefix N (tapePrefix N ω)) :=
    funext (tableValue_full_prefix b y)
  conv_lhs => rw [he]
  exact population_prefix_integral μ q N (fun w => tableValue b y (completePrefix N w))

end ThresholdHC.StoppingProgram
