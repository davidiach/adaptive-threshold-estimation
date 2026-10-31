import ThresholdHC.EntropyTailExecution.IncrementBounds
import ThresholdHC.EntropyTailAssembly.BudgetCertificate

/-! The concrete scheduled bank family and its coupled population moments. -/

noncomputable section
open MeasureTheory Real
open scoped NNReal BigOperators

namespace ThresholdHC.EntropyTailExecution
open ThresholdHC.Tier6 ThresholdHC.EntropyTailUpper ThresholdHC.EntropyTailAssembly
open ThresholdHC.EntropyTailSampling ThresholdHC.ObservableSimulation ThresholdHC.RareAboveTwo

def bankFamily (μ ν : Measure Gap) [IsProbabilityMeasure μ] [IsFiniteMeasure ν]
    (w : ℕ → ℝ≥0) (hw : HasSum w 1) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4) (l : ℕ) : FiniteCall :=
  scheduledCall μ w hw hρ hρ1 l
    (2*errorCapExponent ν (levelAccuracy ρ l) (levelAccuracy_pos hρ l))

def bankFamilyCap (ν : Measure Gap) [IsFiniteMeasure ν] {ρ : ℝ} (hρ : 0 < ρ) (l : ℕ) : ℝ :=
  2*2^(2*errorCapExponent ν (levelAccuracy ρ l) (levelAccuracy_pos hρ l))

theorem bankFamily_cost_bound (μ ν : Measure Gap) [IsProbabilityMeasure μ] [IsFiniteMeasure ν]
    (w : ℕ → ℝ≥0) (hw : HasSum w 1) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4) (l : ℕ) (ω : ℕ → Bool) :
    ((bankFamily μ ν w hw hρ hρ1 l).cost ω:ℝ) ≤ bankFamilyCap ν hρ l := by
  unfold bankFamily scheduledCall bankFamilyCap
  exact_mod_cast raceCost_le (negativeBankTest w (levelEpsilon l))
    (positiveBankTest μ w (ρ*levelEpsilon l))
    (2*errorCapExponent ν (levelAccuracy ρ l) (levelAccuracy_pos hρ l)) ω

theorem bankFamily_binary (μ ν : Measure Gap) [IsProbabilityMeasure μ] [IsFiniteMeasure ν]
    (w : ℕ → ℝ≥0) (hw : HasSum w 1) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4) (l : ℕ) (ω : ℕ → Bool) :
    (bankFamily μ ν w hw hρ hρ1 l).value ω = 0 ∨ (bankFamily μ ν w hw hρ hρ1 l).value ω = 1 :=
  raceValue_zero_or_one _ _ _ _

theorem levelAccuracy_antitone {ρ : ℝ} (hρ : 0 ≤ ρ) : Antitone (levelAccuracy ρ) := by
  intro i j hij
  unfold levelAccuracy
  exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)) hρ

theorem bankFamily_bias (μ ν ζ : Measure Gap) [IsProbabilityMeasure μ]
    [IsFiniteMeasure ν] [IsFiniteMeasure ζ] (hμ : μ = ν+ζ)
    (w : ℕ → ℝ≥0) (hw : HasSum w 1) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4)
    (q : SignLaw) (hq : RarePrior μ ρ q) (l : ℕ) (hz : ζ.real Set.univ ≤ levelAccuracy ρ l/8) :
    |(∫ ω, (bankFamily μ ν w hw hρ hρ1 l).value ω ∂originalPopulationTapeLaw μ q)-signMean μ q.val|
      ≤ levelAccuracy ρ l :=
  (raceValue_bias_le μ q _ _ _).trans (bank_level_error μ ν ζ hμ w hw hρ q hq l hz)

theorem bankFamily_second (μ ν ζ : Measure Gap) [IsProbabilityMeasure μ]
    [IsFiniteMeasure ν] [IsFiniteMeasure ζ] (hμ : μ = ν+ζ)
    (w : ℕ → ℝ≥0) (hw : HasSum w 1) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4)
    (q : SignLaw) (hq : RarePrior μ ρ q) (l : ℕ) (hz : ζ.real Set.univ ≤ levelAccuracy ρ l/8) :
    (∫ ω, ((incrementCall (bankFamily μ ν w hw hρ hρ1) l).value ω)^2
      ∂originalPopulationTapeLaw μ q) ≤ 17*levelAccuracy ρ l := by
  cases l with
  | zero =>
    have he : (fun ω => ((incrementCall (bankFamily μ ν w hw hρ hρ1) 0).value ω)^2) =
        (bankFamily μ ν w hw hρ hρ1 0).value := by
      funext ω
      rcases bankFamily_binary μ ν w hw hρ hρ1 0 ω with h | h <;> simp [incrementCall,h]
    rw [he]
    have hb := (abs_le.mp (bankFamily_bias μ ν ζ hμ w hw hρ hρ1 q hq 0 hz)).2
    have hδ := levelAccuracy_zero ρ
    change signMean μ q.val ≤ ρ at hq
    linarith
  | succ l =>
    have hz' : ζ.real Set.univ ≤ levelAccuracy ρ l/8 :=
      hz.trans (div_le_div_of_nonneg_right (levelAccuracy_antitone hρ.le (by omega)) (by norm_num))
    have h := race_difference_population_moment μ q
      (negativeBankTest w (levelEpsilon (l+1))) (positiveBankTest μ w (ρ*levelEpsilon (l+1)))
      (negativeBankTest w (levelEpsilon l)) (positiveBankTest μ w (ρ*levelEpsilon l))
      (2*errorCapExponent ν (levelAccuracy ρ (l+1)) (levelAccuracy_pos hρ (l+1)))
      (2*errorCapExponent ν (levelAccuracy ρ l) (levelAccuracy_pos hρ l))
    change (∫ ω, ((incrementCall (bankFamily μ ν w hw hρ hρ1) (l+1)).value ω)^2
      ∂originalPopulationTapeLaw μ q) ≤ _ at h
    exact h.trans (by
      have he := add_le_add (bank_level_error μ ν ζ hμ w hw hρ q hq (l+1) hz)
        (bank_level_error μ ν ζ hμ w hw hρ q hq l hz')
      have hδ := levelAccuracy_succ ρ l
      linarith)

theorem bankFamily_work (σ τ ζ : Measure Gap)
    [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)]
    {t ρ : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ))
    (hN : ThresholdHC.EntropyTailQuantile.bandEdge N < t) (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4) (hz : ζ.real Set.univ ≤ ρ) (q : SignLaw)
    (hq : RarePrior (σ+τ+ζ) ρ q) (l : ℕ) :
    (∫ ω, ((bankFamily (σ+τ+ζ) (σ+τ) (referenceWeights σ)
      (referenceWeights_probability σ ht hs hN) hρ hρ1 l).cost ω:ℝ)
      ∂originalPopulationTapeLaw (σ+τ+ζ) q) ≤
      levelWorkCertificate σ τ ρ (ThresholdHC.EntropyTailQuantile.costEntropy
        (fun j : Fin N => ThresholdHC.EntropyTailQuantile.bandCost σ j.val)) (ζ.real Set.univ) hρ l := by
  rw [show (fun ω => ((bankFamily (σ+τ+ζ) (σ+τ) (referenceWeights σ)
      (referenceWeights_probability σ ht hs hN) hρ hρ1 l).cost ω:ℝ)) =
      fun ω => (raceCost (negativeBankTest (referenceWeights σ) (levelEpsilon l))
        (positiveBankTest (σ+τ+ζ) (referenceWeights σ) (ρ*levelEpsilon l))
        (2*errorCapExponent (σ+τ) (levelAccuracy ρ l) (levelAccuracy_pos hρ l)) ω:ℝ) from rfl,
    race_population_work]
  have h := three_piece_level_work σ τ ζ ht hs hN hτ hρ hz q hq l
    (2*errorCapExponent (σ+τ) (levelAccuracy ρ l) (levelAccuracy_pos hρ l))
  simpa only [cap_twice, levelWorkCertificate, mul_comm (ζ.real Set.univ), mul_assoc] using h

end ThresholdHC.EntropyTailExecution
