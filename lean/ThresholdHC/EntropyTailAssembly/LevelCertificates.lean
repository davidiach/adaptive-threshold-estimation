import ThresholdHC.EntropyTailAssembly.AccuracySchedule
import ThresholdHC.EntropyTailAssembly.SelectedWork
import ThresholdHC.EntropyTailAssembly.OrdinaryKernels

/-! Error and expected-work certificates for each actual observable race.
The weights depend on the selected measure, but no component label is an
observation of the procedure. Zero selected mass has a probability-bank
fallback, so the construction remains defined at that boundary. -/

noncomputable section
open MeasureTheory Set Real
open scoped NNReal BigOperators

namespace ThresholdHC.EntropyTailAssembly
open ThresholdHC ThresholdHC.Tier6 ThresholdHC.EntropyTail ThresholdHC.EntropyTailUpper

def referenceWeights (σ : Measure Gap) (j : ℕ) : ℝ≥0 := by
  classical
  exact if σ = 0 then (if j = 0 then 1 else 0) else bandWeights σ j

theorem selected_inverseSquare_pos (σ : Measure Gap) [IsFiniteMeasure σ]
    {t : ℝ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) (hσ : σ ≠ 0) :
    0 < ∫ d : Gap, (d:ℝ)⁻¹^2 ∂σ := by
  have hn : 0 ≤ ∫ d : Gap, (d:ℝ)⁻¹^2 ∂σ := integral_nonneg (fun _ => sq_nonneg _)
  exact lt_of_le_of_ne hn (fun he => hσ (inverseSquare_zero_measure σ
    (inverseSquare_integrable_of_support σ ht hs) he.symm))

theorem referenceWeights_probability (σ : Measure Gap) [IsFiniteMeasure σ]
    {t : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ))
    (hN : bandEdge N < t) : HasSum (referenceWeights σ) 1 := by
  classical
  by_cases hσ : σ = 0
  · have he : referenceWeights σ = fun j => if j = 0 then 1 else 0 := by
      funext j
      simp [referenceWeights, hσ]
    rw [he]
    exact hasSum_ite_eq 0 1
  · have he : referenceWeights σ = bandWeights σ := by
      funext j
      simp [referenceWeights, hσ]
    rw [he]
    exact bandWeights_probability σ hs hN (selected_inverseSquare_pos σ ht hs hσ)

theorem selected_level_work (σ τ ζ : Measure Gap)
    [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)]
    {t ρ : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ))
    (hN : bandEdge N < t) (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ)
    (hρ : 0 < ρ) (hz : ζ.real univ ≤ ρ) (q : SignLaw)
    (hq : RareAboveTwo.RarePrior (σ+τ+ζ) ρ q) (l L : ℕ) :
    (∫ d, mixtureRaceWork q (negativeBankTest (referenceWeights σ) (levelEpsilon l))
      (positiveBankTest (σ+τ+ζ) (referenceWeights σ) (ρ*levelEpsilon l)) L d ∂σ) ≤
      128*(l+1)*costEntropy (fun j : Fin N => bandCost σ j.val) +
      6*(∫ d : Gap, (d:ℝ)⁻¹ ∂τ)^2/ρ := by
  by_cases hσ : σ = 0
  · subst σ
    simp only [integral_zero_measure]
    have hΓ := costEntropy_nonneg (fun j : Fin N => bandCost_nonneg (0:Measure Gap) j.val)
    positivity
  · have hA := selected_inverseSquare_pos σ ht hs hσ
    have he : referenceWeights σ = bandWeights σ := by
      funext j
      simp [referenceWeights, hσ]
    rw [he]
    have h := selected_work_bound σ τ ζ ht hs hN hA hτ (levelEpsilon_pos l)
      (levelEpsilon_le_one l) hρ hz q hq L
    have hlog := levelEpsilon_log l
    have h3 : log (3:ℝ) ≤ 2 := by linarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 3)]
    have hAΓ : (∫ d : Gap, (d:ℝ)⁻¹^2 ∂σ) ≤ costEntropy (fun j : Fin N => bandCost σ j.val) := by
      rw [inverseSquare_eq_band_total σ hs hN]
      exact costTotal_le_costEntropy (fun j => bandCost_nonneg σ j.val)
    have hΓ := costEntropy_nonneg (fun j : Fin N => bandCost_nonneg σ j.val)
    have h1 := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 12*(∫ d : Gap, (d:ℝ)⁻¹^2 ∂σ) by positivity)
    have h2 := mul_le_mul_of_nonneg_right h3 hA.le
    have h4 := mul_le_mul_of_nonneg_left hAΓ (show (0:ℝ) ≤ 108+48*l by positivity)
    have h5 : 0 ≤ (20+80*(l:ℝ))*costEntropy (fun j : Fin N => bandCost σ j.val) := by positivity
    nlinarith

theorem mixtureRaceWork_le_ordinary (q : SignLaw) (neg pos : PrefixTest) (L : ℕ) (d : Gap) :
    mixtureRaceWork q neg pos L d ≤ 2*ordinaryWorkKernel (Uniform713.cap L) (d:ℝ) := by
  have hp := mul_le_mul_of_nonneg_left (race_expected_work_le_ordinary neg pos L d true) (q.property.2 d).1
  have hn := mul_le_mul_of_nonneg_left (race_expected_work_le_ordinary neg pos L d false)
    (sub_nonneg.mpr (q.property.2 d).2)
  unfold mixtureRaceWork conditionalRaceWork
  nlinarith only [hp, hn]

theorem integrated_raceWork_le_ordinary (ξ : Measure Gap) [IsFiniteMeasure ξ]
    (q : SignLaw) (neg pos : PrefixTest) (L : ℕ) :
    (∫ d, mixtureRaceWork q neg pos L d ∂ξ) ≤ 2*ordinaryCost ξ (Uniform713.cap L) := by
  have h := integral_mono (integrable_mixtureRaceWork ξ q neg pos L)
    ((integrable_ordinaryWorkKernel ξ (by unfold Uniform713.cap; positivity)).const_mul 2)
    (mixtureRaceWork_le_ordinary q neg pos L)
  rw [integral_const_mul] at h
  exact h

theorem integrated_raceWork_le_cap (ξ : Measure Gap) [IsFiniteMeasure ξ]
    (q : SignLaw) (neg pos : PrefixTest) (L : ℕ) :
    (∫ d, mixtureRaceWork q neg pos L d ∂ξ) ≤ 2*Uniform713.cap L*ξ.real univ := by
  have h := integrated_raceWork_le_ordinary ξ q neg pos L
  have hc := ordinaryCost_le_cap ξ (M := Uniform713.cap L) (by unfold Uniform713.cap; positivity)
  nlinarith

theorem three_piece_level_work (σ τ ζ : Measure Gap)
    [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)]
    {t ρ : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ))
    (hN : bandEdge N < t) (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ)
    (hρ : 0 < ρ) (hz : ζ.real univ ≤ ρ) (q : SignLaw)
    (hq : RareAboveTwo.RarePrior (σ+τ+ζ) ρ q) (l L : ℕ) :
    (∫ d, mixtureRaceWork q (negativeBankTest (referenceWeights σ) (levelEpsilon l))
      (positiveBankTest (σ+τ+ζ) (referenceWeights σ) (ρ*levelEpsilon l)) L d ∂(σ+τ+ζ)) ≤
      128*(l+1)*costEntropy (fun j : Fin N => bandCost σ j.val) +
      6*(∫ d : Gap, (d:ℝ)⁻¹ ∂τ)^2/ρ + 2*ordinaryCost τ (Uniform713.cap L) +
      2*Uniform713.cap L*ζ.real univ := by
  let neg := negativeBankTest (referenceWeights σ) (levelEpsilon l)
  let pos := positiveBankTest (σ+τ+ζ) (referenceWeights σ) (ρ*levelEpsilon l)
  change (∫ d, mixtureRaceWork q neg pos L d ∂(σ+τ+ζ)) ≤ _
  rw [integral_add_measure (integrable_mixtureRaceWork (σ+τ) q neg pos L)
    (integrable_mixtureRaceWork ζ q neg pos L),
    integral_add_measure (integrable_mixtureRaceWork σ q neg pos L)
      (integrable_mixtureRaceWork τ q neg pos L)]
  exact add_le_add (add_le_add (selected_level_work σ τ ζ ht hs hN hτ hρ hz q hq l L)
    (integrated_raceWork_le_ordinary τ q neg pos L)) (integrated_raceWork_le_cap ζ q neg pos L)

theorem cap_twice (k : ℕ) : Uniform713.cap (2*k) = (4:ℝ)^k := by
  unfold Uniform713.cap
  rw [pow_mul]
  norm_num

theorem bank_level_error (μ ν ζ : Measure Gap) [IsProbabilityMeasure μ]
    [IsFiniteMeasure ν] [IsFiniteMeasure ζ] (hμ : μ = ν+ζ)
    (weights : ℕ → ℝ≥0) (hw : HasSum weights 1) {ρ : ℝ} (hρ : 0 < ρ)
    (q : SignLaw) (hq : RareAboveTwo.RarePrior μ ρ q) (l : ℕ)
    (hz : ζ.real univ ≤ levelAccuracy ρ l/8) :
    racePopulationError μ q (negativeBankTest weights (levelEpsilon l))
      (positiveBankTest μ weights (ρ*levelEpsilon l))
      (2*errorCapExponent ν (levelAccuracy ρ l) (levelAccuracy_pos hρ l)) ≤ levelAccuracy ρ l := by
  have h := bank_population_error_le μ weights hw (levelEpsilon_pos l).le
    (mul_pos hρ (levelEpsilon_pos l)).le q hq
    (2*errorCapExponent ν (levelAccuracy ρ l) (levelAccuracy_pos hρ l))
  change _ ≤ ρ*levelEpsilon l+ρ*levelEpsilon l+eta μ
    (Uniform713.cap (2*errorCapExponent ν (levelAccuracy ρ l) (levelAccuracy_pos hρ l))) at h
  rw [cap_twice, hμ, eta_add, levelEpsilon_accuracy] at h
  have hc := (errorCapExponent_spec ν (levelAccuracy_pos hρ l)).2
  have hz' := eta_le_mass ζ ((4:ℝ)^(errorCapExponent ν (levelAccuracy ρ l) (levelAccuracy_pos hρ l)))
  have hδ := levelAccuracy_pos hρ l
  rw [hμ, levelEpsilon_accuracy]
  linarith

end ThresholdHC.EntropyTailAssembly
