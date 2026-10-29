import ThresholdHC.RareAboveTwo.Unbiased
import ThresholdHC.RareAboveTwo.UniformWork
import ThresholdHC.CriticalUpper.UnbiasedWork

/-! Expected work remains finite after randomizing the level. -/
noncomputable section
namespace ThresholdHC.RareAboveTwo
open MeasureTheory Set ThresholdHC.CriticalEntropy ThresholdHC.Uniform713
open ThresholdHC.Tier6 ThresholdHC.ObservableSimulation
open scoped ENNReal

theorem coupledCost_population_bound (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (a ρ W : ℝ) (hW : 0 ≤ W)
    (hb : ∀ k : ℕ, (∫⁻ ω, ENNReal.ofReal (calibratedCost a ρ k ω : ℝ) ∂originalPopulationTapeLaw μ q) ≤
      ENNReal.ofReal (W*((k : ℝ)+1)^2)) (j : ℕ) :
    (∫⁻ ω, ENNReal.ofReal (coupledCost a ρ j ω : ℝ) ∂originalPopulationTapeLaw μ q) ≤
      ENNReal.ofReal (2*W*((j : ℝ)+1)^2) := by
  cases j with
  | zero =>
    apply (hb 0).trans
    apply ENNReal.ofReal_le_ofReal
    norm_num
    linarith
  | succ j =>
    calc
      _ ≤ ∫⁻ ω, ENNReal.ofReal (calibratedCost a ρ (j+1) ω : ℝ)+
          ENNReal.ofReal (calibratedCost a ρ j ω : ℝ) ∂originalPopulationTapeLaw μ q := by
        apply lintegral_mono
        intro ω
        dsimp only
        rw [← ENNReal.ofReal_add (by positivity : 0 ≤ (calibratedCost a ρ (j+1) ω : ℝ))
          (by positivity : 0 ≤ (calibratedCost a ρ j ω : ℝ))]
        exact ENNReal.ofReal_le_ofReal (by exact_mod_cast coupledCost_succ_le a ρ j ω)
      _ = (∫⁻ ω, ENNReal.ofReal (calibratedCost a ρ (j+1) ω : ℝ) ∂originalPopulationTapeLaw μ q)+
          (∫⁻ ω, ENNReal.ofReal (calibratedCost a ρ j ω : ℝ) ∂originalPopulationTapeLaw μ q) := by
        apply lintegral_add_left
        exact ENNReal.measurable_ofReal.comp
          ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp (measurable_calibratedCost a ρ (j+1)))
      _ ≤ ENNReal.ofReal (W*((j+1 : ℕ)+1)^2)+
          ENNReal.ofReal (W*((j : ℝ)+1)^2) := add_le_add (hb (j+1)) (hb j)
      _ ≤ _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        push_cast
        have hn : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
        have hsq : ((j : ℝ)+1)^2 ≤ ((j : ℝ)+2)^2 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ W)]

theorem rareUnbiased_work_bound (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw)
    (a ρ W : ℝ) (hW : 0 ≤ W)
    (hb : ∀ k : ℕ, (∫⁻ ω, ENNReal.ofReal (calibratedCost a ρ k ω : ℝ) ∂originalPopulationTapeLaw μ q) ≤
      ENNReal.ofReal (W*((k : ℝ)+1)^2)) :
    (∫⁻ z, stoppedProcedureWork (rareUnbiasedProcedure a ρ) z ∂samplingMeasure (originalPopulationTapeLaw μ q)) ≤
      ENNReal.ofReal (224*W) := by
  unfold samplingMeasure
  rw [lintegral_prod _ (measurable_stoppedProcedureWork _).aemeasurable]
  simp_rw [rareUnbiasedProcedure_work]
  rw [CriticalUpper.lintegral_levelMeasure]
  calc
    _ ≤ ∑' j : ℕ, ENNReal.ofReal (2*W*((3/4 : ℝ)^j*((j : ℝ)+1)^2)) := by
      apply ENNReal.tsum_le_tsum
      intro j
      calc
        _ ≤ ENNReal.ofReal (levelProb j)*ENNReal.ofReal (2*W*((j : ℝ)+1)^2) :=
          mul_le_mul' le_rfl (coupledCost_population_bound μ q a ρ W hW hb j)
        _ = ENNReal.ofReal (levelProb j*(2*W*((j : ℝ)+1)^2)) := by
          rw [ENNReal.ofReal_mul (levelProb_pos j).le]
        _ ≤ _ := by
          apply ENNReal.ofReal_le_ofReal
          have h := mul_le_mul_of_nonneg_right (CriticalUpper.levelProb_upper j)
            (by positivity : 0 ≤ 2*W*((j : ℝ)+1)^2)
          nlinarith only [h]
    _ = _ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity)
        (CriticalUpper.hasSum_work_geometric.mul_left (2*W)).summable,
        (CriticalUpper.hasSum_work_geometric.mul_left (2*W)).tsum_eq]
      congr 1
      ring

theorem uniform_unbiased_work (α : ℝ) (hα : 2 < α) :
    ∃ W : ℝ, 0 < W ∧ ∀ a ρ : ℝ, 0 < a → a ≤ 1/2 → 0 < ρ → ρ ≤ 1 →
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ], PowerMargin μ α a →
    ∀ q : SignLaw, RarePrior μ ρ q →
      (∫⁻ z, stoppedProcedureWork (rareUnbiasedProcedure a ρ) z ∂samplingMeasure (originalPopulationTapeLaw μ q)) ≤
        ENNReal.ofReal (W/a^2) := by
  obtain ⟨W,hW,hcal⟩ := uniform_calibrated_work α hα
  refine ⟨224*W,by positivity,?_⟩
  intro a ρ ha ha' hρ hρ1 μ _ hm q hq
  have hb (j : ℕ) : (∫⁻ ω, ENNReal.ofReal (calibratedCost a ρ j ω : ℝ) ∂originalPopulationTapeLaw μ q) ≤
      ENNReal.ofReal ((W/a^2)*((j : ℝ)+1)^2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (calibratedCost_integrable _ a ρ j)
      (ae_of_all _ (fun ω => Nat.cast_nonneg (calibratedCost a ρ j ω)))]
    exact ENNReal.ofReal_le_ofReal (hcal a ρ ha ha' hρ hρ1 μ hm q hq j)
  convert rareUnbiased_work_bound μ q a ρ (W/a^2) (by positivity) hb using 1 <;> congr 1 <;> ring

end ThresholdHC.RareAboveTwo
