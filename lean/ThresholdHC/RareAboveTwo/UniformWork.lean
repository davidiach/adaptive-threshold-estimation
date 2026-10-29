import ThresholdHC.RareAboveTwo.PopulationWork

/-! A quadratic level envelope, uniform over rarity and all margin laws. -/
noncomputable section
open MeasureTheory
namespace ThresholdHC.RareAboveTwo
open ThresholdHC.Tier6 ThresholdHC.Uniform713 ThresholdHC.ObservableSimulation

theorem uniform_calibrated_work (α : ℝ) (hα : 2 < α) :
    ∃ W : ℝ, 0 < W ∧ ∀ a ρ : ℝ, 0 < a → a ≤ 1/2 → 0 < ρ → ρ ≤ 1 →
    ∀ (μ : Measure Gap) [IsProbabilityMeasure μ], PowerMargin μ α a →
    ∀ q : SignLaw, RarePrior μ ρ q → ∀ j : ℕ,
      (∫ ω, (calibratedCost a ρ j ω : ℝ) ∂originalPopulationTapeLaw μ q) ≤
        (W/a^2)*((j : ℝ)+1)^2 := by
  let p : ℝ := (min α 4+2)/4
  have hp : 1 < p := by dsimp [p]; have := lt_min hα (by norm_num : (2 : ℝ) < 4); linarith
  have hp2 : p ≤ 2 := by dsimp [p]; have := min_le_right α (4 : ℝ); linarith
  have hsα : 2*p < α := by dsimp [p]; have := min_le_left α (4 : ℝ); linarith
  let r := (2*p+α)/2
  have hsr : 2*p < r := by dsimp [r]; linarith
  have hrα : r < α := by dsimp [r]; linarith
  have hr : 0 < r := by linarith
  have hβ : 0 < 1-2*p/r := by have := (div_lt_one hr).2 hsr; linarith
  obtain ⟨C,hC,hClog⟩ := rarity_log_power_bound (1-2*p/r) p hβ (by linarith)
  let M := 1+1/(α/(2*p)-1)
  let H := (1+1/(α/r-1))^(2*p/r)*C
  have hM : 0 < M := by have := (one_lt_div (by linarith : 0 < 2*p)).2 hsα; dsimp [M]; positivity
  have hH : 0 < H := by
    have h : 0 < 1+1/(α/r-1) := by have := (one_lt_div hr).2 hrα; positivity
    exact mul_pos (Real.rpow_pos_of_pos h _) hC
  let D := workCoefficient p*(5 : ℝ)^p*(M+H)
  have hD : 0 < D := by dsimp [D]; exact mul_pos (mul_pos (workCoefficient_pos p hp) (by positivity)) (add_pos hM hH)
  refine ⟨2*(1+D),by positivity,?_⟩
  intro a ρ ha ha' hρ hρ1 μ _ hm q hq j
  have hbase := population_work_moment_bound μ α a ρ p hsα ha ha' hρ hρ1 hp hm q j
  have hmoment := margin_inverse_integral μ α a (2*p) ha (by linarith) hsα hm
  have hweighted := log_weighted_inverse_bound μ α a (2*p) r ρ p C ha (by linarith)
    hsr hrα hρ hρ1 (by linarith) hm q hq (hClog ρ hρ hρ1)
  change _ ≤ M at hmoment
  change _ ≤ H at hweighted
  have hbound := mul_le_mul_of_nonneg_left (add_le_add hmoment hweighted)
    (show 0 ≤ workCoefficient p*(5*((j : ℝ)+1))^p by positivity [workCoefficient_pos p hp])
  have hJ : 1 ≤ (j : ℝ)+1 := by have := Nat.cast_nonneg (α := ℝ) j; linarith
  have hJpow : ((j : ℝ)+1)^p ≤ ((j : ℝ)+1)^2 := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hJ hp2
  have hJsq : 1 ≤ ((j : ℝ)+1)^2 := by nlinarith
  have hfactor : workCoefficient p*(5*((j : ℝ)+1))^p*(M+H) = D*((j : ℝ)+1)^p := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 5) (by linarith : 0 ≤ (j : ℝ)+1)]
    dsimp [D]
    ring
  rw [hfactor] at hbound
  have hstage : (∫ ω, (calibratedCost a ρ j ω : ℝ) ∂originalPopulationTapeLaw μ q) ≤
      cap (initialLevel a)*(1+D)*((j : ℝ)+1)^2 := by
    have h₁ := mul_le_mul_of_nonneg_left hbound (cap_pos (initialLevel a)).le
    have h₂ := mul_le_mul_of_nonneg_left hJpow (mul_pos (cap_pos (initialLevel a)) hD).le
    have h₃ := mul_le_mul_of_nonneg_left hJsq (cap_pos (initialLevel a)).le
    nlinarith only [hbase,h₁,h₂,h₃]
  have hcap := mul_le_mul_of_nonneg_right (initialLevel_bounds a ha ha').2
    (show 0 ≤ (1+D)*((j : ℝ)+1)^2 by positivity)
  calc
    _ ≤ _ := hstage
    _ ≤ (2/a^2)*((1+D)*((j : ℝ)+1)^2) := by nlinarith only [hcap]
    _ = _ := by ring

end ThresholdHC.RareAboveTwo
