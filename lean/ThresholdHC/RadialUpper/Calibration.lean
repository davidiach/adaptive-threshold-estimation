import ThresholdHC.RadialUpper.Moments

/-! The calibrated one-coin call `Y = c (A - F) - t` with `c = rho/(2 d0)`.

Its mean under `q_eta` is `(1+eta) rho/2 - t`, its second moment is at most
`(11/2) rho L` plus the squared mean, and its expected number of flips is below `29`,
uniformly in `eta`. The offset `t = 0` gives the uncentered call of the source and
`t = rho/2` the centered call used by the Poisson estimator. -/

noncomputable section
namespace ThresholdHC.RadialUpper
open MeasureTheory Set ThresholdHC.Tier6 ThresholdHC.ObservableSimulation
open ThresholdHC.ConfidenceTransfer (criticalPositiveLaw)

/-- The calibration scale `c = rho/(2 d0)`. -/
def radialScale (ρ b : ℝ) : ℝ := ρ / (2 * radialSlope b)

theorem calibrated_call {ρ b : ℝ} (hρ : 0 < ρ) (hρq : ρ ≤ 1/4) (h : RadialCalibrated ρ b)
    (t : ℝ) :
    ∃ (Y : EntropyTailExecution.FiniteCall) (N : ℕ) (U : ℝ),
      (∀ ω, Y.cost ω ≤ N) ∧ (∀ ω, |Y.value ω| ≤ U) ∧
      ∀ η : RadialIndex,
        (∫ ω, (Y.cost ω : ℝ) ∂originalPopulationTapeLaw criticalPositiveLaw (radialSign b η)) < 29 ∧
        (∫ ω, Y.value ω ∂originalPopulationTapeLaw criticalPositiveLaw (radialSign b η)) =
          (1+(η:ℝ))/2*ρ - t ∧
        (∫ ω, (Y.value ω)^2 ∂originalPopulationTapeLaw criticalPositiveLaw (radialSign b η)) ≤
          11/2*ρ*radialLogFactor ρ + ((1+(η:ℝ))/2*ρ - t)^2 := by
  obtain ⟨hb0, _, hρL, _, _⟩ := calibrated_facts hρ hρq h
  have hK := radialTop_two hb0
  have hN := (radialCap_bounds hb0).1
  have hD4 := radialSlope_ge hρ hρq h
  have hF8 := radialMiss_le hb0
  set F := radialMiss b with hF
  set D := radialSlope b with hD
  set c := radialScale ρ b with hc
  have hb2 : 0 < b^2 := by positivity
  have hD0 : 0 < D := by linarith
  have hcD : c * D = ρ/2 := by rw [hc, radialScale, ← hD]; field_simp
  have hc0 : 0 ≤ c := by rw [hc, radialScale, ← hD]; positivity
  refine ⟨walkCall (radialTop b) (radialCap b) hK hN (c*(1-F) - t) (-(c*F) - t), radialCap b,
    |c*(1-F) - t| + |-(c*F) - t|, walkCall_cost_le _ _ _ _ _ _, walkCall_value_le _ _ _ _ _ _,
    fun η => ?_⟩
  obtain ⟨hm1, hm2⟩ := walkCall_moments (originalPopulationTapeLaw criticalPositiveLaw (radialSign b η))
    (radialTop b) (radialCap b) hK hN (c*(1-F) - t) (-(c*F) - t)
  have hz := radial_hit_formula b η (radialTop b) (radialCap b)
  change _ = F + (1+(η:ℝ)) * D at hz
  rw [hz] at hm1 hm2
  have hη := η.2
  refine ⟨lt_of_le_of_lt (radial_cost_le hρ hρq h η) (by norm_num), ?_, ?_⟩
  · rw [hm1]
    linear_combination (1+(η:ℝ)) * hcD
  · rw [hm2]
    set z := F + (1+(η:ℝ)) * D with hzdef
    have hmean : -(c*F) - t + c*z = (1+(η:ℝ))/2*ρ - t := by
      rw [hzdef]; linear_combination (1+(η:ℝ)) * hcD
    have hid : (-(c*F) - t)^2 + ((c*(1-F) - t)^2 - (-(c*F) - t)^2) * z =
        c^2*z*(1-z) + (-(c*F) - t + c*z)^2 := by ring
    rw [hid, hmean]
    have hz1 : z ≤ 11/6*D := by rw [hzdef]; nlinarith [hη.1, hη.2]
    have h1 : c^2*z ≤ c^2*(11/6*D) := mul_le_mul_of_nonneg_left hz1 (sq_nonneg c)
    have h2 : c^2*(11/6*D) = 11/12*c*ρ := by linear_combination (11/6*c) * hcD
    have h3 : c ≤ ρ/(8*b^2) := by
      rw [hc, radialScale, ← hD]
      exact div_le_div_of_nonneg_left hρ.le (by positivity) (by linarith)
    have h4 : 11/12*c*ρ ≤ 11/12*(ρ/(8*b^2))*ρ := by
      have := mul_le_mul_of_nonneg_right h3 hρ.le
      linarith
    have h5 : 11/12*(ρ/(8*b^2))*ρ ≤ 11/2*ρ*radialLogFactor ρ := by
      rw [show 11/12*(ρ/(8*b^2))*ρ = 11*ρ^2/(96*b^2) by field_simp; ring,
        div_le_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hρL hρ.le]
    have h6 : c^2*z*(1-z) ≤ c^2*z := by nlinarith [sq_nonneg (c*z)]
    linarith

end ThresholdHC.RadialUpper
