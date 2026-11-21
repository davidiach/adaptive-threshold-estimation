import ThresholdHC.RadialUpper.Calibration
import ThresholdHC.KnownLawPlanner.PlannedEstimator
import ThresholdHC.StoppingProgram.ShiftEstimator
import ThresholdHC.RareAboveTwo.Nonvacuity

/-! Corollary `pop:radial-upper` on the known radial submodel.

If `rho/4 <= sqrt(160 rho L/B)` the constant output `rho/2` has error at most
`rho/4` and no work. Otherwise the centered calibrated call is repeated a
Poisson number of times with mean `B/29`, the sum is divided by `B/29`, and
`rho/2` is added back: the expected work is at most `B`, and the squared risk is at
most `(29/B)((11/2) rho L + rho^2/16) <= 160 rho L/B`. -/

noncomputable section
namespace ThresholdHC.RadialUpper
open MeasureTheory Set ThresholdHC.Tier6 ThresholdHC.ObservableSimulation
open ThresholdHC.ConfidenceTransfer (criticalPositiveLaw)
open scoped ENNReal NNReal

/-- The calibrated cutoff exists and is unique. -/
theorem radial_cutoff : RadialCutoffStatement := cutoff_exists_unique

/-- The one-coin constants: unbiased, variance at most `(11/2) rho L`, work below `29`. -/
theorem radial_call : RadialCallStatement := by
  intro ρ b hρ hρq h
  obtain ⟨Y, N, U, hc, hU, hY⟩ := calibrated_call hρ hρq h 0
  refine ⟨Y, N, U, hc, hU, fun η => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hY η
  refine ⟨h1, ?_, ?_⟩
  · rw [h2, radialSign_mean h η]; ring
  · rw [h2]; linarith

/-- Corollary `pop:radial-upper`, algorithmic form. -/
theorem radial_upper : RadialUpperStatement := by
  intro ρ b B hρ hρq h hB
  obtain ⟨_, _, _, _, hL1⟩ := calibrated_facts hρ hρq h
  set L := radialLogFactor ρ with hL
  set s := Real.sqrt (160*ρ*L/B) with hs
  by_cases hcase : ρ/4 ≤ s
  · refine ⟨Unit, inferInstance, RareAboveTwo.constantEstimator (ρ/2), fun η => ?_, fun η => ?_⟩
    · rw [RareAboveTwo.constant_work]
      exact bot_le
    · rw [RareAboveTwo.constant_risk, min_eq_left hcase, radialSign_mean h η]
      apply ENNReal.ofReal_le_ofReal
      have hη := η.2
      rw [abs_le]
      constructor <;> nlinarith [hη.1, hη.2]
  · obtain ⟨Y, N, U, hc, hU, hY⟩ := calibrated_call hρ hρq h (ρ/2)
    have hU0 : 0 ≤ U := (abs_nonneg _).trans (hU (fun _ => false))
    let r : Fin (0+1) → ℝ≥0 := fun _ => ⟨B/29, by positivity⟩
    have hr : ∀ i, 0 < (r i : ℝ) := fun _ => by change 0 < B/29; positivity
    let A := StoppingProgram.shiftEstimator
      (KnownLawPlanner.plannedEstimator r (fun _ : Fin (0+1) => Y)) (ρ/2)
    refine ⟨Fin (0+1) → ℕ, inferInstance, A, fun η => ?_, fun η => ?_⟩
    · rw [StoppingProgram.shiftEstimator_work]
      refine (KnownLawPlanner.planned_work_bound r (fun _ => Y) (K := fun _ => (N : ℝ))
        (fun _ ω => Nat.cast_le.mpr (hc ω)) criticalPositiveLaw (radialSign b η)
        (c := fun _ => 29) (fun _ => (hY η).1.le)).trans ?_
      apply ENNReal.ofReal_le_ofReal
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
      change B/29*29 ≤ B
      linarith
    · have hη := η.2
      obtain ⟨_, hmean, hsec⟩ := hY η
      have hv : (∫ ω, (Y.value ω)^2 ∂originalPopulationTapeLaw criticalPositiveLaw (radialSign b η)) ≤
          11/2*ρ*L + ρ^2/16 := by
        refine hsec.trans ?_
        have : ((1+(η:ℝ))/2*ρ - ρ/2)^2 ≤ ρ^2/16 := by
          nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hη.2)
            (by linarith [hη.1] : (0:ℝ) ≤ 1/2 + η)) (sq_nonneg ρ)]
        linarith
      have hsq : squaredRisk (experimentLaw criticalPositiveLaw A (radialSign b η)) (populationOutput A)
          (signMean criticalPositiveLaw (radialSign b η).val) ≤ ENNReal.ofReal (160*ρ*L/B) := by
        rw [StoppingProgram.shiftEstimator_squaredRisk]
        refine (KnownLawPlanner.planned_mse_bound r hr (fun _ => Y) (U := fun _ => U) (fun _ => hU0)
          (fun _ ω => by rw [Real.norm_eq_abs]; exact hU ω) criticalPositiveLaw (radialSign b η)
          (signMean criticalPositiveLaw (radialSign b η).val - ρ/2) (v := fun _ => 11/2*ρ*L + ρ^2/16)
          (fun _ => hv) (b := 0) le_rfl ?_).trans ?_
        · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
          rw [hmean, radialSign_mean h η]
          simp
        · apply ENNReal.ofReal_le_ofReal
          simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
          change (11/2*ρ*L + ρ^2/16)/(B/29) + 0^2 ≤ 160*ρ*L/B
          have h0 : (0:ℝ)^2 = 0 := by norm_num
          rw [div_div_eq_mul_div, h0, add_zero, div_le_div_iff_of_pos_right hB]
          nlinarith [mul_nonneg hρ.le (sub_nonneg.mpr hL1), mul_nonneg hρ.le (sub_nonneg.mpr hρq)]
      unfold rootMeanRisk
      have hx : 0 ≤ 160*ρ*L/B := by positivity
      calc _ ≤ ENNReal.ofReal (160*ρ*L/B) ^ (1/2 : ℝ) := ENNReal.rpow_le_rpow hsq (by norm_num)
        _ = ENNReal.ofReal s := by
          rw [hs, ← ofReal_square_rpow_half (Real.sqrt (160*ρ*L/B)) (Real.sqrt_nonneg _),
            Real.sq_sqrt hx]
        _ = ENNReal.ofReal (min (ρ/4) s) := by rw [min_eq_right (le_of_not_ge hcase)]

/-- Corollary `pop:radial-upper`, minimax form. -/
theorem radial_minimax_upper : RadialMinimaxUpperStatement := by
  intro ρ b B hρ hρq h hB
  obtain ⟨R, hR, A, hw, hr⟩ := radial_upper ρ b B hρ hρq h hB
  refine (sInf_le ?_).trans (iSup_le hr)
  exact ⟨R, hR, A, hw, rfl⟩

end ThresholdHC.RadialUpper
