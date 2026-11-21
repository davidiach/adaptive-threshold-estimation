import ThresholdHC.PsiNull.Population
import ThresholdHC.RMSLocalization.CommonPair
import ThresholdHC.RareAboveTwo.Psi

/-! Proposition prop:psi-null and its corollary eq:psi-budget-lower.

`psi_null` takes the supremum of `psi_objective_bound` over feasible allocations,
so `Ψ(h) ≤ 4b + h √(192 V W₀)`, and squares. `psi_budget_lower` applies it at
`h = 1/√B` and `b = Ψ/64`, where `Ψ - 4b = 15Ψ/16` and
`J = (15Ψ/16)² B/192`, so `min{b, √(J/B)} = Ψ/64`; the common-pair transfer
`minimax_rms_of_obstruction` then gives `R_{μ,ρ}(B) ≥ Ψ/(64·128) = Ψ/8192`. The
case `Ψ = 0` is trivial. -/
noncomputable section
namespace ThresholdHC.PsiNull
open MeasureTheory
open scoped ENNReal
open ThresholdHC.Tier6 ThresholdHC.CriticalEntropy ThresholdHC.ConfidenceLocalization
  ThresholdHC.ObservableSimulation ThresholdHC.RareAboveTwo

/-- Proposition prop:psi-null (eq:psi-null-product), pointwise in `h > 0`. -/
theorem psi_null : PsiNullStatement := by
  intro μ _ ρ b h hρ hρ4 hb hbρ hh R _ ν _ A m hcap hCex V hV hvar hbias
  obtain ⟨C, hC⟩ := hCex
  set W₀ := (populationExpectedWork μ ν (gapParameter false) (gapParameter true)
    (fun _ => 0) A).toReal with hW₀def
  have hW₀ : 0 ≤ W₀ := ENNReal.toReal_nonneg
  have hK : 0 ≤ 4*b + h * Real.sqrt (192 * V * W₀) := by positivity
  have hpsi : rarePsi μ ρ h ≤ ENNReal.ofReal (4*b + h * Real.sqrt (192 * V * W₀)) :=
    iSup₂_le fun v hv => ENNReal.ofReal_le_ofReal
      (psi_objective_bound μ ν A m hcap hC hρ hρ4 hbρ hh.le hV hvar hbias hv)
  have hΨ := ENNReal.toReal_le_of_le_ofReal hK hpsi
  have hmax : max ((rarePsi μ ρ h).toReal - 4*b) 0 ≤ h * Real.sqrt (192 * V * W₀) :=
    max_le (by linarith) (by positivity)
  have hsq : (max ((rarePsi μ ρ h).toReal - 4*b) 0)^2 ≤ h^2 * (192 * V * W₀) :=
    calc
      _ ≤ (h * Real.sqrt (192 * V * W₀))^2 := pow_le_pow_left₀ (le_max_right _ _) hmax 2
      _ = h^2 * (192 * V * W₀) := by rw [mul_pow, Real.sq_sqrt (by positivity)]
  rw [div_le_iff₀ (by positivity)]
  calc
    _ ≤ h^2 * (192 * V * W₀) := hsq
    _ = V * W₀ * (192 * h^2) := by ring

/-- eq:psi-budget-lower: `R_{μ,ρ}(B) ≥ Ψ_{μ,ρ}(B^{-1/2})/8192`. -/
theorem psi_budget_lower : PsiBudgetLowerStatement := by
  intro μ _ ρ B hρ hρ4 hB
  set h := 1 / Real.sqrt B with hh
  have hs : 0 < Real.sqrt B := Real.sqrt_pos.mpr hB
  have hpos : 0 < h := by positivity
  have hle : rarePsi μ ρ h ≤ ENNReal.ofReal ρ :=
    iSup₂_le fun v hv => ENNReal.ofReal_le_ofReal (rareObjective_le_rarity μ ρ h hpos.le v hv)
  have hfin : rarePsi μ ρ h ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  set Ψ := (rarePsi μ ρ h).toReal with hΨ
  have hΨρ : Ψ ≤ ρ := ENNReal.toReal_le_of_le_ofReal hρ.le hle
  have hΨ0 : 0 ≤ Ψ := ENNReal.toReal_nonneg
  have heq : rarePsi μ ρ h = ENNReal.ofReal Ψ := (ENNReal.ofReal_toReal hfin).symm
  rcases hΨ0.eq_or_lt with h0 | h0
  · rw [heq, ← h0]; simp
  have hb : 0 < Ψ/64 := by positivity
  have hobs : NullVarianceObstruction μ (gapParameter false) (gapParameter true) ρ (Ψ/64)
      ((max (Ψ - 4*(Ψ/64)) 0)^2 / (192*h^2)) :=
    psi_null μ ρ (Ψ/64) h hρ hρ4 hb.le (by linarith) hpos
  have hh2 : h^2 = 1/B := by rw [hh, div_pow, Real.sq_sqrt hB.le]; ring
  have hJ : (max (Ψ - 4*(Ψ/64)) 0)^2 / (192*h^2) = (15*Ψ/16)^2 * B / 192 := by
    rw [max_eq_left (by linarith), hh2]; field_simp; ring
  rw [hJ] at hobs
  have hJpos : 0 < (15*Ψ/16)^2 * B / 192 := by positivity
  have hm := ThresholdHC.RMSLocalization.minimax_rms_of_obstruction μ hρ hρ4 hb hJpos hB hobs
  have hmin : min (Ψ/64) (Real.sqrt ((15*Ψ/16)^2 * B / 192 / B)) = Ψ/64 := by
    apply min_eq_left
    apply Real.le_sqrt_of_sq_le
    rw [show (15*Ψ/16)^2 * B / 192 / B = (15*Ψ/16)^2/192 by field_simp]
    nlinarith
  rw [hmin] at hm
  rw [heq, ← ENNReal.ofReal_mul (by norm_num)]
  convert hm using 2
  ring

end ThresholdHC.PsiNull
