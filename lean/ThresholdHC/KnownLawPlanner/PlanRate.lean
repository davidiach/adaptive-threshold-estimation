import ThresholdHC.KnownLawPlanner.PlanCertificate

/-! The rate of a plan computed from the exact design integrals.

With the exact resolved error as its envelope, the carried cap search returns
the least admissible cap of each level, so the plan's level price is at most
the level work certificate of the upper theorem, and the multilevel sum bound
of that theorem applies:

  `Σ_{l ≤ J} √(17 δ_l k_l) ≤ 28000 (√(ρ Γ) + H)`.

The planner stops at the first level `J` with `δ_J/16` below the target
`max{128 z, ρ/(16 (1 + √B))}`. When `2048 z ≤ ρ` that level is admissible and
`δ_J < 2048 z + ρ/(1 + √B)`. With weights within a factor `θ` of the optimal
ones, the certified root-mean-square risk is at most

  `2048 z + ρ/(1 + √B) + √θ · 28000 (√(ρ Γ) + H)/√B`.

`Γ` is the cost entropy of the band costs of the core, `H = ∫ d⁻¹ dτ` and `z`
the unresolved mass. -/

noncomputable section
open MeasureTheory Set Real Filter
open scoped NNReal ENNReal BigOperators Topology

namespace ThresholdHC.KnownLawPlanner
open ThresholdHC.Tier6 ThresholdHC.EntropyTailQuantile ThresholdHC.EntropyTailUpper
open ThresholdHC.EntropyTailAssembly ThresholdHC.ObservableSimulation ThresholdHC.RareAboveTwo
open ThresholdHC.EntropyTailExecution

/-- With the exact error envelope, the carried search returns the least
admissible cap of each level. -/
theorem searchCaps_exact (ν : Measure Gap) [IsFiniteMeasure ν] {ρ : ℝ} (hρ : 0 < ρ) (l : ℕ) :
    searchCaps (eta ν) (eta_vanishes ν) hρ l =
      errorCapExponent ν (levelAccuracy ρ l) (levelAccuracy_pos hρ l) := by
  induction l with
  | zero =>
    apply le_antisymm
    · exact Nat.find_min' _ (errorCapExponent_spec ν (levelAccuracy_pos hρ 0))
    · exact Nat.find_min' _ (searchCap_spec (eta ν) (eta_vanishes ν) _ _ 1)
  | succ l ih =>
    have hs := errorCapExponent_spec ν (levelAccuracy_pos hρ (l+1))
    have hδ : levelAccuracy ρ (l+1)/8 ≤ levelAccuracy ρ l/8 := by
      rw [levelAccuracy_succ]
      linarith [levelAccuracy_pos hρ l]
    have hle : errorCapExponent ν (levelAccuracy ρ l) (levelAccuracy_pos hρ l) ≤
        errorCapExponent ν (levelAccuracy ρ (l+1)) (levelAccuracy_pos hρ (l+1)) :=
      Nat.find_min' _ ⟨hs.1, hs.2.trans hδ⟩
    have hsp := searchCap_spec (eta ν) (eta_vanishes ν) (levelAccuracy ρ (l+1)/8)
      (div_pos (levelAccuracy_pos hρ (l+1)) (by norm_num))
      (searchCaps (eta ν) (eta_vanishes ν) hρ l)
    apply le_antisymm
    · exact Nat.find_min' _ ⟨by rw [ih]; exact hle, hs.2⟩
    · refine Nat.find_min' _ ⟨le_trans ?_ hsp.1, hsp.2⟩
      rw [ih]
      exact (errorCapExponent_spec ν (levelAccuracy_pos hρ l)).1

/-- The price of the exact plan at level `l` is at most the level work
certificate of the upper theorem. -/
theorem exact_price_le (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] (N : ℕ)
    {ρ : ℝ} (hρ : 0 < ρ) (l : ℕ) :
    (SplitEnclosure.exact σ τ ζ N).price ρ l
        (searchCaps (eta (σ+τ)) (eta_vanishes (σ+τ)) hρ l) ≤
      levelWorkCertificate σ τ ρ (costEntropy (fun j : Fin N => bandCost σ j.val))
        (ζ.real univ) hρ l := by
  rw [searchCaps_exact]
  exact min_le_right _ _

/-- The multilevel sum of the exact plan: `Σ_{l ≤ J} √(17 δ_l k_l)` is at most
`28000 (√(ρ Γ) + H)`. -/
theorem exact_plan_spread (σ τ ζ : Measure Gap)
    [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)]
    {t ρ : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) (hN : bandEdge N < t)
    (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4) (J : ℕ)
    (hzJ : ζ.real univ ≤ levelAccuracy ρ J/8) :
    allocationCertificate (fun i : Fin (J+1) => 17*levelAccuracy ρ i.val)
        (planCost (SplitEnclosure.exact σ τ ζ N) ρ
          (searchCaps (eta (σ+τ)) (eta_vanishes (σ+τ)) hρ) J) ≤
      28000*(sqrt (ρ*costEntropy (fun j : Fin N => bandCost σ j.val)) +
        ∫ d : Gap, (d:ℝ)⁻¹ ∂τ) := by
  have hz128 : ζ.real univ ≤ ρ/128 := by
    have h := levelAccuracy_le_first hρ.le J
    linarith
  have hm := resolved_mass_large σ τ ζ hρ1 hz128
  have hAΓ : (∫ d : Gap, (d:ℝ)⁻¹^2 ∂σ) ≤ costEntropy (fun j : Fin N => bandCost σ j.val) := by
    rw [inverseSquare_eq_band_total σ hs hN]
    exact costTotal_le_costEntropy (fun j => bandCost_nonneg σ j.val)
  have h := multilevel_budget_certificate σ τ (inverseSquare_integrable_of_support σ ht hs) hτ
    hρ (costEntropy_nonneg (fun j : Fin N => bandCost_nonneg σ j.val))
    (measureReal_nonneg) hAΓ hm J hzJ
  refine le_trans ?_ h
  rw [← Fin.sum_univ_eq_sum_range (fun l : ℕ => sqrt (17*levelAccuracy ρ l*adjacentCost
    (levelWorkCertificate σ τ ρ (costEntropy (fun j : Fin N => bandCost σ j.val))
      (ζ.real univ) hρ) l)) (J+1)]
  unfold allocationCertificate
  refine Finset.sum_le_sum fun i _ => sqrt_le_sqrt (mul_le_mul_of_nonneg_left ?_
    (mul_nonneg (by norm_num) (levelAccuracy_pos hρ i.val).le))
  unfold planCost adjacentCost
  split_ifs
  · exact exact_price_le σ τ ζ N hρ _
  · exact add_le_add (exact_price_le σ τ ζ N hρ _) (exact_price_le σ τ ζ N hρ _)

/-- The target of the terminal rule: `max{128 z, ρ/(16 (1 + √B))}`. -/
def planTarget (ρ B z : ℝ) : ℝ := max (128*z) (ρ/(16*(1+sqrt B)))

theorem planTarget_pos {ρ : ℝ} (hρ : 0 < ρ) (B z : ℝ) : 0 < planTarget ρ B z :=
  lt_of_lt_of_le (div_pos hρ (mul_pos (by norm_num) (by positivity))) (le_max_right _ _)

theorem exists_planTerminal {ρ : ℝ} (hρ : 0 < ρ) (B z : ℝ) :
    ∃ l : ℕ, levelAccuracy ρ l/16 < planTarget ρ B z := by
  have hlim : Tendsto (fun l => levelAccuracy ρ l/16) atTop (𝓝 0) := by
    simpa using (levelAccuracy_tendsto ρ).div_const 16
  exact (hlim.eventually (gt_mem_nhds (planTarget_pos hρ B z))).exists

/-- The terminal level of the planner: the first level `l` with `δ_l/16`
below the target. -/
def planTerminal {ρ : ℝ} (hρ : 0 < ρ) (B z : ℝ) : ℕ := Nat.find (exists_planTerminal hρ B z)

theorem planTerminal_spec {ρ : ℝ} (hρ : 0 < ρ) (B z : ℝ) :
    levelAccuracy ρ (planTerminal hρ B z)/16 < planTarget ρ B z :=
  Nat.find_spec (exists_planTerminal hρ B z)

/-- Outside the constant fallback, `2048 z ≤ ρ`, the terminal accuracy is at
least the target. -/
theorem planTarget_le_terminal {ρ : ℝ} (hρ : 0 < ρ) (B : ℝ) {z : ℝ} (hz : 2048*z ≤ ρ) :
    planTarget ρ B z ≤ levelAccuracy ρ (planTerminal hρ B z) := by
  rcases Nat.eq_zero_or_pos (planTerminal hρ B z) with h0 | hpos
  · rw [h0, levelAccuracy_zero]
    refine max_le (by linarith) ?_
    rw [div_le_div_iff₀ (mul_pos (by norm_num) (by positivity)) (by norm_num)]
    nlinarith [sqrt_nonneg B]
  · have hmin := Nat.find_min (exists_planTerminal hρ B z)
      (show planTerminal hρ B z - 1 < planTerminal hρ B z by omega)
    have he : planTerminal hρ B z = (planTerminal hρ B z - 1) + 1 := by omega
    rw [he, levelAccuracy_succ]
    exact not_lt.mp hmin

/-- The terminal level covers the unresolved mass: `z ≤ δ_J/128`. -/
theorem planTerminal_unresolved {ρ : ℝ} (hρ : 0 < ρ) (B : ℝ) {z : ℝ} (hz : 2048*z ≤ ρ) :
    z ≤ levelAccuracy ρ (planTerminal hρ B z)/128 := by
  have h := (le_max_left (128*z) (ρ/(16*(1+sqrt B)))).trans (planTarget_le_terminal hρ B hz)
  linarith

/-- The terminal accuracy: `δ_J < 2048 z + ρ/(1 + √B)`. -/
theorem planTerminal_accuracy_lt {ρ : ℝ} (hρ : 0 < ρ) (B : ℝ) {z : ℝ} (hz0 : 0 ≤ z) :
    levelAccuracy ρ (planTerminal hρ B z) < 2048*z + ρ/(1+sqrt B) := by
  have h := planTerminal_spec hρ B z
  have hpos : (0:ℝ) < 1 + sqrt B := by positivity
  have he : ρ/(16*(1+sqrt B)) = ρ/(1+sqrt B)/16 := by
    field_simp
  have hmax : planTarget ρ B z ≤ 128*z + ρ/(1+sqrt B)/16 := by
    unfold planTarget
    rw [he]
    exact max_le (by linarith [div_nonneg hρ.le hpos.le])
      (by linarith)
  linarith

/-- The certified risk of the exact plan in the design integrals. With
weights within a factor `θ` of the optimal ones, the square root of the
certificate is at most `δ_J + √θ · 28000 (√(ρ Γ) + H)/√B`. -/
theorem exact_plan_rms_le (σ τ ζ : Measure Gap)
    [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)]
    {t ρ B θ : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ)) (hN : bandEdge N < t)
    (hτ : Integrable (fun d : Gap => (d:ℝ)⁻¹) τ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4) (hB : 0 < B)
    (hθ : 0 ≤ θ) (J : ℕ) (hzJ : ζ.real univ ≤ levelAccuracy ρ J/8) (w : Fin (J+1) → ℝ)
    (hlow : ∀ i, sqrt (17*levelAccuracy ρ i.val /
      planCost (SplitEnclosure.exact σ τ ζ N) ρ
        (searchCaps (eta (σ+τ)) (eta_vanishes (σ+τ)) hρ) J i) ≤ w i)
    (hup : ∀ i, w i ≤ θ * sqrt (17*levelAccuracy ρ i.val /
      planCost (SplitEnclosure.exact σ τ ζ N) ρ
        (searchCaps (eta (σ+τ)) (eta_vanishes (σ+τ)) hρ) J i)) :
    sqrt (planCertificate ρ (planRates B (planCost (SplitEnclosure.exact σ τ ζ N) ρ
        (searchCaps (eta (σ+τ)) (eta_vanishes (σ+τ)) hρ) J) w)) ≤
      levelAccuracy ρ J + sqrt θ * (28000*(sqrt (ρ*costEntropy
        (fun j : Fin N => bandCost σ j.val)) + ∫ d : Gap, (d:ℝ)⁻¹ ∂τ)) / sqrt B := by
  have hz : ζ.real univ ≤ ρ := by
    have h := levelAccuracy_le_first hρ.le J
    linarith
  have hk := planCost_pos σ τ ζ ht hs hN hτ hρ hρ1 hz (SplitEnclosure.exact σ τ ζ N)
    (searchCaps (eta (σ+τ)) (eta_vanishes (σ+τ)) hρ) J
  have hcert := planCertificate_le_of_weights hρ hB hk hlow hup
  have hspread := exact_plan_spread σ τ ζ ht hs hN hτ hρ hρ1 J hzJ
  have hS0 : 0 ≤ allocationCertificate (fun i : Fin (J+1) => 17*levelAccuracy ρ i.val)
      (planCost (SplitEnclosure.exact σ τ ζ N) ρ
        (searchCaps (eta (σ+τ)) (eta_vanishes (σ+τ)) hρ) J) :=
    Finset.sum_nonneg fun i _ => sqrt_nonneg _
  have hX0 := hS0.trans hspread
  have hδ := (levelAccuracy_pos hρ J).le
  have hsB : 0 < sqrt B := sqrt_pos.mpr hB
  refine sqrt_le_iff.mpr ⟨by positivity, hcert.trans ?_⟩
  have hsq := pow_le_pow_left₀ hS0 hspread 2
  have hterm : θ * (allocationCertificate (fun i : Fin (J+1) => 17*levelAccuracy ρ i.val)
      (planCost (SplitEnclosure.exact σ τ ζ N) ρ
        (searchCaps (eta (σ+τ)) (eta_vanishes (σ+τ)) hρ) J)) ^ 2 / B ≤
      (sqrt θ * (28000*(sqrt (ρ*costEntropy (fun j : Fin N => bandCost σ j.val)) +
        ∫ d : Gap, (d:ℝ)⁻¹ ∂τ)) / sqrt B) ^ 2 := by
    rw [div_pow, mul_pow, sq_sqrt hθ, sq_sqrt hB.le]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hθ) hB.le
  nlinarith [mul_nonneg hδ (div_nonneg (mul_nonneg (sqrt_nonneg θ) hX0) hsB.le)]

end ThresholdHC.KnownLawPlanner
