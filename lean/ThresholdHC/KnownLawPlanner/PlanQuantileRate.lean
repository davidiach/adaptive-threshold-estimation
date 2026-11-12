import ThresholdHC.KnownLawPlanner.PlanRate
import ThresholdHC.QuantileSelection.Full
import ThresholdHC.EntropyTail.Objective

/-! The exact plan of the quantile split attains the oracle rate.

Let the plan use the quantile split of its gap law `μ`: the core `σ` is the
quantile core at rarity `ρ`, and the quantile part is divided at the budget
scale `h = B^{-1/2}` into the resolved tail `τ`, on gaps at least `h`, and
the unresolved part `ζ`, on gaps at most `h`. Then

  `z + h H + h √(ρ Γ_σ)`

is the uncapped quantile value, which is at most `(8/5) K_{μ,ρ}(B)` when it
is below `ρ`. With `ρ/(1 + √B) ≤ K`, the certified risk of the exact plan
satisfies

  `min{ρ/2, √certificate} ≤ (1 + (8/5) max{2048, 28000 √θ}) K_{μ,ρ}(B)`,

for weights within a factor `θ` of the optimal ones. When `2048 z > ρ` the
planner returns the constant `ρ/2`, which obeys the same bound. -/

noncomputable section
open MeasureTheory Set Real
open scoped NNReal ENNReal BigOperators

namespace ThresholdHC.KnownLawPlanner
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTailQuantile ThresholdHC.EntropyTailUpper
open ThresholdHC.EntropyTailAssembly ThresholdHC.EntropyTailExecution

/-- The elementary floor of the selection functional at a general budget:
`ρ/(1 + √B) ≤ K_{μ,ρ}(B)`. -/
theorem selection_floor (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ B : ℝ} (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (hB : 0 < B) :
    ENNReal.ofReal (ρ/(1+sqrt B)) ≤ EntropyTail.selection μ ρ B := by
  have hs : 0 < sqrt B := sqrt_pos.mpr hB
  have hsρ : ρ ≤ sqrt ρ := by
    have h1 : sqrt ρ ≤ 1 := by
      rw [← sqrt_one]
      exact sqrt_le_sqrt hρ1
    nlinarith [mul_self_sqrt hρ.le, sqrt_nonneg ρ]
  have hdiv : ρ/(1+sqrt B) ≤ ρ * (1/sqrt B) := by
    rw [mul_one_div]
    exact div_le_div_of_nonneg_left hρ.le hs (by linarith)
  have hself : ρ/(1+sqrt B) ≤ ρ := div_le_self hρ.le (by linarith)
  have hinv : 0 < 1/sqrt B := by positivity
  unfold EntropyTail.selection
  refine le_min (ENNReal.ofReal_le_ofReal hself)
    ((ENNReal.ofReal_le_ofReal ?_).trans (EntropyTail.iInf_objective_lower μ hρ.le B))
  refine le_min ?_ (le_min (by linarith) ?_)
  · nlinarith [mul_le_mul_of_nonneg_right hsρ hinv.le]
  · nlinarith [mul_le_mul_of_nonneg_right hρ1 hinv.le]

/-- The oracle side of the quantile split in real numbers. The selection
functional is `ofReal K` for a real `K` with `ρ/(1 + √B) ≤ K`, and the capped
quantile value `min{ρ, z + h H + h √(ρ Γ_σ)}` is at most `(8/5) K`. -/
theorem quantile_split_comparison (σ τ ζ : Measure Gap)
    [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)]
    {ρ B : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B)
    (hcore : σ = quantileCore (σ+τ+ζ) ρ) (htail : τ+ζ = quantileTail (σ+τ+ζ) ρ)
    (hτs : ∀ᵐ d : Gap ∂τ, budgetScale B ≤ (d:ℝ)) (hζs : ∀ᵐ d : Gap ∂ζ, (d:ℝ) ≤ budgetScale B) :
    ∃ K : ℝ, 0 ≤ K ∧ EntropyTail.selection (σ+τ+ζ) ρ B = ENNReal.ofReal K ∧
      ρ/(1+sqrt B) ≤ K ∧
      min ρ (ζ.real univ + budgetScale B * (∫ d : Gap, (d:ℝ)⁻¹ ∂τ) +
        budgetScale B * sqrt (ρ * (measureCostEntropy σ).toReal)) ≤ 8/5 * K := by
  have hρ1 : ρ ≤ 1 := by linarith
  have hh := budgetScale_pos hB
  have ht := (quantileThreshold_properties (σ+τ+ζ) hρ hρ1).1
  have hs : ∀ᵐ d : Gap ∂σ, quantileThreshold (σ+τ+ζ) ρ ≤ (d:ℝ) := by
    have h := quantileCore_support (σ+τ+ζ) ρ
    rw [← hcore] at h
    exact h
  have hG : measureCostEntropy σ ≠ ⊤ := (measureCostEntropy_lt_top_of_support σ ht hs).ne
  have htm : tailModulus (τ+ζ) (budgetScale B) =
      budgetScale B * (∫ d : Gap, (d:ℝ)⁻¹ ∂τ) + ζ.real univ := by
    rw [tailModulus_add τ ζ hh.le, tailModulus_eq_inverseCost τ hτs, tailModulus_eq_mass ζ hζs]
  have hKtop : EntropyTail.selection (σ+τ+ζ) ρ B ≠ ⊤ :=
    ((EntropyTail.selection_le_rho (σ+τ+ζ) ρ B).trans_lt ENNReal.ofReal_lt_top).ne
  have hK : EntropyTail.selection (σ+τ+ζ) ρ B =
      ENNReal.ofReal (EntropyTail.selection (σ+τ+ζ) ρ B).toReal :=
    (ENNReal.ofReal_toReal hKtop).symm
  have hK0 : 0 ≤ (EntropyTail.selection (σ+τ+ζ) ρ B).toReal := ENNReal.toReal_nonneg
  refine ⟨(EntropyTail.selection (σ+τ+ζ) ρ B).toReal, hK0, hK, ?_, ?_⟩
  · have hf := selection_floor (σ+τ+ζ) hρ hρ1 hB
    rw [hK] at hf
    exact (ENNReal.ofReal_le_ofReal_iff hK0).mp hf
  · have h85 := (QuantileSelection.locked_selection_comparison (σ+τ+ζ) hρ hρ4 hB).2
    have hQ : closedQuantileValue (σ+τ+ζ) ρ B =
        ENNReal.ofReal (min ρ (ζ.real univ + budgetScale B * (∫ d : Gap, (d:ℝ)⁻¹ ∂τ) +
          budgetScale B * sqrt (ρ * (measureCostEntropy σ).toReal))) := by
      unfold closedQuantileValue
      rw [← htail, ← hcore, htm, entropy_root_eq_ofReal hG hρ.le hh.le,
        ← ENNReal.ofReal_add (add_nonneg (mul_nonneg hh.le
          (integral_nonneg fun d => inv_nonneg.mpr d.property.1.le)) measureReal_nonneg)
          (mul_nonneg hh.le (sqrt_nonneg _)),
        add_comm (budgetScale B * ∫ d : Gap, (d:ℝ)⁻¹ ∂τ) (ζ.real univ)]
      exact (ENNReal.ofReal_mono.map_min).symm
    rw [hQ, hK, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 8/5)] at h85
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h85

/-- The rate of the exact plan of the quantile split. Outside the constant
fallback, the smaller of `ρ/2` and the certified risk of the plan is at most
`(1 + (8/5) max{2048, 28000 √θ}) K_{μ,ρ}(B)`. -/
theorem quantile_plan_rate (σ τ ζ : Measure Gap)
    [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)]
    {ρ B θ : ℝ} {N : ℕ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) (hθ : 0 ≤ θ)
    (hcore : σ = quantileCore (σ+τ+ζ) ρ) (htail : τ+ζ = quantileTail (σ+τ+ζ) ρ)
    (hτs : ∀ᵐ d : Gap ∂τ, budgetScale B ≤ (d:ℝ)) (hζs : ∀ᵐ d : Gap ∂ζ, (d:ℝ) ≤ budgetScale B)
    (hN : bandEdge N < quantileThreshold (σ+τ+ζ) ρ) (hz : 2048 * ζ.real univ ≤ ρ)
    (w : Fin (planTerminal hρ B (ζ.real univ) + 1) → ℝ)
    (hlow : ∀ i, sqrt (17*levelAccuracy ρ i.val /
      planCost (SplitEnclosure.exact σ τ ζ N) ρ
        (searchCaps (eta (σ+τ)) (eta_vanishes (σ+τ)) hρ)
        (planTerminal hρ B (ζ.real univ)) i) ≤ w i)
    (hup : ∀ i, w i ≤ θ * sqrt (17*levelAccuracy ρ i.val /
      planCost (SplitEnclosure.exact σ τ ζ N) ρ
        (searchCaps (eta (σ+τ)) (eta_vanishes (σ+τ)) hρ)
        (planTerminal hρ B (ζ.real univ)) i)) :
    ENNReal.ofReal (min (ρ/2) (sqrt (planCertificate ρ (planRates B
        (planCost (SplitEnclosure.exact σ τ ζ N) ρ
          (searchCaps (eta (σ+τ)) (eta_vanishes (σ+τ)) hρ)
          (planTerminal hρ B (ζ.real univ))) w)))) ≤
      ENNReal.ofReal (1 + 8/5 * max 2048 (28000 * sqrt θ)) *
        EntropyTail.selection (σ+τ+ζ) ρ B := by
  have hρ1 : ρ ≤ 1 := by linarith
  have hh := budgetScale_pos hB
  have ht := (quantileThreshold_properties (σ+τ+ζ) hρ hρ1).1
  have hs : ∀ᵐ d : Gap ∂σ, quantileThreshold (σ+τ+ζ) ρ ≤ (d:ℝ) := by
    have h := quantileCore_support (σ+τ+ζ) ρ
    rw [← hcore] at h
    exact h
  have hτ := inverse_integrable_of_support τ hh hτs
  have hz0 : 0 ≤ ζ.real univ := measureReal_nonneg
  have hH0 : 0 ≤ ∫ d : Gap, (d:ℝ)⁻¹ ∂τ := integral_nonneg fun d => inv_nonneg.mpr d.property.1.le
  have hG : measureCostEntropy σ ≠ ⊤ := (measureCostEntropy_lt_top_of_support σ ht hs).ne
  have hΓ0 := costEntropy_nonneg (fun j : Fin N => bandCost_nonneg σ j.val)
  have hΓN : costEntropy (fun j : Fin N => bandCost σ j.val) ≤ (measureCostEntropy σ).toReal := by
    rw [← ENNReal.toReal_ofReal hΓ0]
    exact ENNReal.toReal_mono hG (le_iSup (fun k : ℕ => ENNReal.ofReal
      (costEntropy (fun j : Fin k => bandCost σ j.val))) N)
  have hzJ : ζ.real univ ≤ levelAccuracy ρ (planTerminal hρ B (ζ.real univ))/8 := by
    have h := planTerminal_unresolved hρ B hz
    linarith [levelAccuracy_pos hρ (planTerminal hρ B (ζ.real univ))]
  have hrms := exact_plan_rms_le σ τ ζ ht hs hN hτ hρ (by linarith) hB hθ
    (planTerminal hρ B (ζ.real univ)) hzJ w hlow hup
  have hδ := planTerminal_accuracy_lt hρ B hz0
  obtain ⟨K, hK0, hK, hfloor, hQK⟩ :=
    quantile_split_comparison σ τ ζ hρ hρ4 hB hcore htail hτs hζs
  have hm0 : (0:ℝ) ≤ max 2048 (28000 * sqrt θ) := le_trans (by norm_num) (le_max_left _ _)
  rw [hK, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  -- The certified risk against the uncapped quantile value.
  have hscale : (1:ℝ)/sqrt B = budgetScale B := by
    unfold budgetScale
    rw [one_div]
  have hroot : sqrt (ρ * costEntropy (fun j : Fin N => bandCost σ j.val)) ≤
      sqrt (ρ * (measureCostEntropy σ).toReal) :=
    sqrt_le_sqrt (mul_le_mul_of_nonneg_left hΓN hρ.le)
  have hcert : sqrt (planCertificate ρ (planRates B
      (planCost (SplitEnclosure.exact σ τ ζ N) ρ
        (searchCaps (eta (σ+τ)) (eta_vanishes (σ+τ)) hρ)
        (planTerminal hρ B (ζ.real univ))) w)) ≤
      K + max 2048 (28000 * sqrt θ) * (ζ.real univ + budgetScale B * (∫ d : Gap, (d:ℝ)⁻¹ ∂τ) +
        budgetScale B * sqrt (ρ * (measureCostEntropy σ).toReal)) := by
    have hX : sqrt θ * (28000*(sqrt (ρ*costEntropy (fun j : Fin N => bandCost σ j.val)) +
        ∫ d : Gap, (d:ℝ)⁻¹ ∂τ)) / sqrt B =
        28000 * sqrt θ * (budgetScale B * sqrt (ρ*costEntropy
          (fun j : Fin N => bandCost σ j.val)) + budgetScale B * ∫ d : Gap, (d:ℝ)⁻¹ ∂τ) := by
      rw [← hscale]
      ring
    rw [hX] at hrms
    have h1 : 28000 * sqrt θ * (budgetScale B * sqrt (ρ*costEntropy
          (fun j : Fin N => bandCost σ j.val)) + budgetScale B * ∫ d : Gap, (d:ℝ)⁻¹ ∂τ) ≤
        max 2048 (28000 * sqrt θ) * (budgetScale B * sqrt (ρ * (measureCostEntropy σ).toReal) +
          budgetScale B * ∫ d : Gap, (d:ℝ)⁻¹ ∂τ) := by
      refine mul_le_mul (le_max_right _ _) ?_ (by positivity) hm0
      exact add_le_add (mul_le_mul_of_nonneg_left hroot hh.le) le_rfl
    have h2 : 2048 * ζ.real univ ≤ max 2048 (28000 * sqrt θ) * ζ.real univ :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hz0
    linarith
  rcases le_total (ζ.real univ + budgetScale B * (∫ d : Gap, (d:ℝ)⁻¹ ∂τ) +
      budgetScale B * sqrt (ρ * (measureCostEntropy σ).toReal)) ρ with hcase | hcase
  · rw [min_eq_right hcase] at hQK
    refine (min_le_right _ _).trans (hcert.trans ?_)
    nlinarith [mul_le_mul_of_nonneg_left hQK hm0]
  · rw [min_eq_left hcase] at hQK
    refine (min_le_left _ _).trans ?_
    nlinarith [mul_nonneg hm0 hK0]

/-- The constant fallback obeys the same bound. When `2048 z > ρ` the planner
returns the constant `ρ/2`, and `ρ/2 ≤ (1 + (8/5) max{2048, 28000 √θ}) K`. -/
theorem quantile_fallback_rate (σ τ ζ : Measure Gap)
    [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)]
    {ρ B : ℝ} (θ : ℝ) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B)
    (hcore : σ = quantileCore (σ+τ+ζ) ρ) (htail : τ+ζ = quantileTail (σ+τ+ζ) ρ)
    (hτs : ∀ᵐ d : Gap ∂τ, budgetScale B ≤ (d:ℝ)) (hζs : ∀ᵐ d : Gap ∂ζ, (d:ℝ) ≤ budgetScale B)
    (hz : ρ < 2048 * ζ.real univ) :
    ENNReal.ofReal (ρ/2) ≤
      ENNReal.ofReal (1 + 8/5 * max 2048 (28000 * sqrt θ)) *
        EntropyTail.selection (σ+τ+ζ) ρ B := by
  have hh := budgetScale_pos hB
  have hH0 : 0 ≤ ∫ d : Gap, (d:ℝ)⁻¹ ∂τ := integral_nonneg fun d => inv_nonneg.mpr d.property.1.le
  obtain ⟨K, hK0, hK, -, hQK⟩ :=
    quantile_split_comparison σ τ ζ hρ hρ4 hB hcore htail hτs hζs
  have hm : (2048:ℝ) ≤ max 2048 (28000 * sqrt θ) := le_max_left _ _
  rw [hK, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hlow : ρ/2048 ≤ min ρ (ζ.real univ + budgetScale B * (∫ d : Gap, (d:ℝ)⁻¹ ∂τ) +
      budgetScale B * sqrt (ρ * (measureCostEntropy σ).toReal)) := by
    refine le_min (by linarith) ?_
    have h1 : 0 ≤ budgetScale B * (∫ d : Gap, (d:ℝ)⁻¹ ∂τ) := mul_nonneg hh.le hH0
    have h2 : 0 ≤ budgetScale B * sqrt (ρ * (measureCostEntropy σ).toReal) :=
      mul_nonneg hh.le (sqrt_nonneg _)
    linarith
  nlinarith [mul_le_mul_of_nonneg_right hm hK0]

/-- The reported radius. The plan reports a mean-square bound `min{ρ²/4, c}`,
and the median interval has radius an upper square root of eight times that
bound. With a relative enclosure, `r ≤ κ √(8 min{ρ²/4, c})` with `κ √8 ≤ 6`,
a rate `min{ρ/2, √c} ≤ C K` gives `r ≤ 6 C K`, however small the radius is. -/
theorem plan_radius_le {ρ c κ r C : ℝ} {K : ℝ≥0∞} (hρ : 0 ≤ ρ)
    (hκ : κ * sqrt 8 ≤ 6) (hr : r ≤ κ * sqrt (8 * min (ρ^2/4) c))
    (hrate : ENNReal.ofReal (min (ρ/2) (sqrt c)) ≤ ENNReal.ofReal C * K) :
    ENNReal.ofReal r ≤ ENNReal.ofReal (6 * C) * K := by
  have hhalf : sqrt (ρ^2/4) = ρ/2 := by
    rw [show ρ^2/4 = (ρ/2)^2 by ring, sqrt_sq (by linarith)]
  have hmono : Monotone Real.sqrt := fun _ _ hab => Real.sqrt_le_sqrt hab
  have hmin : sqrt (min (ρ^2/4) c) = min (ρ/2) (sqrt c) := by
    rw [hmono.map_min, hhalf]
  have hm0 : 0 ≤ min (ρ/2) (sqrt c) := le_min (by linarith) (sqrt_nonneg c)
  have hreal : r ≤ 6 * min (ρ/2) (sqrt c) := by
    rw [sqrt_mul (by norm_num), hmin, ← mul_assoc] at hr
    exact hr.trans (mul_le_mul_of_nonneg_right hκ hm0)
  calc ENNReal.ofReal r ≤ ENNReal.ofReal (6 * min (ρ/2) (sqrt c)) := ENNReal.ofReal_le_ofReal hreal
    _ = 6 * ENNReal.ofReal (min (ρ/2) (sqrt c)) := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    _ ≤ 6 * (ENNReal.ofReal C * K) := by gcongr
    _ = ENNReal.ofReal (6 * C) * K := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, mul_assoc]

/-- The reported radius of the exact plan of the quantile split is at most
`6 (1 + (8/5) max{2048, 28000 √θ}) K_{μ,ρ}(B)`, for every relative upper
square root with `κ √8 ≤ 6`. -/
theorem quantile_plan_radius (σ τ ζ : Measure Gap)
    [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)]
    {ρ B θ κ r : ℝ} {N : ℕ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) (hθ : 0 ≤ θ)
    (hcore : σ = quantileCore (σ+τ+ζ) ρ) (htail : τ+ζ = quantileTail (σ+τ+ζ) ρ)
    (hτs : ∀ᵐ d : Gap ∂τ, budgetScale B ≤ (d:ℝ)) (hζs : ∀ᵐ d : Gap ∂ζ, (d:ℝ) ≤ budgetScale B)
    (hN : bandEdge N < quantileThreshold (σ+τ+ζ) ρ) (hz : 2048 * ζ.real univ ≤ ρ)
    (w : Fin (planTerminal hρ B (ζ.real univ) + 1) → ℝ)
    (hlow : ∀ i, sqrt (17*levelAccuracy ρ i.val /
      planCost (SplitEnclosure.exact σ τ ζ N) ρ
        (searchCaps (eta (σ+τ)) (eta_vanishes (σ+τ)) hρ)
        (planTerminal hρ B (ζ.real univ)) i) ≤ w i)
    (hup : ∀ i, w i ≤ θ * sqrt (17*levelAccuracy ρ i.val /
      planCost (SplitEnclosure.exact σ τ ζ N) ρ
        (searchCaps (eta (σ+τ)) (eta_vanishes (σ+τ)) hρ)
        (planTerminal hρ B (ζ.real univ)) i))
    (hκ : κ * sqrt 8 ≤ 6)
    (hr : r ≤ κ * sqrt (8 * min (ρ^2/4) (planCertificate ρ (planRates B
      (planCost (SplitEnclosure.exact σ τ ζ N) ρ
        (searchCaps (eta (σ+τ)) (eta_vanishes (σ+τ)) hρ)
        (planTerminal hρ B (ζ.real univ))) w)))) :
    ENNReal.ofReal r ≤
      ENNReal.ofReal (6 * (1 + 8/5 * max 2048 (28000 * sqrt θ))) *
        EntropyTail.selection (σ+τ+ζ) ρ B :=
  plan_radius_le hρ.le hκ hr
    (quantile_plan_rate σ τ ζ hρ hρ4 hB hθ hcore htail hτs hζs hN hz w hlow hup)

end ThresholdHC.KnownLawPlanner
