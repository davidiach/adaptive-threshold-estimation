import ThresholdHC.KnownLawPlanner.PlanTightRate
import ThresholdHC.KnownLawPlanner.PlanQuantileRate

/-! A plan computed from upper bounds attains the oracle rate.

Let the planner use the quantile split of its gap law and a tight enclosure
of the design integrals. It chooses the terminal level from its bound `z̄` of
the unresolved mass, and falls back to the constant when `2048 z̄ > ρ`. Then

  `min{ρ/2, √certificate} ≤ (1 + (8/5) max{4096, 8 · 28000 √θ}) K_{μ,ρ}(B)`,

for weights within a factor `θ` of the optimal ones, and the constant
fallback obeys the same bound. For dyadic upper square roots, `θ = 2`, the
second entry of the maximum is `8 √2 · 28000`. -/

noncomputable section
open MeasureTheory Set Real
open scoped NNReal ENNReal BigOperators

namespace ThresholdHC.KnownLawPlanner
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTailQuantile ThresholdHC.EntropyTailUpper
open ThresholdHC.EntropyTailAssembly ThresholdHC.EntropyTailExecution

/-- The rate arithmetic. Let `K` be the oracle value with floor `F ≤ K`, and
let the capped design value `min{ρ, z + V}` be at most `c K`. A certified
risk `s ≤ δ + a V` with `δ ≤ m z + F` gives
`min{ρ/2, s} ≤ (1 + c max{m, a}) K`. -/
theorem rate_arithmetic {ρ K F V z s δ c m a : ℝ} (hK : 0 ≤ K) (hF : F ≤ K) (hc : 0 ≤ c)
    (hm : 1/2 ≤ m) (hz : 0 ≤ z) (hV : 0 ≤ V) (hQ : min ρ (z + V) ≤ c * K)
    (hδ : δ ≤ m * z + F) (hs : s ≤ δ + a * V) :
    min (ρ/2) s ≤ (1 + c * max m a) * K := by
  have hmax : 1/2 ≤ max m a := hm.trans (le_max_left _ _)
  have hmax0 : 0 ≤ max m a := le_trans (by norm_num) hmax
  have h1 : m * z ≤ max m a * z := mul_le_mul_of_nonneg_right (le_max_left _ _) hz
  have h2 : a * V ≤ max m a * V := mul_le_mul_of_nonneg_right (le_max_right _ _) hV
  rcases le_total (z + V) ρ with hcase | hcase
  · rw [min_eq_right hcase] at hQ
    refine (min_le_right _ _).trans ?_
    nlinarith [mul_le_mul_of_nonneg_left hQ hmax0]
  · rw [min_eq_left hcase] at hQ
    refine (min_le_left _ _).trans ?_
    nlinarith [mul_nonneg (mul_nonneg hc hK) (sub_nonneg.mpr hmax)]

/-- The fallback arithmetic. When the capped design value `min{ρ, U}` is at
most `c K`, `z ≤ U` and `ρ < m z`, the constant risk `ρ/2` is at most
`(1 + c max{m, a}) K`. -/
theorem fallback_arithmetic {ρ K U z c m : ℝ} (a : ℝ) (hρ : 0 ≤ ρ) (hK : 0 ≤ K) (hc : 0 ≤ c)
    (hm : 1/2 ≤ m) (hzU : z ≤ U) (hQ : min ρ U ≤ c * K) (hfall : ρ < m * z) :
    ρ/2 ≤ (1 + c * max m a) * K := by
  have hmax : m ≤ max m a := le_max_left _ _
  have hm0 : 0 ≤ m := le_trans (by norm_num) hm
  have hcK : 0 ≤ c * K := mul_nonneg hc hK
  rcases le_total U ρ with hcase | hcase
  · rw [min_eq_right hcase] at hQ
    have h1 : m * z ≤ m * (c * K) := mul_le_mul_of_nonneg_left (hzU.trans hQ) hm0
    nlinarith [mul_le_mul_of_nonneg_right hmax hcK]
  · rw [min_eq_left hcase] at hQ
    nlinarith [mul_nonneg hcK (sub_nonneg.mpr (hm.trans hmax))]

/-- The rate of a plan computed from a tight enclosure, in real numbers. Let
`K` be an oracle value with `ρ/(1 + √B) ≤ K` and
`min{ρ, z + h H + h √(ρ Γ_σ)} ≤ c K`. Outside the constant fallback, the
smaller of `ρ/2` and the certified risk of the plan is at most
`(1 + c max{4096, 8 · 28000 √θ}) K`. -/
theorem tight_plan_rate_real (σ τ ζ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ]
    {t ρ B θ z K c : ℝ} {N : ℕ} (ht : 0 < t) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d:ℝ))
    (hN : bandEdge N < t) (hτs : ∀ᵐ d : Gap ∂τ, budgetScale B ≤ (d:ℝ)) (hρ : 0 < ρ)
    (hB : 0 < B) (hθ : 0 ≤ θ) (hm : ρ/128 < (σ+τ).real univ)
    (E : SplitEnclosure σ τ ζ N) (hE : E.Tight z) (hz : 2048 * E.unresolved ≤ ρ)
    (hK : 0 ≤ K) (hfloor : ρ/(1+sqrt B) ≤ K) (hc : 0 ≤ c)
    (hQ : min ρ (z + (budgetScale B * (∫ d : Gap, (d:ℝ)⁻¹ ∂τ) +
      budgetScale B * sqrt (ρ * (measureCostEntropy σ).toReal))) ≤ c * K)
    (w : Fin (planTerminal hρ B E.unresolved + 1) → ℝ)
    (hlow : ∀ i, sqrt (17*levelAccuracy ρ i.val /
      planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ)
        (planTerminal hρ B E.unresolved) i) ≤ w i)
    (hup : ∀ i, w i ≤ θ * sqrt (17*levelAccuracy ρ i.val /
      planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ)
        (planTerminal hρ B E.unresolved) i)) :
    min (ρ/2) (sqrt (planCertificate ρ (planRates B
        (planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ)
          (planTerminal hρ B E.unresolved)) w))) ≤
      (1 + c * max 4096 (224000 * sqrt θ)) * K := by
  have hh := budgetScale_pos hB
  have hτ := inverse_integrable_of_support τ hh hτs
  have hz0 : 0 ≤ z := by linarith [hE.2.2.1, hE.2.2.2.1]
  have hH0 : 0 ≤ ∫ d : Gap, (d:ℝ)⁻¹ ∂τ := integral_nonneg fun d => inv_nonneg.mpr d.property.1.le
  have hG : measureCostEntropy σ ≠ ⊤ := (measureCostEntropy_lt_top_of_support σ ht hs).ne
  have hΓ0 := costEntropy_nonneg (fun j : Fin N => bandCost_nonneg σ j.val)
  have hΓN : costEntropy (fun j : Fin N => bandCost σ j.val) ≤ (measureCostEntropy σ).toReal := by
    rw [← ENNReal.toReal_ofReal hΓ0]
    exact ENNReal.toReal_mono hG (le_iSup (fun k : ℕ => ENNReal.ofReal
      (costEntropy (fun j : Fin k => bandCost σ j.val))) N)
  obtain ⟨hzJ, hδ⟩ := tight_planTerminal hE hρ B hz
  have hrms := tight_plan_rms_le σ τ ζ ht hs hN hτ hρ hB hθ hm E hE
    (planTerminal hρ B E.unresolved) hzJ w hlow hup
  have hscale : (1:ℝ)/sqrt B = budgetScale B := by
    unfold budgetScale
    rw [one_div]
  have hroot : sqrt (ρ * costEntropy (fun j : Fin N => bandCost σ j.val)) ≤
      sqrt (ρ * (measureCostEntropy σ).toReal) :=
    sqrt_le_sqrt (mul_le_mul_of_nonneg_left hΓN hρ.le)
  have hX : sqrt θ * (224000*(sqrt (ρ*costEntropy (fun j : Fin N => bandCost σ j.val)) +
      ∫ d : Gap, (d:ℝ)⁻¹ ∂τ)) / sqrt B =
      224000 * sqrt θ * (budgetScale B * (∫ d : Gap, (d:ℝ)⁻¹ ∂τ) +
        budgetScale B * sqrt (ρ*costEntropy (fun j : Fin N => bandCost σ j.val))) := by
    rw [← hscale]
    ring
  rw [hX] at hrms
  have hV : 224000 * sqrt θ * (budgetScale B * (∫ d : Gap, (d:ℝ)⁻¹ ∂τ) +
      budgetScale B * sqrt (ρ*costEntropy (fun j : Fin N => bandCost σ j.val))) ≤
      224000 * sqrt θ * (budgetScale B * (∫ d : Gap, (d:ℝ)⁻¹ ∂τ) +
        budgetScale B * sqrt (ρ * (measureCostEntropy σ).toReal)) :=
    mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left hroot hh.le))
      (by positivity)
  exact rate_arithmetic hK hfloor hc (by norm_num) hz0
    (add_nonneg (mul_nonneg hh.le hH0) (mul_nonneg hh.le (sqrt_nonneg _))) hQ hδ.le
    (hrms.trans (add_le_add le_rfl hV))

/-- The rate of a plan computed from a tight enclosure of the quantile split.
Outside the constant fallback, the smaller of `ρ/2` and the certified risk
is at most `(1 + (8/5) max{4096, 8 · 28000 √θ}) K_{μ,ρ}(B)`. -/
theorem tight_quantile_plan_rate (σ τ ζ : Measure Gap)
    [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)]
    {ρ B θ : ℝ} {N : ℕ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) (hθ : 0 ≤ θ)
    (hcore : σ = quantileCore (σ+τ+ζ) ρ) (htail : τ+ζ = quantileTail (σ+τ+ζ) ρ)
    (hτs : ∀ᵐ d : Gap ∂τ, budgetScale B ≤ (d:ℝ)) (hζs : ∀ᵐ d : Gap ∂ζ, (d:ℝ) ≤ budgetScale B)
    (hN : bandEdge N < quantileThreshold (σ+τ+ζ) ρ)
    (E : SplitEnclosure σ τ ζ N) (hE : E.Tight (ζ.real univ)) (hz : 2048 * E.unresolved ≤ ρ)
    (w : Fin (planTerminal hρ B E.unresolved + 1) → ℝ)
    (hlow : ∀ i, sqrt (17*levelAccuracy ρ i.val /
      planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ)
        (planTerminal hρ B E.unresolved) i) ≤ w i)
    (hup : ∀ i, w i ≤ θ * sqrt (17*levelAccuracy ρ i.val /
      planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ)
        (planTerminal hρ B E.unresolved) i)) :
    ENNReal.ofReal (min (ρ/2) (sqrt (planCertificate ρ (planRates B
        (planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ)
          (planTerminal hρ B E.unresolved)) w)))) ≤
      ENNReal.ofReal (1 + 8/5 * max 4096 (224000 * sqrt θ)) *
        EntropyTail.selection (σ+τ+ζ) ρ B := by
  have hρ1 : ρ ≤ 1 := by linarith
  have ht := (quantileThreshold_properties (σ+τ+ζ) hρ hρ1).1
  have hs : ∀ᵐ d : Gap ∂σ, quantileThreshold (σ+τ+ζ) ρ ≤ (d:ℝ) := by
    have h := quantileCore_support (σ+τ+ζ) ρ
    rw [← hcore] at h
    exact h
  have hm : ρ/128 < (σ+τ).real univ :=
    resolved_mass_large σ τ ζ hρ4 (by linarith [E.unresolved_le])
  obtain ⟨K, hK0, hK, hfloor, hQK⟩ :=
    quantile_split_comparison σ τ ζ hρ hρ4 hB hcore htail hτs hζs
  rw [hK, ← ENNReal.ofReal_mul (by positivity)]
  rw [add_assoc] at hQK
  exact ENNReal.ofReal_le_ofReal (tight_plan_rate_real σ τ ζ ht hs hN hτs hρ hB hθ hm E hE hz
    hK0 hfloor (by norm_num) hQK w hlow hup)

/-- The constant fallback obeys the same bound. When `2048 z̄ > ρ` the planner
returns the constant `ρ/2`. -/
theorem tight_quantile_fallback_rate (σ τ ζ : Measure Gap)
    [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)]
    {ρ B : ℝ} {N : ℕ} (θ : ℝ) (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B)
    (hcore : σ = quantileCore (σ+τ+ζ) ρ) (htail : τ+ζ = quantileTail (σ+τ+ζ) ρ)
    (hτs : ∀ᵐ d : Gap ∂τ, budgetScale B ≤ (d:ℝ)) (hζs : ∀ᵐ d : Gap ∂ζ, (d:ℝ) ≤ budgetScale B)
    (E : SplitEnclosure σ τ ζ N) (hE : E.Tight (ζ.real univ)) (hz : ρ < 2048 * E.unresolved) :
    ENNReal.ofReal (ρ/2) ≤
      ENNReal.ofReal (1 + 8/5 * max 4096 (224000 * sqrt θ)) *
        EntropyTail.selection (σ+τ+ζ) ρ B := by
  have hh := budgetScale_pos hB
  have hH0 : 0 ≤ ∫ d : Gap, (d:ℝ)⁻¹ ∂τ := integral_nonneg fun d => inv_nonneg.mpr d.property.1.le
  obtain ⟨K, hK0, hK, -, hQK⟩ :=
    quantile_split_comparison σ τ ζ hρ hρ4 hB hcore htail hτs hζs
  rw [hK, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hzU : ζ.real univ ≤ ζ.real univ + budgetScale B * (∫ d : Gap, (d:ℝ)⁻¹ ∂τ) +
      budgetScale B * sqrt (ρ * (measureCostEntropy σ).toReal) := by
    have h1 : 0 ≤ budgetScale B * (∫ d : Gap, (d:ℝ)⁻¹ ∂τ) := mul_nonneg hh.le hH0
    have h2 : 0 ≤ budgetScale B * sqrt (ρ * (measureCostEntropy σ).toReal) :=
      mul_nonneg hh.le (sqrt_nonneg _)
    linarith
  exact fallback_arithmetic (224000 * sqrt θ) hρ.le hK0 (by norm_num) (by norm_num) hzU hQK
    (by linarith [hE.2.2.2.1])

/-- The reported radius of a plan computed from a tight enclosure is at most
`6 (1 + (8/5) max{4096, 8 · 28000 √θ}) K_{μ,ρ}(B)`, for every relative upper
square root with `κ √8 ≤ 6`. -/
theorem tight_quantile_plan_radius (σ τ ζ : Measure Gap)
    [IsFiniteMeasure σ] [IsFiniteMeasure τ] [IsFiniteMeasure ζ] [IsProbabilityMeasure (σ+τ+ζ)]
    {ρ B θ κ r : ℝ} {N : ℕ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) (hθ : 0 ≤ θ)
    (hcore : σ = quantileCore (σ+τ+ζ) ρ) (htail : τ+ζ = quantileTail (σ+τ+ζ) ρ)
    (hτs : ∀ᵐ d : Gap ∂τ, budgetScale B ≤ (d:ℝ)) (hζs : ∀ᵐ d : Gap ∂ζ, (d:ℝ) ≤ budgetScale B)
    (hN : bandEdge N < quantileThreshold (σ+τ+ζ) ρ)
    (E : SplitEnclosure σ τ ζ N) (hE : E.Tight (ζ.real univ)) (hz : 2048 * E.unresolved ≤ ρ)
    (w : Fin (planTerminal hρ B E.unresolved + 1) → ℝ)
    (hlow : ∀ i, sqrt (17*levelAccuracy ρ i.val /
      planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ)
        (planTerminal hρ B E.unresolved) i) ≤ w i)
    (hup : ∀ i, w i ≤ θ * sqrt (17*levelAccuracy ρ i.val /
      planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ)
        (planTerminal hρ B E.unresolved) i))
    (hκ : κ * sqrt 8 ≤ 6)
    (hr : r ≤ κ * sqrt (8 * min (ρ^2/4) (planCertificate ρ (planRates B
      (planCost E ρ (searchCaps E.resolvedError hE.vanishes hρ)
        (planTerminal hρ B E.unresolved)) w)))) :
    ENNReal.ofReal r ≤
      ENNReal.ofReal (6 * (1 + 8/5 * max 4096 (224000 * sqrt θ))) *
        EntropyTail.selection (σ+τ+ζ) ρ B :=
  plan_radius_le hρ.le hκ hr
    (tight_quantile_plan_rate σ τ ζ hρ hρ4 hB hθ hcore htail hτs hζs hN E hE hz w hlow hup)

end ThresholdHC.KnownLawPlanner
