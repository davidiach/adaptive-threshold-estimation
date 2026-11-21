import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Order.SaddlePoint

/-! The saddle point of a quadratic control-variate risk.

For a compact convex nonempty set `Q`, functions `A`, `θ`, `c` that are
continuous on `Q` and affine along segments of `Q`, and `v > 0`, the map
`f β q = A q - θ q ^ 2 - 2 β c q + v β ^ 2` has a saddle point on `ℝ × Q`.
The proof maximizes `g = A - θ ^ 2 - c ^ 2 / v` over `Q` at `q₀` and takes
`β₀ = c q₀ / v`; this replaces the coercivity and active-set argument of the
source `thm:saddle`. -/

namespace ThresholdHC.PilotCorrection

/-- If `D ≤ t K` for every `t ∈ (0,1]` and `K ≥ 0`, then `D ≤ 0`. -/
theorem le_zero_of_forall_le_mul {D K : ℝ} (hK : 0 ≤ K)
    (h : ∀ t : ℝ, 0 < t → t ≤ 1 → D ≤ t * K) : D ≤ 0 := by
  by_contra hD'
  have hD : 0 < D := lt_of_not_ge hD'
  have hK1 : 0 < K + 1 := by linarith
  have ht0 : 0 < min 1 (D / (2 * (K + 1))) :=
    lt_min one_pos (div_pos hD (by positivity))
  have ht1 : min 1 (D / (2 * (K + 1))) ≤ 1 := min_le_left _ _
  have ht2 : min 1 (D / (2 * (K + 1))) ≤ D / (2 * (K + 1)) := min_le_right _ _
  have h3 : min 1 (D / (2 * (K + 1))) * (K + 1) ≤ D / 2 := by
    calc min 1 (D / (2 * (K + 1))) * (K + 1) ≤ D / (2 * (K + 1)) * (K + 1) :=
          mul_le_mul_of_nonneg_right ht2 hK1.le
      _ = D / 2 := by field_simp
  have h4 := h _ ht0 ht1
  nlinarith

/-- The quadratic saddle point. -/
theorem quadratic_saddle {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    {Q : Set E} (hQc : IsCompact Q) (hQv : Convex ℝ Q) (hQn : Q.Nonempty)
    (A θ c : E → ℝ) (hA : ContinuousOn A Q) (hθ : ContinuousOn θ Q)
    (hc : ContinuousOn c Q)
    (hAa : ∀ p ∈ Q, ∀ q ∈ Q, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      A (p + t • (q - p)) = A p + t * (A q - A p))
    (hθa : ∀ p ∈ Q, ∀ q ∈ Q, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      θ (p + t • (q - p)) = θ p + t * (θ q - θ p))
    (hca : ∀ p ∈ Q, ∀ q ∈ Q, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      c (p + t • (q - p)) = c p + t * (c q - c p))
    {v : ℝ} (hv : 0 < v) (f : ℝ → E → ℝ)
    (hf : ∀ β, ∀ q ∈ Q, f β q = A q - θ q ^ 2 - 2 * β * c q + v * β ^ 2) :
    ∃ β₀ : ℝ, ∃ q₀ ∈ Q, IsSaddlePointOn Set.univ Q f β₀ q₀ := by
  have hg : ContinuousOn (fun q => A q - θ q ^ 2 - c q ^ 2 / v) Q :=
    (hA.sub (hθ.pow 2)).sub ((hc.pow 2).div_const v)
  obtain ⟨q₀, hq₀, hmax⟩ := hQc.exists_isMaxOn hQn hg
  refine ⟨c q₀ / v, q₀, hq₀, ?_⟩
  intro β _ q hq
  rw [hf _ q hq, hf _ q₀ hq₀]
  have hβ₀ : v * (c q₀ / v) = c q₀ := by field_simp
  set β₀ := c q₀ / v with hβ₀def
  have hD : (A q - A q₀) - 2 * θ q₀ * (θ q - θ q₀) - 2 * β₀ * (c q - c q₀) ≤ 0 := by
    apply le_zero_of_forall_le_mul (K := (θ q - θ q₀) ^ 2 + (c q - c q₀) ^ 2 / v)
      (by positivity)
    intro t ht0 ht1
    have hmem : q₀ + t • (q - q₀) ∈ Q := hQv.add_smul_sub_mem hq₀ hq ⟨ht0.le, ht1⟩
    have hle := isMaxOn_iff.mp hmax _ hmem
    rw [hAa q₀ hq₀ q hq t ht0.le ht1, hθa q₀ hq₀ q hq t ht0.le ht1,
      hca q₀ hq₀ q hq t ht0.le ht1] at hle
    have hcid : (c q₀ + t * (c q - c q₀)) ^ 2 / v - c q₀ ^ 2 / v =
        2 * t * β₀ * (c q - c q₀) + t * (t * ((c q - c q₀) ^ 2 / v)) := by
      rw [← hβ₀]; field_simp; ring
    have hmul : t * ((A q - A q₀) - 2 * θ q₀ * (θ q - θ q₀) - 2 * β₀ * (c q - c q₀)) ≤
        t * (t * ((θ q - θ q₀) ^ 2 + (c q - c q₀) ^ 2 / v)) := by
      nlinarith
    exact le_of_mul_le_mul_left hmul ht0
  have hsq : 0 ≤ (β - β₀) ^ 2 := sq_nonneg _
  have hvsq : 0 ≤ v * (β - β₀) ^ 2 := mul_nonneg hv.le hsq
  rw [← hβ₀] at hD ⊢
  nlinarith [sq_nonneg (θ q - θ q₀)]

end ThresholdHC.PilotCorrection
