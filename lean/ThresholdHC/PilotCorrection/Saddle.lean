import ThresholdHC.PilotCorrection.Quadratic
import ThresholdHC.PilotCorrection.Mixture

/-! The saddle point of `Var_q(Y - βZ)` on `ℝ × Q`.

Under `FixedFeatures`, the variance has the quadratic form of
`quadratic_saddle` on `Q`, with affine continuous coefficients, so it has a
saddle point; coercing to `EReal`, `isSaddlePointOn_value` gives the common
minimax value. -/

noncomputable section
namespace ThresholdHC.PilotCorrection
open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} {π : Fin k → ℝ} {ρ : ℝ}
  {Pplus Pminus : Fin k → Measure Ω} [∀ i, IsProbabilityMeasure (Pplus i)]
  [∀ i, IsProbabilityMeasure (Pminus i)] {Y Z : Ω → ℝ} {v : ℝ}

theorem saddle_real (hF : FixedFeatures π ρ Pplus Pminus Y Z v) :
    ∃ β₀ : ℝ, ∃ q₀ ∈ rarityPolytope π ρ,
      IsSaddlePointOn Set.univ (rarityPolytope π ρ)
        (fun β q => variance (fun ω => Y ω - β * Z ω) (coinLaw π Pplus Pminus q)) β₀ q₀ := by
  have hρ : 0 ≤ ρ := hF.2.2.1
  have hv : 0 < v := hF.2.2.2.2.2.2.1
  refine quadratic_saddle (rarityPolytope_isCompact π ρ) (rarityPolytope_convex π ρ)
    ⟨0, zero_mem_rarityPolytope π hρ⟩
    (fun q => ∑ i, (π i * ((∫ ω, Y ω ^ 2 ∂Pplus i) - ∫ ω, Y ω ^ 2 ∂Pminus i) * q i +
      π i * ∫ ω, Y ω ^ 2 ∂Pminus i))
    (fun q => ∑ i, (π i * q i + (0 : Fin k → ℝ) i))
    (fun q => ∑ i, (π i * ((∫ ω, Y ω * Z ω ∂Pplus i) - ∫ ω, Y ω * Z ω ∂Pminus i) * q i +
      π i * ∫ ω, Y ω * Z ω ∂Pminus i))
    (continuous_sum_affine _ _).continuousOn (continuous_sum_affine _ _).continuousOn
    (continuous_sum_affine _ _).continuousOn
    (fun p _ q _ t _ _ => sum_affine_segment _ _ p q t)
    (fun p _ q _ t _ _ => sum_affine_segment _ _ p q t)
    (fun p _ q _ t _ _ => sum_affine_segment _ _ p q t) hv _ ?_
  intro β q hq
  rw [variance_coinLaw hF hq β, signMass_eq_sum_affine]

theorem saddle_value {f : ℝ → (Fin k → ℝ) → ℝ} {β₀ : ℝ} {q₀ : Fin k → ℝ}
    (hq₀ : q₀ ∈ rarityPolytope π ρ)
    (h : IsSaddlePointOn Set.univ (rarityPolytope π ρ) f β₀ q₀) :
    (⨅ β : ℝ, ⨆ q ∈ rarityPolytope π ρ, ((f β q : ℝ) : EReal)) = ((f β₀ q₀ : ℝ) : EReal) ∧
      (⨆ q ∈ rarityPolytope π ρ, ⨅ β : ℝ, ((f β q : ℝ) : EReal)) =
        ((f β₀ q₀ : ℝ) : EReal) := by
  have h' : IsSaddlePointOn Set.univ (rarityPolytope π ρ)
      (fun β q => ((f β q : ℝ) : EReal)) β₀ q₀ :=
    fun x hx y hy => EReal.coe_le_coe_iff.mpr (h x hx y hy)
  have hv := isSaddlePointOn_value (Set.mem_univ β₀) hq₀ h'
  simpa only [Set.mem_univ, iInf_pos] using hv

end ThresholdHC.PilotCorrection
