import ThresholdHC.AnytimeLower.FiniteMatching
import ThresholdHC.AnytimeLower.DenseTail
import ThresholdHC.AnytimeLower.SparseTail
import ThresholdHC.AnytimeLower.TailRegion

noncomputable section
open MeasureTheory Real Set Filter
open scoped ENNReal Topology
namespace ThresholdHC.AnytimeLower
open ThresholdHC.Tier3 ThresholdHC.Tier6

/-- Every positive-gap law forces the known-law selection rate, with its
iterated-logarithm budget penalty, at arbitrarily late physical budgets.
No monotonicity of the deterministic envelope is required. -/
theorem law_dependent_online_lower {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ δ : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hd : 0 < δ ∧ δ ≤ 1/4)
    (A : AdaptiveEstimator R) (H : ∀ n, R × Prefix n → ℝ)
    (hH : ∀ n, Measurable (H n)) (t : ℕ → ℝ) (hacc : OnlineAccuracy μ A H ρ δ t)
    (M : ℕ) :
    ∃ n : ℕ, M ≤ n ∧ ENNReal.ofReal ((10:ℝ)⁻¹^22) *
      ThresholdHC.EntropyTail.selection μ ρ ((n:ℝ)/budgetInflation δ n) ≤ ENNReal.ofReal (t n) := by
  by_cases hI : Integrable (fun d : Gap => (d:ℝ)⁻¹) μ
  · exact finite_coefficient_matching μ hρ hρ4 (selectionCoefficients_bddAbove μ hI ρ)
      A H hH ⟨hd.1.le,by linarith⟩ t hacc M
  obtain ⟨τ,hτ,hτq,hμ,hm⟩ := exists_smallGapRegion μ hI hρ
  by_cases hdense : ∀ᶠ k in atTop, (tailDropIndex μ hτ hμ k:ℝ) ≤ ((k:ℝ)+2)^2
  · obtain ⟨n,hn,hbound⟩ := dense_tail_matching μ hI A H hH hτ hτq hμ hm
      ⟨hd.1.le,by linarith⟩ t hacc hdense M
    refine ⟨n,hn,?_⟩
    exact (mul_le_mul_left (ENNReal.ofReal_le_ofReal
      (by norm_num : (10:ℝ)⁻¹^22 ≤ 1/2560)) _).trans hbound
  have hlarge : ∃ᶠ k : ℕ in atTop, (k:ℝ)^2 < (tailDropIndex μ hτ hμ k:ℝ) := by
    have hf : ∃ᶠ k : ℕ in atTop, ((k:ℝ)+2)^2 < (tailDropIndex μ hτ hμ k:ℝ) := by
      simpa only [not_eventually,not_le] using hdense
    apply hf.mono
    intro k hk
    have := Nat.cast_nonneg (α:=ℝ) k
    nlinarith
  have hblocks := frequently_long_blocks (fun k => (tailDropIndex μ hτ hμ k:ℝ))
    (fun k => Nat.cast_nonneg _) hlarge
  obtain ⟨n,hn,hbound⟩ := sparse_tail_matching μ hI A H hH hτ hτq hμ hm hd.2 t hacc hblocks M
  refine ⟨n,hn,?_⟩
  exact (mul_le_mul_left (ENNReal.ofReal_le_ofReal
    (by norm_num : (10:ℝ)⁻¹^22 ≤ 1/512)) _).trans hbound

end ThresholdHC.AnytimeLower
