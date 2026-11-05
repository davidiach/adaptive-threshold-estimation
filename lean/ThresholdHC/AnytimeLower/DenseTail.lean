
import ThresholdHC.AnytimeLower.TailAsymptotics
import ThresholdHC.AnytimeLower.TailGeometry
import ThresholdHC.AnytimeLower.TailSchedule
import ThresholdHC.AnytimeLower.InflatedScale

noncomputable section
open MeasureTheory Real Set Filter
open scoped ENNReal Topology
namespace ThresholdHC.AnytimeLower
open ThresholdHC.Tier3 ThresholdHC.Tier6

/-- The dense-block branch of the law-dependent comparison, with an explicit
constant and arbitrarily late integer physical budgets. -/
theorem dense_tail_matching {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ]
    (hI : ¬Integrable (fun d : Gap => (d:ℝ)⁻¹) μ)
    (A : AdaptiveEstimator R) (H : ∀ n, R × Prefix n → ℝ)
    (hH : ∀ n, Measurable (H n))
    {τ ρ δ : ℝ} (hτ : 0 < τ) (hτq : τ ≤ 1/4)
    (hμ : 0 < μ {d : Gap | (d:ℝ) ≤ τ})
    (hrare : μ.real {d : Gap | (d:ℝ) ≤ τ} ≤ ρ)
    (hd : 0 ≤ δ ∧ δ ≤ 1/2) (t : ℕ → ℝ) (hacc : OnlineAccuracy μ A H ρ δ t)
    (hdense : ∀ᶠ k in atTop, (tailDropIndex μ hτ hμ k:ℝ) ≤ ((k:ℝ)+2)^2)
    (M : ℕ) :
    ∃ n : ℕ, M ≤ n ∧ ENNReal.ofReal (1/2560) *
      ThresholdHC.EntropyTail.selection μ ρ ((n:ℝ)/budgetInflation δ n) ≤ ENNReal.ofReal (t n) := by
  let s := selectedScale μ hτ hμ
  let N := testingBudget δ s
  have hs : ∀ k, 0 < s k := fun k => geometricScale_pos hτ _
  have hN := testingBudget_tendsto (by linarith : δ < 1) s hs (selectedScale_antitone μ hτ hμ)
  have hf := tail_scheduled_frequently μ A H hH hτ hτq hμ hrare hd t hacc
  obtain ⟨h₀,hh₀,hupper⟩ := tail_selection_small_scale μ hI hτ ρ
  have hsmall := (selectedScale_tendsto_zero μ hτ hμ).eventually
    (gt_mem_nhds (show (0:ℝ) < h₀/5 by positivity))
  have hscale := dense_inflatedScale_bound hd hτ (tailDropIndex μ hτ hμ)
    (tailDropIndex_strictMono μ hτ hμ).monotone hdense
  have he : ∀ᶠ k in atTop, ThresholdHC.EntropyTail.selection μ ρ
      ((N k:ℝ)/budgetInflation δ (N k)) ≤ ENNReal.ofReal (10*profileMass μ τ (s k)) := by
    filter_upwards [hsmall,hscale] with k hk hsk
    change 0 < N k ∧ 0 < budgetInflation δ (N k) ∧
      inflatedScale δ (N k) ≤ 5*s k at hsk
    have hnp : (0:ℝ) < N k := by exact_mod_cast hsk.1
    have hB : 0 < (N k:ℝ)/budgetInflation δ (N k) := div_pos hnp hsk.2.1
    have hu := hupper ((N k:ℝ)/budgetInflation δ (N k)) hB (by
      change inflatedScale δ (N k) ≤ h₀
      have hh : s k < h₀/5 := hk
      linarith [hsk.2.2])
    have hp := (profileMass_mono μ τ (ThresholdHC.EntropyTailQuantile.budgetScale_nonneg _)
      hsk.2.2).trans (profileMass_scaled μ τ (hs k).le (show (1:ℝ) ≤ 5 by norm_num))
    change profileMass μ τ (inflatedScale δ (N k)) ≤ 5*profileMass μ τ (s k) at hp
    apply hu.trans (ENNReal.ofReal_le_ofReal _)
    change 2*profileMass μ τ (inflatedScale δ (N k)) ≤ _
    linarith
  obtain ⟨k,hk,hK,hM⟩ := (hf.and_eventually (he.and (hN.eventually (eventually_ge_atTop M)))).exists
  refine ⟨N k,hM,?_⟩
  calc
    _ ≤ ENNReal.ofReal (1/2560)*ENNReal.ofReal (10*profileMass μ τ (s k)) :=
      mul_le_mul_right hK _
    _ = ENNReal.ofReal (profileMass μ τ (s k)/256) := by
      rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/2560)]
      congr 1
      ring
    _ ≤ ENNReal.ofReal (t (N k)) := ENNReal.ofReal_le_ofReal hk

end ThresholdHC.AnytimeLower
