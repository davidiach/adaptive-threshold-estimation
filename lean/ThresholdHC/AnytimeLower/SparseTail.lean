import ThresholdHC.AnytimeLower.SparseScale
import ThresholdHC.AnytimeLower.TailFixedTesting
import ThresholdHC.AnytimeLower.TailAsymptotics
import ThresholdHC.AnytimeLower.TailGeometry
import ThresholdHC.AnytimeLower.Spacing

noncomputable section
open MeasureTheory Real Set Filter
open scoped ENNReal Topology
namespace ThresholdHC.AnytimeLower
open ThresholdHC.Tier3 ThresholdHC.Tier6

/-- Long quarter-drop blocks force the matching lower bound using one
fixed-prefix test inside each block. -/
theorem sparse_tail_matching {R : Type} [MeasurableSpace R]
    (μ : Measure Gap) [IsProbabilityMeasure μ]
    (hI : ¬Integrable (fun d : Gap => (d:ℝ)⁻¹) μ)
    (A : AdaptiveEstimator R) (H : ∀ n, R × Prefix n → ℝ)
    (hH : ∀ n, Measurable (H n))
    {τ ρ δ : ℝ} (hτ : 0 < τ) (hτq : τ ≤ 1/4)
    (hμ : 0 < μ {d : Gap | (d:ℝ) ≤ τ})
    (hrare : μ.real {d : Gap | (d:ℝ) ≤ τ} ≤ ρ)
    (hd : δ ≤ 1/4) (t : ℕ → ℝ) (hacc : OnlineAccuracy μ A H ρ δ t)
    (hsparse : ∃ᶠ k in atTop, sqrt (tailDropIndex μ hτ hμ k:ℝ) ≤
      (tailDropIndex μ hτ hμ (k+1):ℝ)-tailDropIndex μ hτ hμ k)
    (M : ℕ) :
    ∃ n : ℕ, M ≤ n ∧ ENNReal.ofReal (1/512) *
      ThresholdHC.EntropyTail.selection μ ρ ((n:ℝ)/budgetInflation δ n) ≤ ENNReal.ofReal (t n) := by
  let j := tailDropIndex μ hτ hμ
  let N := fun k => sparseBudget τ (j k)
  have hj := (tailDropIndex_strictMono μ hτ hμ).tendsto_atTop
  have hN : Tendsto N atTop atTop := (sparseBudget_tendsto hτ).comp hj
  obtain ⟨h₀,hh₀,hupper⟩ := tail_selection_small_scale μ hI hτ ρ
  have hsmall := (selectedScale_tendsto_zero μ hτ hμ).eventually (gt_mem_nhds hh₀)
  have hscale := hj.eventually (sparse_inflatedScale_bound (δ:=δ) hτ (by linarith))
  obtain ⟨k,hblock,hsk,hjk,hsmallk,hMk⟩ :=
    (hsparse.and_eventually (hscale.and ((hj.eventually (eventually_ge_atTop 64)).and
      (hsmall.and (hN.eventually (eventually_ge_atTop M)))))).exists
  change sqrt (j k:ℝ) ≤ (j (k+1):ℝ)-j k at hblock
  change 0 < N k ∧ 0 < budgetInflation δ (N k) ∧
    inflatedScale δ (N k) ≤ geometricScale τ (j k) at hsk
  have hnp : (0:ℝ) < N k := by exact_mod_cast hsk.1
  have hB : 0 < (N k:ℝ)/budgetInflation δ (N k) := div_pos hnp hsk.2.1
  have hK : ThresholdHC.EntropyTail.selection μ ρ ((N k:ℝ)/budgetInflation δ (N k)) ≤
      ENNReal.ofReal (2*tailMassSequence μ τ (j k)) := by
    have hu := hupper ((N k:ℝ)/budgetInflation δ (N k)) hB
      (hsk.2.2.trans hsmallk.le)
    apply hu.trans (ENNReal.ofReal_le_ofReal _)
    have hp := profileMass_mono μ τ (ThresholdHC.EntropyTailQuantile.budgetScale_nonneg _) hsk.2.2
    change profileMass μ τ (inflatedScale δ (N k)) ≤ tailMassSequence μ τ (j k) at hp
    change 2*profileMass μ τ (inflatedScale δ (N k)) ≤ _
    linarith
  have ht := tail_fixed_radius μ A H hH hτq (geometricScale_pos hτ (sparseIndex (j k)+1)).le
    hrare hd t hacc (N k) ((sparseBudget_scale_upper hτ (by linarith) (j k)).trans_lt
      (by norm_num : (1/8:ℝ) < 1/2))
  have hplateau := tailMassSequence_plateau μ hτ hμ k (sparseIndex (j k)+1)
    (by dsimp [j,sparseIndex]; omega) (sparseIndex_inside hjk hblock)
  change tailMassSequence μ τ (sparseIndex (j k)+1)/64 ≤ t (N k) at ht
  change tailMassSequence μ τ (j k)/4 < tailMassSequence μ τ (sparseIndex (j k)+1) at hplateau
  have hl : tailMassSequence μ τ (j k)/256 ≤ t (N k) := by linarith
  refine ⟨N k,hMk,?_⟩
  calc
    _ ≤ ENNReal.ofReal (1/512)*ENNReal.ofReal (2*tailMassSequence μ τ (j k)) :=
      mul_le_mul_right hK _
    _ = ENNReal.ofReal (tailMassSequence μ τ (j k)/256) := by
      rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/512)]
      congr 1
      ring
    _ ≤ ENNReal.ofReal (t (N k)) := ENNReal.ofReal_le_ofReal hl

end ThresholdHC.AnytimeLower
