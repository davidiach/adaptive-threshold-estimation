import ThresholdHC.PsiGap.Specification
import ThresholdHC.PsiClosedForm.Full
import ThresholdHC.EntropyTailQuantile.BandGeometry
import ThresholdHC.EntropyTailQuantile.CostEntropySeries
import ThresholdHC.EntropyTail.Band

/-! The cost entropy of the quantile core: `Γ_κ = A_κ (1 + E_κ)`.

A finite measure that lives on `d ≥ t` meets only the bands `I_0,…,I_{N-1}`,
where `N ≤ log₂(1/t)`. Its cost entropy is the homogeneous entropy of those
`N` band costs, whose total is the inverse-square cost. Normalizing gives the
factor `1 + E`, and comparing with the uniform law on `N` bands gives
`E ≤ log N`. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace ThresholdHC.PsiGap
open ThresholdHC.Tier6 ThresholdHC.PsiClosedForm
open ThresholdHC.EntropyTailQuantile

/-- The bands met by a finite measure that lives on `d ≥ t`. -/
theorem core_bands (σ : Measure Gap) [IsFiniteMeasure σ] {t : ℝ} (ht : 0 < t)
    (ht2 : t ≤ 1/2) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d : ℝ)) :
    ∃ N : ℕ, 1 ≤ N ∧ (N : ℝ) ≤ Real.logb 2 (1 / t) ∧
      (∀ j, N ≤ j → bandCost σ j = 0) ∧
      Integrable (fun d : Gap => (d : ℝ)⁻¹ ^ 2) σ ∧
      costTotal (fun i : Fin N => bandCost σ i) = ∫ d : Gap, (d : ℝ)⁻¹ ^ 2 ∂σ := by
  obtain ⟨N, hN, hlt⟩ := exists_band_cutoff ht
  have hN1 : 1 ≤ N := by
    by_contra hnot
    have h0 : N = 0 := by omega
    rw [h0] at hN
    have : bandEdge 0 = 1/2 := by norm_num [bandEdge]
    linarith
  have hlog : (N : ℝ) ≤ Real.logb 2 (1 / t) := by
    have hle : t ≤ bandEdge (N - 1) := hlt (N - 1) (by omega)
    have hedge : bandEdge (N - 1) = (2 : ℝ)⁻¹ ^ N := by
      unfold bandEdge
      congr 1
      omega
    rw [hedge] at hle
    have hmul : t * (2 : ℝ) ^ N ≤ 1 := by
      calc t * (2 : ℝ) ^ N ≤ (2 : ℝ)⁻¹ ^ N * (2 : ℝ) ^ N :=
            mul_le_mul_of_nonneg_right hle (by positivity)
        _ = 1 := by rw [← mul_pow]; norm_num
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity), Real.rpow_natCast,
      le_div_iff₀ ht]
    linarith [mul_comm t ((2 : ℝ) ^ N)]
  have hnull (j : ℕ) (hj : N ≤ j) : σ (band j) = 0 := by
    apply measure_mono_null (t := {d : Gap | (d : ℝ) < t})
    · intro d hd
      exact hd.2.trans_lt ((bandEdge_antitone hj).trans_lt hN)
    · simpa only [ae_iff, not_le] using hs
  have hzero (j : ℕ) (hj : N ≤ j) : bandCost σ j = 0 := by
    simp only [bandCost, Measure.restrict_eq_zero.mpr (hnull j hj), integral_zero_measure]
  have hint : Integrable (fun d : Gap => (d : ℝ)⁻¹ ^ 2) σ := by
    refine (integrable_const (t⁻¹ ^ 2)).mono'
      ((measurable_subtype_coe.inv.pow_const 2).aestronglyMeasurable) (hs.mono fun d hd => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (inv_nonneg.2 d.2.1.le) (inv_anti₀ ht hd) 2
  have hmem : ∀ᵐ d : Gap ∂σ, d ∈ ⋃ j ∈ Finset.range N, band j := hs.mono fun d hd => by
    obtain ⟨j, hj⟩ := ThresholdHC.EntropyTail.exists_band d
    rw [← ThresholdHC.EntropyTail.quantile_band_eq j] at hj
    have hjN : j < N := by
      by_contra hnot
      have : (d : ℝ) < t := hj.2.trans_lt ((bandEdge_antitone (not_lt.1 hnot)).trans_lt hN)
      linarith
    exact Set.mem_iUnion₂.2 ⟨j, Finset.mem_range.2 hjN, hj⟩
  have htot : costTotal (fun i : Fin N => bandCost σ i) = ∫ d : Gap, (d : ℝ)⁻¹ ^ 2 ∂σ := by
    unfold costTotal
    rw [Fin.sum_univ_eq_sum_range (fun j => bandCost σ j) N]
    unfold bandCost
    rw [← integral_biUnion_finset (Finset.range N) (fun j _ => measurableSet_band j)
      (fun i _ j _ hij => bands_disjoint hij) (fun j _ => hint.integrableOn),
      Measure.restrict_eq_self_of_ae_mem hmem]
  exact ⟨N, hN1, hlog, hzero, hint, htot⟩

/-- The cost entropy of a nonzero finite measure on `d ≥ t`, normalized. -/
theorem core_entropy_real (σ : Measure Gap) [IsFiniteMeasure σ] {t : ℝ} (ht : 0 < t)
    (ht2 : t ≤ 1/2) (hs : ∀ᵐ d : Gap ∂σ, t ≤ (d : ℝ)) (hσ : σ univ ≠ 0) :
    ∃ A E : ℝ, 0 < A ∧ 0 ≤ E ∧ inverseSquareCost σ = ENNReal.ofReal A ∧
      E = ∑' j : ℕ, Real.negMulLog (bandCost σ j / A) ∧
      measureCostEntropy σ = ENNReal.ofReal (A * (1 + E)) ∧
      E ≤ Real.log (Real.logb 2 (1 / t)) := by
  obtain ⟨N, hN1, hlog, hzero, hint, htot⟩ := core_bands σ ht ht2 hs
  set a : Fin N → ℝ := fun i => bandCost σ i with ha
  have ha0 : ∀ i, 0 ≤ a i := fun i => bandCost_nonneg σ i
  have hApos : 0 < ∫ d : Gap, (d : ℝ)⁻¹ ^ 2 ∂σ := by
    have hreal : 0 < σ.real univ := ENNReal.toReal_pos hσ (measure_ne_top σ _)
    have hmono : ∫ _d : Gap, (4 : ℝ) ∂σ ≤ ∫ d : Gap, (d : ℝ)⁻¹ ^ 2 ∂σ :=
      integral_mono (integrable_const _) hint fun d => by
        have h2 : (2 : ℝ) ≤ (d : ℝ)⁻¹ := by
          rw [le_inv_comm₀ (by norm_num) d.2.1]
          have := d.2.2
          norm_num at this ⊢
          exact this
        show (4 : ℝ) ≤ (d : ℝ)⁻¹ ^ 2
        nlinarith
    rw [integral_const, smul_eq_mul] at hmono
    nlinarith
  have hA : costTotal a = ∫ d : Gap, (d : ℝ)⁻¹ ^ 2 ∂σ := htot
  have hinv : inverseSquareCost σ = ENNReal.ofReal (∫ d : Gap, (d : ℝ)⁻¹ ^ 2 ∂σ) := by
    unfold inverseSquareCost
    exact (ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun d => sq_nonneg _)).symm
  have hsum : ∑' j : ℕ, Real.negMulLog (bandCost σ j / (∫ d : Gap, (d : ℝ)⁻¹ ^ 2 ∂σ)) =
      ∑ i : Fin N, Real.negMulLog (a i / costTotal a) := by
    rw [tsum_eq_sum (s := Finset.range N) (fun j hj => by
      rw [hzero j (not_lt.1 (fun h => hj (Finset.mem_range.2 h)))]
      simp), hA]
    exact (Fin.sum_univ_eq_sum_range
      (fun j => Real.negMulLog (bandCost σ j / (∫ d : Gap, (d : ℝ)⁻¹ ^ 2 ∂σ))) N).symm
  have hAa : 0 < costTotal a := hA ▸ hApos
  have hE0 : 0 ≤ ∑ i : Fin N, Real.negMulLog (a i / costTotal a) :=
    Finset.sum_nonneg fun i _ => Real.negMulLog_nonneg (div_nonneg (ha0 i) hAa.le)
      ((div_le_one hAa).2 (le_costTotal ha0 i))
  have hnorm := costEntropy_normalized hAa
  have hgamma : measureCostEntropy σ = ENNReal.ofReal (costEntropy a) := by
    unfold measureCostEntropy
    refine le_antisymm (iSup_le fun n => ENNReal.ofReal_le_ofReal
      (costEntropy_prefix_le_of_eventually_zero (bandCost_nonneg σ) hzero n)) ?_
    exact le_iSup (fun n : ℕ => ENNReal.ofReal (costEntropy fun j : Fin n => bandCost σ j.val)) N
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hEN : ∑ i : Fin N, Real.negMulLog (a i / costTotal a) ≤ Real.log N := by
    have href := costEntropy_le_reference (p := fun _ : Fin N => (N : ℝ)⁻¹) ha0
      (fun _ => inv_pos.2 hNpos) (by simp [hNpos.ne'])
    have hrhs : ∑ i : Fin N, a i * (1 - Real.log (N : ℝ)⁻¹) =
        costTotal a * (1 + Real.log N) := by
      rw [← Finset.sum_mul, Real.log_inv]
      unfold costTotal
      ring
    rw [hrhs, hnorm] at href
    have := le_of_mul_le_mul_left href hAa
    linarith
  refine ⟨∫ d : Gap, (d : ℝ)⁻¹ ^ 2 ∂σ, ∑ i : Fin N, Real.negMulLog (a i / costTotal a),
    hApos, hE0, hinv, hsum.symm, ?_, hEN.trans (Real.log_le_log hNpos hlog)⟩
  rw [hgamma, hnorm, hA]

end ThresholdHC.PsiGap
