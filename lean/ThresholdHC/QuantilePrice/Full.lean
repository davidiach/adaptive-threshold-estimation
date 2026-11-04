import ThresholdHC.QuantilePrice.Weights
import ThresholdHC.QuantilePrice.Scalar
import ThresholdHC.QuantileSelection.Full

noncomputable section
open MeasureTheory Real Set
open scoped ENNReal
namespace ThresholdHC.QuantilePrice
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTailQuantile

theorem separated_cost (Z : Measure Gap) [IsFiniteMeasure Z] {t : ℝ} (ht : 0 < t)
    (hs : ∀ᵐ d : Gap ∂Z, t ≤ (d:ℝ)) :
    measureCostEntropy Z ≤ ENNReal.ofReal (((16/9)/t)*∫ d : Gap, (d:ℝ)⁻¹ ∂Z) :=
  QuantileSelection.separated_cost_of_weights (16/9) (by norm_num) weight weight_pos weight_mass
    (@weight_band) Z ht hs

private theorem core_interaction (V Z : Measure Gap) [IsFiniteMeasure V] [IsFiniteMeasure Z]
    {t : ℝ} (ht : 0 < t) (hV : ∀ᵐ d : Gap ∂V, t ≤ (d:ℝ)) (hZ : ∀ᵐ d : Gap ∂Z, t ≤ (d:ℝ)) :
    (measureCostEntropy (V+Z)).toReal ≤ (measureCostEntropy V).toReal+(measureCostEntropy Z).toReal+
      (111/80)*sqrt ((measureCostEntropy V).toReal*(measureCostEntropy Z).toReal) := by
  obtain ⟨N,hN,_⟩ := exists_band_cutoff ht
  rw [measureCostEntropy_eq_prefix_of_support _ (ae_add_measure_iff.mpr ⟨hV,hZ⟩) hN,
    measureCostEntropy_eq_prefix_of_support _ hV hN, measureCostEntropy_eq_prefix_of_support _ hZ hN]
  simp only [bandCost_add]
  let a : Fin N → ℝ := fun i => bandCost V i
  let b : Fin N → ℝ := fun i => bandCost Z i
  have ha (i) : 0 ≤ a i := bandCost_nonneg _ _
  have hb (i) : 0 ≤ b i := bandCost_nonneg _ _
  change (ENNReal.ofReal (costEntropy (fun i => a i+b i))).toReal ≤ _
  rw [ENNReal.toReal_ofReal (costEntropy_nonneg (fun i => add_nonneg (ha i) (hb i)))]
  change _ ≤ (ENNReal.ofReal (costEntropy a)).toReal+(ENNReal.ofReal (costEntropy b)).toReal+
    (111/80)*sqrt ((ENNReal.ofReal (costEntropy a)).toReal*(ENNReal.ofReal (costEntropy b)).toReal)
  rw [ENNReal.toReal_ofReal (costEntropy_nonneg ha),ENNReal.toReal_ofReal (costEntropy_nonneg hb)]
  have h := (QuantileSelection.entropy_interaction a b ha hb).1
  have hs : sqrt (costTotal a*costTotal b) ≤ sqrt (costEntropy a*costEntropy b) :=
    sqrt_le_sqrt (mul_le_mul (costTotal_le_costEntropy ha) (costTotal_le_costEntropy hb)
      (costTotal_nonneg hb) (costEntropy_nonneg ha))
  apply h.trans
  apply add_le_add_right
  exact mul_le_mul (by linarith [log_two_lt_d9] : 2*log 2 ≤ 111/80) hs (sqrt_nonneg _) (by norm_num)

private theorem core_price {q V Z C T c : ℝ} (hq : 0 ≤ q) (hV : 0 ≤ V) (hZ : 0 ≤ Z)
    (hT : 0 ≤ T) (hc : 0 ≤ c) (hint : C ≤ V+Z+(111/80)*sqrt (V*Z))
    (hwork : q*Z ≤ (16/9)*T*c) :
    T + sqrt (q*C) ≤ (31/20)*(sqrt (T^2+(sqrt (q*V))^2)+c) := by
  let v := sqrt (q*V)
  let u := sqrt (q*Z)
  let z := sqrt (T*c)
  have hv : 0 ≤ v := sqrt_nonneg _
  have hu : 0 ≤ u := sqrt_nonneg _
  have hz : 0 ≤ z := sqrt_nonneg _
  have hv2 : v^2=q*V := sq_sqrt (mul_nonneg hq hV)
  have hu2 : u^2=q*Z := sq_sqrt (mul_nonneg hq hZ)
  have hz2 : z^2=T*c := sq_sqrt (mul_nonneg hT hc)
  have he : q*sqrt (V*Z) = v*u := by
    apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow,mul_pow,sq_sqrt (mul_nonneg hV hZ),hv2,hu2]; ring
  have hU : u ≤ (4/3)*z := (sq_le_sq₀ hu (by positivity)).mp (by nlinarith only [hu2,hz2,hwork])
  have hi := mul_le_mul_of_nonneg_left hint hq
  have hrad : q*C ≤ (v+37/40*z)^2+(77/80*z)^2 := by
    have hx := mul_le_mul_of_nonneg_left hU hv
    have he' : q*((111/80)*sqrt (V*Z)) = (111/80)*(v*u) := by rw [← he]; ring
    rw [mul_add,mul_add,he'] at hi
    nlinarith only [hi,hwork,hv2,hz2,hx,sq_nonneg z]
  exact (add_le_add_right (sqrt_le_sqrt hrad) T).trans (scalar_price T v c hT hv hc)

/-- The sharper comparison on the original minimax selection functional. -/
theorem quantile_le_31_20_selection (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B : ℝ} (hρ : 0 < ρ) (hρ4 : ρ ≤ 1/4) (hB : 0 < B) :
    ThresholdHC.EntropyTail.selection μ ρ B ≤ closedQuantileValue μ ρ B ∧
    closedQuantileValue μ ρ B ≤ ENNReal.ofReal (31/20)*ThresholdHC.EntropyTail.selection μ ρ B := by
  rw [← ThresholdHC.EntropyTail.quantile_selectionValue_eq μ ρ B]
  have hρ1 : ρ ≤ 1 := by linarith
  refine ⟨selectionValue_le_closedQuantileValue μ hρ hρ1 B,?_⟩
  have hf : (1:ℝ≥0∞) ≤ ENNReal.ofReal (31/20) := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by norm_num)
  have hpos := ne_of_gt (lt_of_lt_of_le zero_lt_one hf)
  by_cases ht : quantileThreshold μ ρ ≤ budgetScale B
  · obtain ⟨hk,hQ⟩ := quantile_saturation μ hρ hρ1 ht
    rw [hk,hQ]; simpa only [one_mul] using mul_le_mul_left hf (ENNReal.ofReal ρ)
  unfold selectionValue
  rw [mul_min]
  refine le_min ((min_le_left _ _).trans ?_) ?_
  · simpa only [one_mul] using mul_le_mul_left hf (ENNReal.ofReal ρ)
  · rw [ENNReal.mul_iInf_of_ne hpos ENNReal.ofReal_ne_top]
    apply le_iInf
    intro σ
    rw [ENNReal.mul_iInf_of_ne hpos ENNReal.ofReal_ne_top]
    apply le_iInf
    intro hσ
    apply QuantileSelection.comparison_pointwise_of_price (16/9) (31/20) (by norm_num) (by norm_num)
      (fun Z _ _ ht hs => separated_cost Z ht hs) _ μ hρ hρ1 hB (lt_of_not_ge ht) σ hσ
    intro V Z _ _ t q T c ht hV hZ hq hT hc hwork
    exact core_price hq ENNReal.toReal_nonneg ENNReal.toReal_nonneg hT hc
      (core_interaction V Z ht hV hZ) hwork

end ThresholdHC.QuantilePrice
