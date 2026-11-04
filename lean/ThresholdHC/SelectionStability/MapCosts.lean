import ThresholdHC.SelectionStability.Specification
import ThresholdHC.EntropyTail.HardSelection

noncomputable section
open MeasureTheory Set Real
open scoped ENNReal
namespace ThresholdHC.SelectionStability
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTail

/-- Coordinatewise domination scales the prefix supremum, including infinite entropy. -/
theorem gamma_le_scaled {σ τ : Measure Gap} [IsFiniteMeasure σ] [IsFiniteMeasure τ]
    {a : ℝ} (ha : 0 ≤ a) (hc : ∀ j, bandCost σ j ≤ ENNReal.ofReal a * bandCost τ j) :
    gamma σ ≤ ENNReal.ofReal a * gamma τ := by
  rw [gamma_eq_iSup σ]
  apply iSup_le
  intro J
  let v := fun j : Fin (J+1) => (bandCost τ j).toReal
  have hcoord (j : Fin (J+1)) : (bandCost σ j).toReal ≤ (a • v) j := by
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (bandCost_ne_top τ j)) (hc j)
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal ha, Pi.smul_apply, smul_eq_mul, v] using h
  have hp := costEntropy_mono (fun j : Fin (J+1) => ENNReal.toReal_nonneg (a := bandCost σ j)) hcoord
  rw [costEntropy_smul v ha] at hp
  calc
    _ ≤ ENNReal.ofReal (a * prefixEntropy τ J) := ENNReal.ofReal_le_ofReal hp
    _ ≤ _ := by rw [ENNReal.ofReal_mul ha]; exact mul_le_mul_right (ofReal_prefixEntropy_le_gamma τ J) _

/-- Compare both kernels before integration. The factor is squared only for inverse-square cost. -/
theorem rounding_kernels {x y : Gap} {r h : ℝ} (hr : 1 ≤ r) (hh : 0 ≤ h)
    (hxy : (x:ℝ) ≤ (y:ℝ)) (hy : (y:ℝ) ≤ r*(x:ℝ)) :
    (y:ℝ)⁻¹^2 ≤ (x:ℝ)⁻¹^2 ∧ (x:ℝ)⁻¹^2 ≤ r^2 * (y:ℝ)⁻¹^2 ∧
    min 1 (h/(y:ℝ)) ≤ min 1 (h/(x:ℝ)) ∧ min 1 (h/(x:ℝ)) ≤ r * min 1 (h/(y:ℝ)) := by
  have hr0 : 0 ≤ r := zero_le_one.trans hr
  have h₁ := inv_anti₀ x.property.1 hxy
  have h₂ : (x:ℝ)⁻¹ ≤ r*(y:ℝ)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ y.property.1]
    rw [inv_mul_eq_div, div_le_iff₀ x.property.1]
    exact hy
  refine ⟨pow_le_pow_left₀ (inv_nonneg.mpr y.property.1.le) h₁ 2, ?_, ?_, ?_⟩
  · simpa only [mul_pow] using pow_le_pow_left₀ (inv_nonneg.mpr x.property.1.le) h₂ 2
  · exact min_le_min_left _ (div_le_div_of_nonneg_left hh x.property.1 hxy)
  · rw [mul_min_of_nonneg _ _ hr0,mul_one]
    apply le_min ((min_le_left _ _).trans hr)
    apply (min_le_right _ _).trans
    simpa only [div_eq_mul_inv, mul_left_comm] using mul_le_mul_of_nonneg_left h₂ hh

/-- Integrated cost bounds for a measurable, band-preserving map. -/
theorem map_costs (σ : Measure Gap) (T : Gap → Gap) (hm : Measurable T)
    {r h : ℝ} (hr : 1 ≤ r) (hh : 0 ≤ h)
    (hd : ∀ d : Gap, (d:ℝ) ≤ (T d:ℝ) ∧ (T d:ℝ) ≤ r*(d:ℝ))
    (hb : ∀ j, T ⁻¹' band j = band j) :
    (∀ j, bandCost (σ.map T) j ≤ bandCost σ j ∧
      bandCost σ j ≤ ENNReal.ofReal (r^2) * bandCost (σ.map T) j) ∧
    tailCost (σ.map T) h ≤ tailCost σ h ∧ tailCost σ h ≤ ENNReal.ofReal r * tailCost (σ.map T) h := by
  have H (d : Gap) := rounding_kernels hr hh (hd d).1 (hd d).2
  have hr0 : 0 ≤ r := zero_le_one.trans hr
  constructor
  · intro j
    unfold bandCost
    rw [Measure.restrict_map hm (measurableSet_band j), hb j, lintegral_map (by fun_prop) hm]
    refine ⟨lintegral_mono (fun d => ENNReal.ofReal_le_ofReal (H d).1), ?_⟩
    rw [← lintegral_const_mul _ (by fun_prop)]
    exact lintegral_mono (fun d => (ENNReal.ofReal_le_ofReal (H d).2.1).trans_eq
      (ENNReal.ofReal_mul (sq_nonneg r)))
  · unfold tailCost
    rw [lintegral_map (measurable_tailWeight h) hm]
    refine ⟨lintegral_mono (fun d => ENNReal.ofReal_le_ofReal (H d).2.2.1), ?_⟩
    rw [← lintegral_const_mul _ (f := fun d : Gap => ENNReal.ofReal (min 1 (h/(T d:ℝ)))) (by fun_prop)]
    exact lintegral_mono (fun d => (ENNReal.ofReal_le_ofReal (H d).2.2.2).trans_eq
      (ENNReal.ofReal_mul hr0))

end ThresholdHC.SelectionStability
