import ThresholdHC.UnknownRarity.Specification
import ThresholdHC.Tier6.RiskReduction

/-! Risk arithmetic for the unknown-rarity obstruction.

At `θ = 0` the displayed bound is at most `max C 0 · ρ` for every `ρ`, so the
RMS error vanishes and the output is zero almost surely. Zero output has RMS
error `1/4` at `θ = 1/4`, while the displayed bound at `ρ = θ = 1/4` is below
`1/4` once `B > 4C²/d²`. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.UnknownRarity
open ThresholdHC.Tier6

/-- The displayed bound is at most the linear bound `max C 0 · ρ`. -/
theorem bound_le_linear (C ρ d B : ℝ) (hρ : 0 ≤ ρ) (hd : 0 < d) :
    C * min ρ (Real.sqrt ρ / (d * Real.sqrt B)) ≤ max C 0 * ρ := by
  have hm0 : 0 ≤ min ρ (Real.sqrt ρ / (d * Real.sqrt B)) :=
    le_min hρ (div_nonneg (Real.sqrt_nonneg _) (mul_nonneg hd.le (Real.sqrt_nonneg _)))
  have hm : min ρ (Real.sqrt ρ / (d * Real.sqrt B)) ≤ ρ := min_le_left _ _
  calc C * min ρ (Real.sqrt ρ / (d * Real.sqrt B))
      ≤ max C 0 * min ρ (Real.sqrt ρ / (d * Real.sqrt B)) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hm0
    _ ≤ max C 0 * ρ := mul_le_mul_of_nonneg_left hm (le_max_right _ _)

/-- An extended real bounded by `c ρ` for every `ρ ∈ (0,1/4]` is zero. -/
theorem eq_zero_of_le_linear (x : ℝ≥0∞) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1/4 → x ≤ ENNReal.ofReal (c * ρ)) : x = 0 := by
  have htop : x ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h (1/4) (by norm_num) le_rfl)
  have hreal : ∀ ε : ℝ, 0 < ε → x.toReal ≤ 0 + ε := by
    intro ε hε
    have hc1 : 0 < c + 1 := by linarith
    have hρ0 : 0 < min (1/4 : ℝ) (ε / (c + 1)) := lt_min (by norm_num) (div_pos hε hc1)
    have hρ1 : min (1/4 : ℝ) (ε / (c + 1)) ≤ 1/4 := min_le_left _ _
    have hρ2 : min (1/4 : ℝ) (ε / (c + 1)) ≤ ε / (c + 1) := min_le_right _ _
    have hx := h _ hρ0 hρ1
    have hx' : x.toReal ≤ c * min (1/4 : ℝ) (ε / (c + 1)) := by
      have hh := (ENNReal.toReal_le_toReal htop ENNReal.ofReal_ne_top).2 hx
      rwa [ENNReal.toReal_ofReal (mul_nonneg hc hρ0.le)] at hh
    have hce : c * (ε / (c + 1)) ≤ ε := by
      rw [mul_div_assoc', div_le_iff₀ hc1]
      nlinarith
    have hcm := mul_le_mul_of_nonneg_left hρ2 hc
    linarith
  have h0 : x.toReal ≤ 0 := le_of_forall_pos_le_add hreal
  have hx0 : x.toReal = 0 := le_antisymm h0 ENNReal.toReal_nonneg
  rcases (ENNReal.toReal_eq_zero_iff x).1 hx0 with hz | hz
  · exact hz
  · exact absurd hz htop

/-- Zero RMS error at target `0` forces zero output almost surely. -/
theorem output_zero_of_rms_zero {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (f : Ω → ℝ)
    (hf : Measurable f) (h : rootMeanRisk P f 0 = 0) : ∀ᵐ x ∂P, f x = 0 := by
  unfold rootMeanRisk at h
  rw [ENNReal.rpow_eq_zero_iff] at h
  have hsq : squaredRisk P f 0 = 0 := by
    rcases h with h | h
    · exact h.1
    · norm_num at h
  unfold squaredRisk at hsq
  have hm : Measurable (fun x => ENNReal.ofReal ((f x - 0)^2)) :=
    ENNReal.measurable_ofReal.comp ((hf.sub_const 0).pow_const 2)
  rw [lintegral_eq_zero_iff hm] at hsq
  filter_upwards [hsq] with x hx
  simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero, sub_zero] at hx
  exact (pow_eq_zero_iff two_ne_zero).1 (le_antisymm hx (sq_nonneg _))

/-- Zero output almost surely has RMS error `a` at a target `a ≥ 0`. -/
theorem rms_of_output_zero {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (f : Ω → ℝ) (h : ∀ᵐ x ∂P, f x = 0) (a : ℝ) (ha : 0 ≤ a) :
    rootMeanRisk P f a = ENNReal.ofReal a := by
  unfold rootMeanRisk squaredRisk
  have hc : (fun x => ENNReal.ofReal ((f x - a)^2)) =ᵐ[P] fun _ => ENNReal.ofReal (a^2) := by
    filter_upwards [h] with x hx
    rw [hx, zero_sub, neg_sq]
  rw [lintegral_congr_ae hc, lintegral_const, measure_univ, mul_one,
    ofReal_square_rpow_half a ha]

/-- The displayed bound at `ρ = 1/4` is below `1/4` once `B > 4C²/d²`. -/
theorem bound_quarter_lt (d C B : ℝ) (hd : 0 < d) (hB : 4 * C^2 / d^2 < B) :
    ¬ ENNReal.ofReal (1/4) ≤
      ENNReal.ofReal (C * min (1/4) (Real.sqrt (1/4) / (d * Real.sqrt B))) := by
  intro h
  rw [ENNReal.ofReal_le_ofReal_iff'] at h
  have h' : (1/4 : ℝ) ≤ C * min (1/4) (Real.sqrt (1/4) / (d * Real.sqrt B)) := by
    rcases h with h | h
    · exact h
    · norm_num at h
  have hs : Real.sqrt (1/4) = 1/2 := by
    rw [show (1/4 : ℝ) = (1/2)^2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [hs] at h'
  have hm0 : 0 ≤ min (1/4 : ℝ) (1/2 / (d * Real.sqrt B)) :=
    le_min (by norm_num) (div_nonneg (by norm_num) (mul_nonneg hd.le (Real.sqrt_nonneg _)))
  rcases le_or_gt C 0 with hC | hC
  · nlinarith [mul_nonpos_of_nonpos_of_nonneg hC hm0]
  · have hsq : 2 * C / d < Real.sqrt B := by
      rw [Real.lt_sqrt (by positivity)]
      calc (2 * C / d)^2 = 4 * C^2 / d^2 := by ring
        _ < B := hB
    have hdB : 2 * C < d * Real.sqrt B := by
      rw [div_lt_iff₀ hd] at hsq
      linarith
    have hpos : 0 < d * Real.sqrt B := by linarith
    have hm : min (1/4 : ℝ) (1/2 / (d * Real.sqrt B)) ≤ 1/2 / (d * Real.sqrt B) :=
      min_le_right _ _
    have hlt : C * (1/2 / (d * Real.sqrt B)) < 1/4 := by
      rw [mul_div_assoc', div_lt_iff₀ hpos]
      linarith
    nlinarith [mul_le_mul_of_nonneg_left hm hC.le]

end ThresholdHC.UnknownRarity
