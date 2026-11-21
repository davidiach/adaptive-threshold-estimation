import ThresholdHC.MarginClasses.Basic

/-! The gap class `𝒢_Δ` (Corollary `cor:gap`): it is the envelope class of the
point mass at `Δ`, whose modulus is `min 1 (h/Δ)`; the envelope confidence law
is inverted directly. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.MarginClasses
open ThresholdHC.Tier6 ThresholdHC.Confidence ThresholdHC.Envelope

/-- Every law of the gap class lies below the point mass at `Δ`. -/
theorem gapClass_within {Δ : ℝ} (hΔ : 0 < Δ) (hΔ' : Δ ≤ 1/2) (ν : Measure Gap)
    [IsProbabilityMeasure ν] (h : GapClass Δ ν) :
    Within (Measure.dirac (⟨Δ,hΔ,hΔ'⟩ : Gap)) ν := by
  intro t ht
  by_cases htΔ : t < Δ
  · have h0 : ν {d : Gap | (d:ℝ) ≤ t} = 0 :=
      measure_mono_null (fun d hd => lt_of_le_of_lt hd htΔ) h
    rw [h0]
    exact bot_le
  · have hm : (⟨Δ,hΔ,hΔ'⟩ : Gap) ∈ {d : Gap | (d:ℝ) ≤ t} := le_of_not_gt htΔ
    rw [Measure.dirac_apply_of_mem hm]
    exact prob_le_one

/-- The point mass at `Δ` lies in the gap class. -/
theorem dirac_gapClass {Δ : ℝ} (hΔ : 0 < Δ) (hΔ' : Δ ≤ 1/2) :
    GapClass Δ (Measure.dirac (⟨Δ,hΔ,hΔ'⟩ : Gap)) := by
  have hm : MeasurableSet {d : Gap | (d:ℝ) < Δ} :=
    measurableSet_lt measurable_subtype_coe measurable_const
  have hn : (⟨Δ,hΔ,hΔ'⟩ : Gap) ∉ {d : Gap | (d:ℝ) < Δ} := fun h => lt_irrefl Δ h
  rw [GapClass,Measure.dirac_apply' _ hm,Set.indicator_of_notMem hn]

/-- A witness valid at accuracy `ε ≤ 1/25` at a point mass `g` has budget at
least `(15/(256√2))^2 log(1/δ)/(ε^2 g^2)`. -/
theorem dirac_lower {R : Type} [MeasurableSpace R] (g : Gap) (A : AdaptiveEstimator R)
    {B ε δ : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1/25) (hδ : 0 < δ) (hδ' : δ ≤ 1/4)
    (hw : UniformBudget (Measure.dirac g) A B) (hc : UniformConfidence (Measure.dirac g) A ε δ) :
    225/131072 * Real.log (1/δ) / (ε^2 * (g:ℝ)^2) ≤ B := by
  obtain ⟨hB,h⟩ := witness_lower _ A hε hε' hδ hδ' hw hc
  rw [modulus_dirac] at h
  have hB0 : 0 < B := by linarith
  have hsq := scale_sq hB0 hδ hδ'
  have hs0 : 0 ≤ confidenceScale B δ := Real.sqrt_nonneg _
  have hg := g.property.1
  have hc0 := cutoff_lt
  have hk := lower_const_sq
  have hcp : 0 < 15/(256*Real.sqrt 2) := by positivity
  rcases min_cases 1 (confidenceScale B δ/(g:ℝ)) with ⟨h1,_⟩ | ⟨h1,_⟩
  · rw [h1,mul_one] at h
    linarith
  · rw [h1,← mul_div_assoc,div_le_iff₀ hg] at h
    have h3 : (15/(256*Real.sqrt 2)*confidenceScale B δ)^2 ≤ (ε*g)^2 :=
      pow_le_pow_left₀ (by positivity) h 2
    rw [div_le_iff₀ (by positivity)]
    calc 225/131072 * Real.log (1/δ)
        = (15/(256*Real.sqrt 2))^2 * ((confidenceScale B δ)^2 * B) := by rw [hsq,hk]
      _ = (15/(256*Real.sqrt 2)*confidenceScale B δ)^2 * B := by ring
      _ ≤ (ε*g)^2 * B := mul_le_mul_of_nonneg_right h3 hB0.le
      _ = B * (ε^2 * (g:ℝ)^2) := by ring

/-- Lower half of Corollary `cor:gap`. -/
theorem gap_lower {Δ ε δ : ℝ} (hΔ : 0 < Δ) (hΔ' : Δ ≤ 1/2) (hε : 0 < ε) (hε' : ε ≤ 1/25)
    (hδ : 0 < δ) (hδ' : δ ≤ 1/4) :
    ENNReal.ofReal (225/131072 * Real.log (1/δ) / (ε^2 * Δ^2)) ≤ classWork (GapClass Δ) ε δ := by
  apply le_sInf
  rintro t ⟨R,mR,A,B,hA,rfl⟩
  obtain ⟨hw,hc⟩ := hA (Measure.dirac (⟨Δ,hΔ,hΔ'⟩ : Gap)) (dirac_gapClass hΔ hΔ')
  exact ENNReal.ofReal_le_ofReal (dirac_lower ⟨Δ,hΔ,hΔ'⟩ A hε hε' hδ hδ' hw hc)

/-- The upper budget of Corollary `cor:gap` is at least one, and at it the
reference modulus at the confidence scale is at most `ε/8192`. -/
theorem gap_scale {Δ ε δ : ℝ} (hΔ : 0 < Δ) (hΔ' : Δ ≤ 1/2) (hε : 0 < ε) (hε' : ε ≤ 1/25)
    (hδ : 0 < δ) (hδ' : δ ≤ 1/4) :
    1 ≤ 67108864 * Real.log (1/δ) / (ε^2 * Δ^2) ∧
      8192 * modulus (Measure.dirac (⟨Δ,hΔ,hΔ'⟩ : Gap))
        (confidenceScale (67108864 * Real.log (1/δ) / (ε^2 * Δ^2)) δ) ≤ ε := by
  have hL := log_ge hδ hδ'
  have hx : 0 < ε*Δ/8192 := by positivity
  have hB : 67108864 * Real.log (1/δ) / (ε^2 * Δ^2) * (ε*Δ/8192)^2 = Real.log (1/δ) := by
    field_simp
    ring
  refine ⟨?_,?_⟩
  · rw [le_div_iff₀ (by positivity)]
    have h1 : ε^2 ≤ 1 := by nlinarith
    have h2 : Δ^2 ≤ 1 := by nlinarith
    have h3 : ε^2*Δ^2 ≤ 1 := by nlinarith [sq_nonneg ε,sq_nonneg Δ]
    nlinarith
  · rw [scale_eq hδ hδ' hx hB,modulus_dirac]
    have h1 : ε*Δ/8192/((⟨Δ,hΔ,hΔ'⟩ : Gap) : ℝ) = ε/8192 := by
      change ε*Δ/8192/Δ = ε/8192
      field_simp
    rw [h1,min_eq_right (by linarith)]
    linarith

end ThresholdHC.MarginClasses
