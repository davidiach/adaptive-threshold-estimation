import ThresholdHC.SmoothDensity.Representation
import ThresholdHC.SmoothDensity.Information
import ThresholdHC.SmoothDensity.Scale

noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal
namespace ThresholdHC.SmoothDensity
open ThresholdHC.Tier6 ThresholdHC.Confidence

/-- Uniform work and confidence are required only on members of the smooth class. -/
def FitsClass {R : Type} [MeasurableSpace R] (s : ℕ) (M B ε δ : ℝ)
    (A : AdaptiveEstimator R) : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw),
    SmoothModel s M μ q →
      expectedWork μ A q ≤ ENNReal.ofReal B ∧
        failureProbability μ A q ε ≤ ENNReal.ofReal δ

theorem smoothModel_mono {s : ℕ} {M N : ℝ} {μ : Measure Gap} {q : SignLaw}
    (h : SmoothModel s M μ q) (hMN : M ≤ N) : SmoothModel s N μ q := by
  obtain ⟨f,hs,hn,hp,hi,hb,hr⟩ := h
  exact ⟨f,hs,hn,hp,hi,fun k hk p => (hb k hk p).trans hMN,hr⟩

/-- The logarithmic lower complexity holds uniformly over all adaptive
estimators, including randomized policies with unbounded stopping times. -/
theorem smooth_confidence_lower (s : ℕ) :
    ∃ M₀ c ε₀ : ℝ, 0 < M₀ ∧ 0 < c ∧ 0 < ε₀ ∧
      ∀ (M B ε δ : ℝ), M₀ ≤ M → 0 < ε → ε ≤ ε₀ → 0 < δ → δ ≤ 1 / 4 →
      ∀ (R : Type) [MeasurableSpace R] (A : AdaptiveEstimator R),
        FitsClass s M B ε δ A →
          c * (ε ^ 2)⁻¹ * (Real.log (1 / ε)) ^ 2 * Real.log (1 / δ) ≤ B := by
  obtain ⟨M₀,hM₀,hpair⟩ := smooth_pair_in_class s
  let c := 225 / (512 * (scaleConstant s) ^ 2)
  refine ⟨M₀,c,radiusCutoff s,hM₀,?_,radiusCutoff_pos s,?_⟩
  · dsimp [c]
    exact div_pos (by norm_num) (mul_pos (by norm_num) (sq_pos_of_pos (scaleConstant_pos s)))
  intro M B ε δ hM hε he hδ hd R _ A hA
  obtain ⟨t,ht,ht1,hpow,hsep⟩ := choose_smooth_scale s hε he
  have ht' : t ≤ 1 := by linarith
  let qp := smoothSign s ht ht' true
  let qm := smoothSign s ht ht' false
  obtain ⟨hw,hcp⟩ := hA smoothGapLaw qp (smoothModel_mono (hpair t ht ht' true) hM)
  obtain ⟨_,hcm⟩ := hA smoothGapLaw qm (smoothModel_mono (hpair t ht ht' false) hM)
  have hcost := local_pair_confidence_cost smoothGapLaw A
    (fun d => perturbation s t d)
    ((perturbation_contDiff s t).continuous.measurable.comp measurable_subtype_coe)
    (fun d => ⟨perturbation_nonneg s ht.le d.property.1.le,
      (le_abs_self _).trans (perturbation_abs_le s ht.le ht' d)⟩)
    qp qm (fun d => by simp [qp,smoothSign]) (fun d => by simp [qm,smoothSign,sub_eq_add_neg])
    B (t ^ (s + 1)) ε δ (pow_pos ht _)
    (fun d => gap_mul_perturbation_le s ht d) hw hδ hd
    (hsep.trans_le (smoothSign_separation s ht ht1)) hcp hcm
  rw [hpow] at hcost
  have hL : 0 < Real.log (1 / ε) := by
    have hh : 0 < scaleConstant s * ε / Real.log (1 / ε) := hpow ▸ pow_pos ht _
    exact (div_pos_iff.mp hh).resolve_right (by
      intro h
      exact (not_lt_of_ge (mul_nonneg (scaleConstant_pos s).le hε.le)) h.1) |>.2
  have hden : 0 < 512 * (scaleConstant s) ^ 2 * ε ^ 2 := by
    exact mul_pos (mul_pos (by norm_num) (sq_pos_of_pos (scaleConstant_pos s))) (sq_pos_of_pos hε)
  have hK := scaleConstant_pos s
  change 225 / (512 * scaleConstant s ^ 2) * (ε ^ 2)⁻¹ * Real.log (1 / ε) ^ 2 * Real.log (1 / δ) ≤ B
  field_simp
  have hscaled := mul_le_mul_of_nonneg_left hcost (show 0 ≤ 900 * Real.log (1 / ε) ^ 2 by positivity)
  field_simp at hscaled
  nlinarith

end ThresholdHC.SmoothDensity
