import ThresholdHC.SmoothDensity.Representation
import ThresholdHC.SmoothDensity.SymmetricInformation
import ThresholdHC.UnbiasedConverse.TwoPoint

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
namespace ThresholdHC.SmoothDensity
open ThresholdHC.Tier6 ThresholdHC.UnbiasedConverse

/-- Finite variance and work are uniform over the smooth class, and the
integrable output has the exact threshold probability as its expectation. -/
def FiniteUnbiasedClass {R : Type} [MeasurableSpace R] (s : ℕ) (M V W : ℝ)
    (A : AdaptiveEstimator R) : Prop :=
  ∀ (μ : Measure Gap) [IsProbabilityMeasure μ] (q : SignLaw), SmoothModel s M μ q →
    Integrable (populationOutput A) (experimentLaw μ A q) ∧
    (∫ z, populationOutput A z ∂experimentLaw μ A q) = signMean μ q.val ∧
    evariance (populationOutput A) (experimentLaw μ A q) ≤ ENNReal.ofReal V ∧
    expectedWork μ A q ≤ ENNReal.ofReal W

theorem smooth_unbiased_impossible (s : ℕ) :
    ∃ M₀ : ℝ, 0 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M →
      ∀ (R : Type) [MeasurableSpace R] (A : AdaptiveEstimator R) (V W : ℝ),
        0 ≤ V → 0 ≤ W → ¬ FiniteUnbiasedClass s M V W A := by
  obtain ⟨M₀,hM₀,hpair⟩ := smooth_pair_in_class s
  refine ⟨M₀,hM₀,?_⟩
  intro M hM R _ A V W hV hW hA
  let C := (128 / 225 : ℝ) * W * (2 * V + 1 / 2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let L := Real.log 64 + 8 * (Real.sqrt C + 1)
  have hlog : 0 < Real.log (64 : ℝ) := Real.log_pos (by norm_num)
  have hL : 0 < L := by dsimp [L]; positivity
  let t := Real.exp (-L)
  have ht : 0 < t := Real.exp_pos _
  have ht1 : t ≤ 1 / 64 := by
    calc
      t ≤ Real.exp (-Real.log 64) := Real.exp_le_exp.mpr (by
        dsimp [L]
        linarith [Real.sqrt_nonneg C])
      _ = 1 / 64 := by rw [Real.exp_neg,Real.exp_log (by norm_num)]; norm_num
  have ht' : t ≤ 1 := by linarith
  have hlt : Real.log (1 / t) = L := by simp [t]
  let qp := smoothSign s ht ht' true
  let qm := smoothSign s ht ht' false
  have hmodel (q : SignLaw) (hq : q = qp ∨ q = qm) : SmoothModel s M smoothGapLaw q := by
    rcases hq with rfl | rfl
    · obtain ⟨f,hf,hn,hs,hi,hb,hr⟩ := hpair t ht ht' true
      exact ⟨f,hf,hn,hs,hi,fun k hk p => (hb k hk p).trans hM,hr⟩
    · obtain ⟨f,hf,hn,hs,hi,hb,hr⟩ := hpair t ht ht' false
      exact ⟨f,hf,hn,hs,hi,fun k hk p => (hb k hk p).trans hM,hr⟩
  obtain ⟨_,hup,hvp,hwp⟩ := hA smoothGapLaw qp (hmodel qp (Or.inl rfl))
  obtain ⟨_,hum,hvm,hwm⟩ := hA smoothGapLaw qm (hmodel qm (Or.inr rfl))
  let η : Gap → ℝ := fun d => perturbation s t d
  have hη : Measurable η := (perturbation_contDiff s t).continuous.measurable.comp measurable_subtype_coe
  have hηb (d : Gap) : 0 ≤ η d ∧ η d ≤ 1 / 8 :=
    ⟨perturbation_nonneg s ht.le d.property.1.le,
      (le_abs_self _).trans (perturbation_abs_le s ht.le ht' d)⟩
  have hqp (d : Gap) : qp.val d = 1 / 2 + η d := by simp [qp,smoothSign,η]
  have hqm (d : Gap) : qm.val d = 1 / 2 - η d := by simp [qm,smoothSign,η,sub_eq_add_neg]
  have hgap (d : Gap) : (d : ℝ) * η d ≤ t ^ (s + 1) / 8 :=
    gap_mul_perturbation_le s ht d
  have hklp := hidden_local_pair_information smoothGapLaw A η hη hηb qp qm hqp hqm
    W (t ^ (s + 1)) (pow_pos ht _) hgap hwp
  have hklm := hidden_reverse_pair_information smoothGapLaw A η hηb qp qm hqp hqm
    W (t ^ (s + 1)) (pow_pos ht _) hgap hwm
  have hlp := (evariance_lt_top_iff_memLp (measurable_populationOutput A).aestronglyMeasurable).mp
    (lt_of_le_of_lt hvp ENNReal.ofReal_lt_top)
  have hlm := (evariance_lt_top_iff_memLp (measurable_populationOutput A).aestronglyMeasurable).mp
    (lt_of_le_of_lt hvm ENNReal.ofReal_lt_top)
  have hvp' : variance (populationOutput A) (experimentLaw smoothGapLaw A qp) ≤ V := by
    simpa only [variance,ENNReal.toReal_ofReal hV] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hvp
  have hvm' : variance (populationOutput A) (experimentLaw smoothGapLaw A qm) ≤ V := by
    simpa only [variance,ENNReal.toReal_ofReal hV] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hvm
  have hv := two_point_uniform_variance (experimentLaw smoothGapLaw A qp) (experimentLaw smoothGapLaw A qm)
    hlp hlm hV (by positivity) hvp' hvm' hklp hklm
  rw [hup,hum] at hv
  let Δ := signMean smoothGapLaw qp.val - signMean smoothGapLaw qm.val
  have hd : Δ ^ 2 ≤ 1 := by
    have hp := signMean_bounds smoothGapLaw qp
    have hm := signMean_bounds smoothGapLaw qm
    dsimp [Δ]
    nlinarith [sq_nonneg (signMean smoothGapLaw qp.val - signMean smoothGapLaw qm.val)]
  have hb : Δ ^ 2 ≤ C * (t ^ (s + 1)) ^ 2 := by
    have hc := mul_le_mul_of_nonneg_left
      (show 2 * V + Δ ^ 2 / 2 ≤ 2 * V + 1 / 2 by linarith)
      (show 0 ≤ (128 / 225 : ℝ) * (t ^ (s + 1)) ^ 2 * W by positivity)
    dsimp [C]
    change Δ ^ 2 ≤ _ at hv
    nlinarith [hv.trans hc]
  have hsep := smoothSign_separation s ht ht1
  rw [hlt] at hsep
  change t ^ (s + 1) / 8 * L ≤ Δ at hsep
  have hsq := mul_self_le_mul_self (show 0 ≤ t ^ (s + 1) / 8 * L by positivity) hsep
  have hcancel : L ^ 2 ≤ 64 * C := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos (pow_pos ht (s + 1)))).mp
    nlinarith only [hsq,hb]
  have hlower : 8 * Real.sqrt C < L := by dsimp [L]; linarith
  nlinarith [Real.sq_sqrt hC, Real.sqrt_nonneg C]

end ThresholdHC.SmoothDensity
