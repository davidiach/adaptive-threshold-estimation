import ThresholdHC.Genie.LatentModel
import ThresholdHC.Genie.RevealReward

/-! Finite latent divergence removes singular nonzero score states almost
everywhere and is exactly the score's second moment under the actual latent
reference law. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.Genie
open ThresholdHC.Tier6 ThresholdHC.StoppingProgram

theorem weighted_score_square (x y : ℝ) (hy : 0 ≤ y) (hfin : perspective x y ≠ ⊤) :
    ENNReal.ofReal y*ENNReal.ofReal ((x/y)^2) = perspective x y := by
  by_cases hy0 : y = 0
  · have hx : x = 0 := by
      by_contra hx
      exact hfin (by rw [hy0,perspective_nonzero_zero hx])
    simp [hy0,hx,perspective_zero_zero]
  · have hy' : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
    rw [perspective_pos hy',←ENNReal.ofReal_mul hy]
    congr 1
    field_simp

theorem finite_latent_perspectives_ae (μ : Measure Gap) (Q : FourPriors)
    (hC : latentDivergence μ Q ≠ ⊤) :
    ∀ᵐ d ∂μ, perspective (Q.high.val d-Q.low.val d) (Q.variance.val d) ≠ ⊤ ∧
      perspective (Q.high.val d-Q.low.val d) (1-Q.variance.val d) ≠ ⊤ := by
  have hd := Q.high.property.1.sub Q.low.property.1
  have hm : Measurable (fun d : Gap => perspective (Q.high.val d-Q.low.val d) (Q.variance.val d)+
      perspective (Q.high.val d-Q.low.val d) (1-Q.variance.val d)) :=
    (measurable_perspective _ _ hd Q.variance.property.1).add
    (measurable_perspective _ _ hd (measurable_const.sub Q.variance.property.1))
  have hh := ae_lt_top hm hC
  filter_upwards [hh] with d hd
  exact ENNReal.add_ne_top.mp hd.ne

theorem latentScore_secondMoment (μ : Measure Gap) [IsFiniteMeasure μ]
    (Q : FourPriors) (hC : latentDivergence μ Q ≠ ⊤) :
    (∫⁻ z, ENNReal.ofReal ((latentScore Q z)^2) ∂latentReference μ Q.variance) =
      latentDivergence μ Q := by
  rw [latentReference_lintegral μ Q.variance _ ((measurable_latentScore Q).pow_const 2).ennreal_ofReal]
  apply lintegral_congr_ae
  filter_upwards [finite_latent_perspectives_ae μ Q hC] with d hd
  simp only [latentScore,ite_true,Bool.false_eq_true,ite_false]
  rw [weighted_score_square _ _ (Q.variance.property.2 d).1 hd.1]
  have he : perspective (-(Q.high.val d-Q.low.val d)) (1-Q.variance.val d) ≠ ⊤ := by
    rw [perspective_neg_left]
    exact hd.2
  rw [weighted_score_square _ _ (sub_nonneg.mpr (Q.variance.property.2 d).2) he,perspective_neg_left]

theorem latentScore_memLp_two (μ : Measure Gap) [IsProbabilityMeasure μ]
    (Q : FourPriors) (hC : latentDivergence μ Q ≠ ⊤) :
    MemLp (latentScore Q) 2 (latentReference μ Q.variance) := by
  apply (memLp_two_iff_integrable_sq (measurable_latentScore Q).aestronglyMeasurable).mpr
  apply (lintegral_ofReal_ne_top_iff_integrable
    ((measurable_latentScore Q).pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z => sq_nonneg (latentScore Q z)))).mp
  rwa [latentScore_secondMoment μ Q hC]

theorem latentScore_integrable (μ : Measure Gap) [IsProbabilityMeasure μ]
    (Q : FourPriors) (hC : latentDivergence μ Q ≠ ⊤) :
    Integrable (latentScore Q) (latentReference μ Q.variance) :=
  (latentScore_memLp_two μ Q hC).integrable (by norm_num)

end ThresholdHC.Genie
