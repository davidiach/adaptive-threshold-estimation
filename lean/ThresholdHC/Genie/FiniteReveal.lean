import ThresholdHC.Genie.RevealReward
import ThresholdHC.Genie.PerspectiveTopology
import ThresholdHC.StoppingProgram.FiniteProgram
import ThresholdHC.StoppingProgram.PriorContraction

/-! Exact atom formulas and latent rotated-cone certificates for finite
gap laws. Positive atom weights retain the null-reference convention. -/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace ThresholdHC.Genie
open ThresholdHC.Tier6 ThresholdHC.StoppingProgram
variable {I : Type*} [Fintype I]

theorem finite_law_lintegral (μ : Measure Gap) (w : I → ℝ) (d : I → Gap)
    (hμ : μ = ∑ i, ENNReal.ofReal (w i) • Measure.dirac (d i))
    (F : Gap → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, F x ∂μ) = ∑ i, ENNReal.ofReal (w i)*F (d i) := by
  rw [hμ,lintegral_finsetSum_measure]
  simp only [lintegral_smul_measure,lintegral_dirac' _ hF,smul_eq_mul]

theorem finite_revealReward (μ : Measure Gap) (w : I → ℝ) (d : I → Gap)
    (hμ : μ = ∑ i, ENNReal.ofReal (w i) • Measure.dirac (d i))
    (Q : FourPriors) (n k : ℕ) :
    revealReward μ Q n k = ∑ i, ENNReal.ofReal (w i)*
      (ENNReal.ofReal (prefixLikelihood true n k (d i))*perspective (Q.high.val (d i)-Q.low.val (d i)) (Q.variance.val (d i))+
       ENNReal.ofReal (prefixLikelihood false n k (d i))*perspective (Q.high.val (d i)-Q.low.val (d i)) (1-Q.variance.val (d i))) :=
  finite_law_lintegral μ w d hμ _ (measurable_revealIntegrand Q n k)

theorem finite_latentDivergence (μ : Measure Gap) (w : I → ℝ) (d : I → Gap)
    (hμ : μ = ∑ i, ENNReal.ofReal (w i) • Measure.dirac (d i)) (Q : FourPriors) :
    latentDivergence μ Q = ∑ i, ENNReal.ofReal (w i)*
      (perspective (Q.high.val (d i)-Q.low.val (d i)) (Q.variance.val (d i))+
       perspective (Q.high.val (d i)-Q.low.val (d i)) (1-Q.variance.val (d i))) := by
  simpa [prefixLikelihood] using
    (revealReward_root μ Q).symm.trans (finite_revealReward μ w d hμ Q 0 0)

theorem finite_latent_perspectives (μ : Measure Gap) (w : I → ℝ) (d : I → Gap)
    (hw : ∀ i, 0 < w i) (hμ : μ = ∑ i, ENNReal.ofReal (w i) • Measure.dirac (d i))
    (Q : FourPriors) (hC : latentDivergence μ Q ≠ ⊤) (i : I) :
    perspective (Q.high.val (d i)-Q.low.val (d i)) (Q.variance.val (d i)) ≠ ⊤ ∧
      perspective (Q.high.val (d i)-Q.low.val (d i)) (1-Q.variance.val (d i)) ≠ ⊤ := by
  rw [finite_latentDivergence μ w d hμ] at hC
  have hm := ENNReal.sum_ne_top.mp hC i (Finset.mem_univ i)
  exact ENNReal.add_ne_top.mp (ENNReal.lt_top_of_mul_ne_top_right hm (ENNReal.ofReal_pos.mpr (hw i)).ne').ne

theorem finite_revealReward_toReal (μ : Measure Gap) (w : I → ℝ) (d : I → Gap)
    (hw : ∀ i, 0 < w i) (hμ : μ = ∑ i, ENNReal.ofReal (w i) • Measure.dirac (d i))
    (Q : FourPriors) (hC : latentDivergence μ Q ≠ ⊤) (n k : ℕ) :
    (revealReward μ Q n k).toReal = ∑ i, w i*
      (prefixLikelihood true n k (d i)*(perspective (Q.high.val (d i)-Q.low.val (d i)) (Q.variance.val (d i))).toReal+
       prefixLikelihood false n k (d i)*(perspective (Q.high.val (d i)-Q.low.val (d i)) (1-Q.variance.val (d i))).toReal) := by
  have hf := finite_latent_perspectives μ w d hw hμ Q hC
  rw [finite_revealReward μ w d hμ,ENNReal.toReal_sum (fun i _ =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hf i).1,ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hf i).2⟩))]
  apply Finset.sum_congr rfl
  intro i _
  rw [ENNReal.toReal_mul,ENNReal.toReal_add
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hf i).1) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hf i).2)]
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (hw i).le,
    ENNReal.toReal_ofReal (prefixLikelihood_nonneg _ _ _ _)]

def LatentCones (d : I → Gap) (Q : FourPriors) (α : ℝ) (rPlus rMinus : I → ℝ) : Prop :=
  ∀ i, 0 ≤ rPlus i ∧ 0 ≤ rMinus i ∧
    (α*(Q.high.val (d i)-Q.low.val (d i)))^2 ≤ Q.variance.val (d i)*rPlus i ∧
    (α*(Q.high.val (d i)-Q.low.val (d i)))^2 ≤ (1-Q.variance.val (d i))*rMinus i

theorem latentCones_bounds (d : I → Gap) (Q : FourPriors) (α : ℝ)
    (rPlus rMinus : I → ℝ) (hr : LatentCones d Q α rPlus rMinus) (i : I) :
    perspective (α*(Q.high.val (d i)-Q.low.val (d i))) (Q.variance.val (d i)) ≤ ENNReal.ofReal (rPlus i) ∧
    perspective (α*(Q.high.val (d i)-Q.low.val (d i))) (1-Q.variance.val (d i)) ≤ ENNReal.ofReal (rMinus i) := by
  constructor
  · rw [perspective_le_finite_iff _ _ (Q.variance.property.2 (d i)).1 _ ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (hr i).1]
    simpa only [mul_comm] using (hr i).2.2.1
  · rw [perspective_le_finite_iff _ _ (sub_nonneg.mpr (Q.variance.property.2 (d i)).2) _ ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (hr i).2.1]
    simpa only [mul_comm] using (hr i).2.2.2

theorem latentCones_of_finite (μ : Measure Gap) (w : I → ℝ) (d : I → Gap)
    (hw : ∀ i, 0 < w i) (hμ : μ = ∑ i, ENNReal.ofReal (w i) • Measure.dirac (d i))
    (Q : FourPriors) (hC : latentDivergence μ Q ≠ ⊤) (α : ℝ) :
    LatentCones d Q α
      (fun i => α^2*(perspective (Q.high.val (d i)-Q.low.val (d i)) (Q.variance.val (d i))).toReal)
      (fun i => α^2*(perspective (Q.high.val (d i)-Q.low.val (d i)) (1-Q.variance.val (d i))).toReal) := by
  intro i
  have hf := finite_latent_perspectives μ w d hw hμ Q hC i
  have hp := (perspective_le_finite_iff _ _ (Q.variance.property.2 (d i)).1 _ hf.1).mp le_rfl
  have hm := (perspective_le_finite_iff _ _ (sub_nonneg.mpr (Q.variance.property.2 (d i)).2) _ hf.2).mp le_rfl
  refine ⟨by positivity,by positivity,?_,?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left hp (sq_nonneg α)]
  · nlinarith [mul_le_mul_of_nonneg_left hm (sq_nonneg α)]

theorem latentCones_finite (μ : Measure Gap) (w : I → ℝ) (d : I → Gap)
    (hμ : μ = ∑ i, ENNReal.ofReal (w i) • Measure.dirac (d i))
    (Q : FourPriors) (α : ℝ) (hα : 0 < α) (rPlus rMinus : I → ℝ)
    (hr : LatentCones d Q α rPlus rMinus) : latentDivergence μ Q ≠ ⊤ := by
  rw [finite_latentDivergence μ w d hμ]
  apply ENNReal.sum_ne_top.mpr
  intro i _
  apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
  apply ENNReal.add_ne_top.mpr
  have hp := latentCones_bounds d Q α rPlus rMinus hr i
  have hs : ENNReal.ofReal (α^2) ≠ 0 := (ENNReal.ofReal_pos.mpr (sq_pos_of_pos hα)).ne'
  rw [perspective_scale_contrast,perspective_scale_contrast] at hp
  exact ⟨(ENNReal.lt_top_of_mul_ne_top_right (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hp.1) hs).ne,
    (ENNReal.lt_top_of_mul_ne_top_right (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hp.2) hs).ne⟩

end ThresholdHC.Genie
