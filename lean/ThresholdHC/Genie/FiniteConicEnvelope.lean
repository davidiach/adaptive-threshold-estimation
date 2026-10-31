import ThresholdHC.Genie.FiniteReveal
import ThresholdHC.Genie.BellmanEnvelope
import ThresholdHC.Genie.RevealBellman

/-! The finite latent cones and triangular stopping/continuation inequalities
are exactly the scaled genie Bellman epigraph. -/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace ThresholdHC.Genie
open ThresholdHC.Tier6 ThresholdHC.StoppingProgram
variable {I : Type*} [Fintype I]

def finiteRevealBound (w : I → ℝ) (d : I → Gap) (rPlus rMinus : I → ℝ) (n k : ℕ) : ℝ :=
  ∑ i, w i*(prefixLikelihood true n k (d i)*rPlus i+prefixLikelihood false n k (d i)*rMinus i)

theorem finiteRevealBound_lower (μ : Measure Gap) (w : I → ℝ) (d : I → Gap)
    (hw : ∀ i, 0 < w i) (hμ : μ = ∑ i, ENNReal.ofReal (w i) • Measure.dirac (d i))
    (Q : FourPriors) (hC : latentDivergence μ Q ≠ ⊤) (α : ℝ)
    (rPlus rMinus : I → ℝ) (hr : LatentCones d Q α rPlus rMinus) (n k : ℕ) :
    α^2*(revealReward μ Q n k).toReal ≤ finiteRevealBound w d rPlus rMinus n k := by
  rw [finite_revealReward_toReal μ w d hw hμ Q hC]
  unfold finiteRevealBound
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hp := latentCones_bounds d Q α rPlus rMinus hr i
  have hp' := ENNReal.toReal_mono ENNReal.ofReal_ne_top hp.1
  have hm' := ENNReal.toReal_mono ENNReal.ofReal_ne_top hp.2
  rw [perspective_scale_contrast,ENNReal.toReal_mul,ENNReal.toReal_ofReal (sq_nonneg α),
    ENNReal.toReal_ofReal (hr i).1] at hp'
  rw [perspective_scale_contrast,ENNReal.toReal_mul,ENNReal.toReal_ofReal (sq_nonneg α),
    ENNReal.toReal_ofReal (hr i).2.1] at hm'
  have hh := mul_le_mul_of_nonneg_left (add_le_add
    (mul_le_mul_of_nonneg_left hp' (prefixLikelihood_nonneg true n k (d i)))
    (mul_le_mul_of_nonneg_left hm' (prefixLikelihood_nonneg false n k (d i)))) (hw i).le
  convert hh using 1 <;> ring

theorem finiteRevealBound_exact (μ : Measure Gap) (w : I → ℝ) (d : I → Gap)
    (hw : ∀ i, 0 < w i) (hμ : μ = ∑ i, ENNReal.ofReal (w i) • Measure.dirac (d i))
    (Q : FourPriors) (hC : latentDivergence μ Q ≠ ⊤) (α : ℝ) (n k : ℕ) :
    finiteRevealBound w d
      (fun i => α^2*(perspective (Q.high.val (d i)-Q.low.val (d i)) (Q.variance.val (d i))).toReal)
      (fun i => α^2*(perspective (Q.high.val (d i)-Q.low.val (d i)) (1-Q.variance.val (d i))).toReal) n k =
        α^2*(revealReward μ Q n k).toReal := by
  rw [finite_revealReward_toReal μ w d hw hμ Q hC,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

theorem quadratic_slack_iff (x y α X : ℝ) (hy : 0 ≤ y) (hX : 0 ≤ X)
    (hf : perspective x y ≠ ⊤) :
    (α*x)^2 ≤ 4*y*X ↔ α^2/4*(perspective x y).toReal ≤ X := by
  by_cases hy0 : y = 0
  · have hx : x = 0 := by
      by_contra hx
      exact hf (by rw [hy0,perspective_nonzero_zero hx])
    simp [hy0,hx,perspective,hX]
  · have hypos : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
    rw [perspective_pos hypos,ENNReal.toReal_ofReal (div_nonneg (sq_nonneg x) hy)]
    have he : α^2/4*(x^2/y) = (α*x)^2/(4*y) := by ring
    rw [he,div_le_iff₀ (by positivity : 0 < 4*y)]
    constructor <;> intro h <;> nlinarith

def FiniteGenieCones {N : ℕ} (μ : Measure Gap) (w : I → ℝ) (d : I → Gap)
    (Q : FourPriors) (α η : ℝ) (X : CountState N → ℝ) (rPlus rMinus : I → ℝ) : Prop :=
  LatentCones d Q α rPlus rMinus ∧
  (∀ n k, 1 ≤ n → n ≤ N → k ≤ n → 0 ≤ arrayAt X n k ∧
    (if n = N then finiteRevealBound w d rPlus rMinus n k/4 ≤ arrayAt X n k
     else (α*(prefixCoefficient μ Q.high n k-prefixCoefficient μ Q.low n k))^2 ≤
       4*prefixCoefficient μ Q.variance n k*arrayAt X n k)) ∧
  (∀ n k, 1 ≤ n → n < N → k ≤ n →
    arrayAt X (n+1) k+arrayAt X (n+1) (k+1)-η*prefixCoefficient μ Q.work n k ≤ arrayAt X n k) ∧
  arrayAt X 1 0+arrayAt X 1 1-η ≤ 0

theorem finiteGenieCones_envelope {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (w : I → ℝ) (d : I → Gap) (hw : ∀ i, 0 < w i)
    (hμ : μ = ∑ i, ENNReal.ofReal (w i) • Measure.dirac (d i))
    (Q : FourPriors) (hC : latentDivergence μ Q ≠ ⊤) (α η : ℝ)
    (X : CountState N → ℝ) (rPlus rMinus : I → ℝ)
    (hX : FiniteGenieCones μ w d Q α η X rPlus rMinus) :
    BellmanEnvelope (fun n k => α^2/4*genieReward μ Q N n k) (prefixCoefficient μ Q.work) η X := by
  refine ⟨?_,hX.2.2⟩
  intro n k hn hnN hk
  have hs := hX.2.1 n k hn hnN hk
  by_cases he : n = N
  · simp only [he,ite_true] at hs
    have hb := finiteRevealBound_lower μ w d hw hμ Q hC α rPlus rMinus hX.1 N k
    change α^2/4*(geniePrefixInformation μ Q N n k).toReal ≤ _
    simp only [geniePrefixInformation,he,ite_true]
    nlinarith [hs.2]
  · simp only [he,ite_false] at hs
    have hf := ne_top_of_le_ne_top hC ((prefixInformation_le_revealReward μ Q n k).trans
      (revealReward_le_latentDivergence μ Q n k))
    have hh := (quadratic_slack_iff _ _ α _ (prefixCoefficient_nonneg μ Q.variance n k) hs.1 hf).mp hs.2
    simpa only [genieReward,geniePrefixInformation,he,ite_false,prefixInformation] using hh

theorem finiteGenieCones_of_envelope {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (w : I → ℝ) (d : I → Gap) (hw : ∀ i, 0 < w i)
    (hμ : μ = ∑ i, ENNReal.ofReal (w i) • Measure.dirac (d i))
    (Q : FourPriors) (hC : latentDivergence μ Q ≠ ⊤) (α η : ℝ)
    (X : CountState N → ℝ)
    (hX : BellmanEnvelope (fun n k => α^2/4*genieReward μ Q N n k) (prefixCoefficient μ Q.work) η X) :
    ∃ rPlus rMinus : I → ℝ, FiniteGenieCones μ w d Q α η X rPlus rMinus := by
  refine ⟨_,_,latentCones_of_finite μ w d hw hμ Q hC α,?_,hX.2⟩
  intro n k hn hnN hk
  have hh := hX.1 n k hn hnN hk
  have hpos : 0 ≤ arrayAt X n k := (show 0 ≤ α^2/4*genieReward μ Q N n k by
    exact mul_nonneg (by positivity) ENNReal.toReal_nonneg).trans hh
  refine ⟨hpos,?_⟩
  by_cases he : n = N
  · rw [ite_eq_left he,finiteRevealBound_exact μ w d hw hμ Q hC]
    simpa only [genieReward,geniePrefixInformation,he,ite_true,div_mul_eq_mul_div] using hh
  · rw [ite_eq_right he]
    have hf := ne_top_of_le_ne_top hC ((prefixInformation_le_revealReward μ Q n k).trans
      (revealReward_le_latentDivergence μ Q n k))
    apply (quadratic_slack_iff _ _ α _ (prefixCoefficient_nonneg μ Q.variance n k) hpos hf).mpr
    simpa only [genieReward,geniePrefixInformation,he,ite_false,prefixInformation] using hh

theorem finiteGenieCones_iff_bellman (N : ℕ) (μ : Measure Gap) [IsProbabilityMeasure μ]
    (w : I → ℝ) (d : I → Gap) (hw : ∀ i, 0 < w i)
    (hμ : μ = ∑ i, ENNReal.ofReal (w i) • Measure.dirac (d i))
    (Q : FourPriors) (hC : latentDivergence μ Q ≠ ⊤) (hN : 0 < N) (α η : ℝ) :
    (∃ X rPlus rMinus, FiniteGenieCones (N := N) μ w d Q α η X rPlus rMinus) ↔
      rootBellman (fun n k => α^2/4*genieReward μ Q N n k) (prefixCoefficient μ Q.work) η (N-1) ≤ 0 := by
  rw [←exists_bellmanEnvelope_iff N _ _ _ hN]
  constructor
  · rintro ⟨X,rp,rm,hX⟩
    exact ⟨X,finiteGenieCones_envelope μ w d hw hμ Q hC α η X rp rm hX⟩
  · rintro ⟨X,hX⟩
    obtain ⟨rp,rm,hr⟩ := finiteGenieCones_of_envelope μ w d hw hμ Q hC α η X hX
    exact ⟨X,rp,rm,hr⟩

end ThresholdHC.Genie
