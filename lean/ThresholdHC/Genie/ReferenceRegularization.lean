import ThresholdHC.Genie.Model
import ThresholdHC.Genie.PerspectiveTopology
import ThresholdHC.StoppingProgram.AbsorbedPriors

/-! Mix only the variance reference with the endpoint midpoint. This keeps
the target gap and work reference fixed, preserves rarity, and controls the
information penalty while making the latent divergence finite. -/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace ThresholdHC.Genie
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.StoppingProgram

def regularizedPriors (Q : FourPriors) (ε : ℝ) (hε : 0 ≤ ε ∧ ε ≤ 1) : FourPriors :=
  ⟨Q.low,Q.high,mixPrior (midpointPrior Q.low Q.high) Q.variance ε hε,Q.work⟩

theorem regularizedPriors_admissible (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ : ℝ} (Q : FourPriors) (hQ : Admissible μ ρ Q) (ε : ℝ) (hε : 0 ≤ ε ∧ ε ≤ 1) :
    Admissible μ ρ (regularizedPriors Q ε hε) :=
  ⟨hQ.1,hQ.2.1,mixPrior_rare μ _ _
    (mixPrior_rare μ Q.low Q.high hQ.1 hQ.2.1 (1/2) (by norm_num)) hQ.2.2.1 ε hε,hQ.2.2.2⟩

theorem perspective_scale_reference (x y c : ℝ) (hy : 0 ≤ y) (hc : 0 < c) :
    perspective x (c*y) = ENNReal.ofReal (1/c)*perspective x y := by
  by_cases hy0 : y = 0
  · subst y
    by_cases hx : x = 0
    · simp [hx,perspective]
    · rw [mul_zero,perspective_nonzero_zero hx,
        ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr (by positivity : 0 < 1/c))]
  · have hy' : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
    rw [perspective_pos (mul_pos hc hy'),perspective_pos hy',←ENNReal.ofReal_mul (by positivity : 0 ≤ 1/c)]
    congr 1
    ring

theorem regularized_count_reference {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (Q : FourPriors) (ε : ℝ) (hε : 0 ≤ ε ∧ ε ≤ 1) (s : CountState N) :
    (1-ε)*countCoefficient μ Q.variance s ≤ countCoefficient μ (regularizedPriors Q ε hε).variance s := by
  change _ ≤ countCoefficient μ (mixPrior _ _ ε hε) s
  rw [mixPrior_countCoefficient]
  exact le_add_of_nonneg_left (mul_nonneg hε.1 (countCoefficient_nonneg μ _ s))

theorem regularized_flowInformation {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (Q : FourPriors) (ε : ℝ) (hε : 0 ≤ ε ∧ ε ≤ 1) (hε1 : ε < 1) (f : Flow N) :
    flowInformation μ (regularizedPriors Q ε hε) f ≤
      ENNReal.ofReal (1/(1-ε))*flowInformation μ Q f := by
  unfold flowInformation
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  have hh := perspective_antitone_reference (countCoefficient μ Q.high s-countCoefficient μ Q.low s)
    (mul_nonneg (by linarith : 0 ≤ 1-ε) (countCoefficient_nonneg μ Q.variance s))
    (regularized_count_reference μ Q ε hε s)
  rw [perspective_scale_reference _ _ _ (countCoefficient_nonneg μ Q.variance s) (by linarith)] at hh
  have hm := mul_le_mul_right hh (ENNReal.ofReal (f.stopWeight s))
  simpa only [regularizedPriors,mul_left_comm] using hm

theorem regularized_informationRatio (μ : Measure Gap) [IsProbabilityMeasure μ]
    (N : ℕ) (Q : FourPriors) (ε : ℝ) (hε : 0 ≤ ε ∧ ε ≤ 1) (hε1 : ε < 1) :
    informationRatio μ N (regularizedPriors Q ε hε) ≤
      ENNReal.ofReal (1/(1-ε))*informationRatio μ N Q := by
  apply iSup_le
  intro f
  apply iSup_le
  intro hf
  apply iSup_le
  intro hi
  calc
    _ ≤ (ENNReal.ofReal (1/(1-ε))*flowInformation μ Q f)/
        ENNReal.ofReal (countMean μ Q.work f.continueWeight) :=
      ENNReal.div_le_div_right (regularized_flowInformation μ Q ε hε hε1 f) _
    _ = ENNReal.ofReal (1/(1-ε))*(flowInformation μ Q f/
        ENNReal.ofReal (countMean μ Q.work f.continueWeight)) := mul_div_assoc _ _ _
    _ ≤ _ := by
      have hs : flowInformation μ Q f/ENNReal.ofReal (countMean μ Q.work f.continueWeight) ≤
          informationRatio μ N Q := le_iSup_of_le f (le_iSup_of_le hf (le_iSup_of_le hi le_rfl))
      exact mul_le_mul_right hs _

theorem regularized_infiniteInformation (μ : Measure Gap) [IsProbabilityMeasure μ]
    (Q : FourPriors) (ε : ℝ) (hε : 0 ≤ ε ∧ ε ≤ 1) (hε1 : ε < 1) :
    infiniteInformationRatio μ (regularizedPriors Q ε hε) ≤
      ENNReal.ofReal (1/(1-ε))*infiniteInformationRatio μ Q := by
  rw [infiniteInformationRatio,infiniteInformationRatio,ENNReal.mul_iSup]
  exact iSup_mono (fun N => regularized_informationRatio μ (N+1) Q ε hε hε1)

theorem binary_difference_sq_bound (a b : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) :
    (b-a)^2 ≤ a+b ∧ (b-a)^2 ≤ 2-a-b := by
  have ha2 : a^2 ≤ a := by nlinarith [mul_nonneg ha.1 (sub_nonneg.mpr ha.2)]
  have hb2 : b^2 ≤ b := by nlinarith [mul_nonneg hb.1 (sub_nonneg.mpr hb.2)]
  constructor
  · nlinarith [mul_nonneg ha.1 hb.1]
  · nlinarith [mul_nonneg (sub_nonneg.mpr ha.2) (sub_nonneg.mpr hb.2)]

theorem regularized_latent_perspective (Q : FourPriors) (ε : ℝ)
    (hε : 0 ≤ ε ∧ ε ≤ 1) (hε0 : 0 < ε) (d : Gap) :
    perspective (Q.high.val d-Q.low.val d) ((regularizedPriors Q ε hε).variance.val d) ≤ ENNReal.ofReal (2/ε) ∧
    perspective (Q.high.val d-Q.low.val d) (1-(regularizedPriors Q ε hε).variance.val d) ≤ ENNReal.ofReal (2/ε) := by
  let v := (regularizedPriors Q ε hε).variance.val d
  have hv : 0 ≤ v ∧ v ≤ 1 := (regularizedPriors Q ε hε).variance.property.2 d
  have hsq := binary_difference_sq_bound (Q.low.val d) (Q.high.val d)
    (Q.low.property.2 d) (Q.high.property.2 d)
  have he : v = ε*(Q.low.val d+Q.high.val d)/2+(1-ε)*Q.variance.val d := by
    dsimp [v,regularizedPriors,mixPrior,midpointPrior]
    ring
  have h1 : ε/2*(Q.low.val d+Q.high.val d) ≤ v := by
    rw [he]
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1-ε) (Q.variance.property.2 d).1]
  have h2 : ε/2*(2-Q.low.val d-Q.high.val d) ≤ 1-v := by
    rw [he]
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1-ε) (sub_nonneg.mpr (Q.variance.property.2 d).2)]
  constructor
  · rw [perspective_le_finite_iff _ _ hv.1 _ ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 2/ε)]
    change _ ≤ (2/ε)*v
    have hh := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 2/ε)
    have hc : (2/ε)*(ε/2) = 1 := by field_simp
    rw [←mul_assoc,hc,one_mul] at hh
    exact hsq.1.trans hh
  · rw [perspective_le_finite_iff _ _ (sub_nonneg.mpr hv.2) _ ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 2/ε)]
    change _ ≤ (2/ε)*(1-v)
    have hh := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 2/ε)
    have hc : (2/ε)*(ε/2) = 1 := by field_simp
    rw [←mul_assoc,hc,one_mul] at hh
    exact hsq.2.trans hh

theorem regularized_latentDivergence_bound (μ : Measure Gap) [IsProbabilityMeasure μ]
    (Q : FourPriors) (ε : ℝ) (hε : 0 ≤ ε ∧ ε ≤ 1) (hε0 : 0 < ε) :
    latentDivergence μ (regularizedPriors Q ε hε) ≤ ENNReal.ofReal (4/ε) := by
  calc
    _ ≤ ∫⁻ _ : Gap, ENNReal.ofReal (2/ε)+ENNReal.ofReal (2/ε) ∂μ :=
      lintegral_mono (fun d => add_le_add (regularized_latent_perspective Q ε hε hε0 d).1
        (regularized_latent_perspective Q ε hε hε0 d).2)
    _ = _ := by
      simp only [lintegral_const,measure_univ,mul_one]
      rw [←ENNReal.ofReal_add (by positivity : 0 ≤ 2/ε) (by positivity : 0 ≤ 2/ε)]
      congr 1
      ring

end ThresholdHC.Genie
