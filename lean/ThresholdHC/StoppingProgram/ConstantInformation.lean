import ThresholdHC.StoppingProgram.LabelPerspective
import ThresholdHC.StoppingProgram.PositiveValue

/-! A cap-independent information bound for constant sign priors follows by
revealing the latent binary label and conserving the terminal flow mass. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.StoppingProgram
open ThresholdHC.Tier6 (Gap SignLaw)

theorem constantPrior_countCoefficient {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (i : CountState N) :
    countCoefficient μ (constantPrior p hp) i =
      p*countCoefficient μ (constantPrior 1 (by norm_num)) i+
        (1-p)*countCoefficient μ (constantPrior 0 (by norm_num)) i := by
  have he : constantPrior p hp = mixPrior (constantPrior 1 (by norm_num))
      (constantPrior 0 (by norm_num)) p hp := by
    apply Subtype.ext
    funext d
    simp [constantPrior,mixPrior]
  rw [he,mixPrior_countCoefficient]

theorem constantPrior_midpoint (u v : ℝ) (hu : 0 ≤ u ∧ u ≤ 1) (hv : 0 ≤ v ∧ v ≤ 1) :
    midpointPrior (constantPrior u hu) (constantPrior v hv) =
      constantPrior ((u+v)/2) ⟨by linarith [hu.1,hv.1],by linarith [hu.2,hv.2]⟩ := by
  apply Subtype.ext
  funext d
  dsimp only [midpointPrior,mixPrior,constantPrior]
  ring

theorem constant_flowInformation_bound {N : ℕ} (μ : Measure Gap) [IsProbabilityMeasure μ]
    (u v m : ℝ) (hu : 0 ≤ u ∧ u ≤ 1) (hv : 0 ≤ v ∧ v ≤ 1)
    (hm : 0 < m) (hm1 : m < 1) (f : Flow N) (hf : FlowCone f) :
    flowInformation μ ⟨constantPrior u hu,constantPrior v hv,
      constantPrior m ⟨hm.le,hm1.le⟩,constantPrior m ⟨hm.le,hm1.le⟩⟩ f ≤
      ENNReal.ofReal ((v-u)^2*intensity f/(m*(1-m))) := by
  let qp := constantPrior 1 (by norm_num)
  let qm := constantPrior 0 (by norm_num)
  have hstate (i : CountState N) :
      perspective (countCoefficient μ (constantPrior v hv) i-countCoefficient μ (constantPrior u hu) i)
        (countCoefficient μ (constantPrior m ⟨hm.le,hm1.le⟩) i) ≤
      ENNReal.ofReal ((v-u)^2*(countCoefficient μ qp i/m+countCoefficient μ qm i/(1-m))) := by
    rw [constantPrior_countCoefficient μ v hv,constantPrior_countCoefficient μ u hu,
      constantPrior_countCoefficient μ m]
    have he : v*countCoefficient μ qp i+(1-v)*countCoefficient μ qm i-
        (u*countCoefficient μ qp i+(1-u)*countCoefficient μ qm i) =
        (v-u)*(countCoefficient μ qp i-countCoefficient μ qm i) := by ring
    rw [he]
    exact perspective_label_bound _ _ m (v-u) (countCoefficient_nonneg μ qp i)
      (countCoefficient_nonneg μ qm i) hm hm1
  calc
    _ ≤ ∑ i : CountState N, ENNReal.ofReal (f.stopWeight i*((v-u)^2*
        (countCoefficient μ qp i/m+countCoefficient μ qm i/(1-m)))) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [ENNReal.ofReal_mul (hf.stop_nonneg i)]
      exact mul_le_mul_right (hstate i) _
    _ = ENNReal.ofReal (∑ i : CountState N, f.stopWeight i*((v-u)^2*
        (countCoefficient μ qp i/m+countCoefficient μ qm i/(1-m)))) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro i hi
      exact mul_nonneg (hf.stop_nonneg i) (mul_nonneg (sq_nonneg _)
        (add_nonneg (div_nonneg (countCoefficient_nonneg μ qp i) hm.le)
          (div_nonneg (countCoefficient_nonneg μ qm i) (by linarith))))
    _ = _ := by
      congr 1
      have he (i : CountState N) : f.stopWeight i*((v-u)^2*
          (countCoefficient μ qp i/m+countCoefficient μ qm i/(1-m))) =
          (v-u)^2*(countCoefficient μ qp i*f.stopWeight i/m+
            countCoefficient μ qm i*f.stopWeight i/(1-m)) := by ring
      simp_rw [he]
      rw [← Finset.mul_sum,Finset.sum_add_distrib,← Finset.sum_div,← Finset.sum_div]
      change (v-u)^2*(countMean μ qp f.stopWeight/m+countMean μ qm f.stopWeight/(1-m)) = _
      rw [countMean_stop_eq_intensity μ qp f hf,countMean_stop_eq_intensity μ qm f hf]
      field_simp
      ring

theorem constant_informationRatio_bound (μ : Measure Gap) [IsProbabilityMeasure μ]
    (N : ℕ) (u v m : ℝ) (hu : 0 ≤ u ∧ u ≤ 1) (hv : 0 ≤ v ∧ v ≤ 1)
    (hm : 0 < m) (hm1 : m < 1) :
    informationRatio μ N ⟨constantPrior u hu,constantPrior v hv,
      constantPrior m ⟨hm.le,hm1.le⟩,constantPrior m ⟨hm.le,hm1.le⟩⟩ ≤
      ENNReal.ofReal ((v-u)^2/(m*(1-m))) := by
  apply iSup_le
  intro f
  apply iSup_le
  intro hf
  apply iSup_le
  intro hi
  have hI := constant_flowInformation_bound μ u v m hu hv hm hm1 f hf
  rw [hi,mul_one] at hI
  have hw : 1 ≤ ENNReal.ofReal (countMean μ (constantPrior m ⟨hm.le,hm1.le⟩) f.continueWeight) := by
    have h := ENNReal.ofReal_le_ofReal (flow_work_ge_intensity μ (constantPrior m ⟨hm.le,hm1.le⟩) f hf)
    simpa [hi] using h
  apply ENNReal.div_le_of_le_mul
  exact hI.trans (by simpa only [mul_one] using mul_le_mul_right hw (ENNReal.ofReal ((v-u)^2/(m*(1-m)))))

end ThresholdHC.StoppingProgram
