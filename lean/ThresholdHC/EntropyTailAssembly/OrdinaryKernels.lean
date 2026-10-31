import ThresholdHC.EntropyTailUpper.Ordinary
import ThresholdHC.EntropyTailUpper.PopulationErrors

/-! Deterministic ordinary error/work kernels and their finite-measure
integrals. No normalization of the component measure is imposed. -/

noncomputable section
open MeasureTheory Set Real Filter
open scoped Topology

namespace ThresholdHC.EntropyTailAssembly
open ThresholdHC.Tier6 ThresholdHC.EntropyTailUpper

def eta (ξ : Measure Gap) (M : ℝ) : ℝ := ∫ d : Gap, ordinaryErrorKernel M (d:ℝ) ∂ξ
def ordinaryCost (ξ : Measure Gap) (M : ℝ) : ℝ := ∫ d : Gap, ordinaryWorkKernel M (d:ℝ) ∂ξ

theorem ordinaryErrorKernel_nonneg (M d : ℝ) : 0 ≤ ordinaryErrorKernel M d := by
  unfold ordinaryErrorKernel
  positivity

theorem ordinaryWorkKernel_nonneg {M : ℝ} (hM : 0 ≤ M) (d : ℝ) : 0 ≤ ordinaryWorkKernel M d := by
  have h := le_max_left (0:ℝ) (log (M*d^2))
  unfold ordinaryWorkKernel
  positivity

theorem integrable_ordinaryWorkKernel (ξ : Measure Gap) [IsFiniteMeasure ξ] {M : ℝ} (hM : 0 ≤ M) :
    Integrable (fun d : Gap => ordinaryWorkKernel M (d:ℝ)) ξ := by
  have hm : Measurable (fun d : Gap => ordinaryWorkKernel M (d:ℝ)) := by
    unfold ordinaryWorkKernel
    fun_prop
  apply Integrable.of_bound hm.aestronglyMeasurable M
  exact ae_of_all _ (fun d => by
    rw [Real.norm_of_nonneg (ordinaryWorkKernel_nonneg hM (d:ℝ))]
    exact min_le_left _ _)

theorem eta_nonneg (ξ : Measure Gap) (M : ℝ) : 0 ≤ eta ξ M :=
  integral_nonneg (fun d => ordinaryErrorKernel_nonneg M (d:ℝ))

theorem ordinaryCost_nonneg (ξ : Measure Gap) {M : ℝ} (hM : 0 ≤ M) : 0 ≤ ordinaryCost ξ M :=
  integral_nonneg (fun d => ordinaryWorkKernel_nonneg hM (d:ℝ))

theorem eta_le_mass (ξ : Measure Gap) [IsFiniteMeasure ξ] (M : ℝ) : eta ξ M ≤ ξ.real univ := by
  change (∫ d : Gap, ordinaryErrorKernel M (d:ℝ) ∂ξ) ≤ _
  have h := integral_mono (integrable_ordinaryErrorKernel ξ M) (integrable_const (1:ℝ))
    (fun _ => min_le_left _ _)
  simpa using h

theorem ordinaryCost_le_cap (ξ : Measure Gap) [IsFiniteMeasure ξ] {M : ℝ} (hM : 0 ≤ M) :
    ordinaryCost ξ M ≤ M*ξ.real univ := by
  change (∫ d : Gap, ordinaryWorkKernel M (d:ℝ) ∂ξ) ≤ _
  have h := integral_mono (integrable_ordinaryWorkKernel ξ hM) (integrable_const M)
    (fun _ => min_le_left _ _)
  simpa [mul_comm] using h

theorem ordinaryErrorKernel_four (d : Gap) : ordinaryErrorKernel 4 (d:ℝ) = 1 := by
  have hd2 : 0 < 4*(d:ℝ)^2 := by positivity [d.property.1]
  have hd1 : 4*(d:ℝ)^2 ≤ 1 := by nlinarith [d.property.1, d.property.2]
  have hi : 1 ≤ (4*(d:ℝ)^2)⁻¹ := (one_le_inv₀ hd2).mpr hd1
  exact min_eq_left (by nlinarith)

theorem eta_four (ξ : Measure Gap) [IsFiniteMeasure ξ] : eta ξ 4 = ξ.real univ := by
  unfold eta
  simp only [ordinaryErrorKernel_four, integral_const, smul_eq_mul, mul_one]

theorem ordinaryErrorKernel_antitone {M P : ℝ} (hM : 0 < M) (hMP : M ≤ P) (d : Gap) :
    ordinaryErrorKernel P (d:ℝ) ≤ ordinaryErrorKernel M (d:ℝ) := by
  have hP : 0 < P := hM.trans_le hMP
  apply min_le_min le_rfl
  apply pow_le_pow_left₀ (by positivity)
  exact inv_anti₀ (by positivity [d.property.1]) (mul_le_mul_of_nonneg_right hMP (sq_nonneg _))

theorem eta_antitone (ξ : Measure Gap) [IsFiniteMeasure ξ] {M P : ℝ} (hM : 0 < M) (hMP : M ≤ P) :
    eta ξ P ≤ eta ξ M :=
  integral_mono (integrable_ordinaryErrorKernel ξ P) (integrable_ordinaryErrorKernel ξ M)
    (ordinaryErrorKernel_antitone hM hMP)

theorem ordinaryErrorKernel_four_mul (M d : ℝ) :
    ordinaryErrorKernel M d / 16 ≤ ordinaryErrorKernel (4*M) d := by
  have he : ((4*M*d^2)⁻¹^2) = ((M*d^2)⁻¹^2)/16 := by ring
  unfold ordinaryErrorKernel
  rw [he]
  apply le_min
  · exact (div_le_one (by norm_num : (0:ℝ) < 16)).mpr ((min_le_left _ _).trans (by norm_num))
  · exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)

theorem eta_four_mul (ξ : Measure Gap) [IsFiniteMeasure ξ] (M : ℝ) : eta ξ M / 16 ≤ eta ξ (4*M) := by
  have h := integral_mono ((integrable_ordinaryErrorKernel ξ M).div_const 16)
    (integrable_ordinaryErrorKernel ξ (4*M)) (fun d : Gap => ordinaryErrorKernel_four_mul M (d:ℝ))
  rw [integral_div] at h
  exact h

theorem eta_add (σ τ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ] (M : ℝ) :
    eta (σ+τ) M = eta σ M+eta τ M :=
  integral_add_measure (integrable_ordinaryErrorKernel σ M) (integrable_ordinaryErrorKernel τ M)

theorem ordinaryCost_add (σ τ : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure τ]
    {M : ℝ} (hM : 0 ≤ M) : ordinaryCost (σ+τ) M = ordinaryCost σ M+ordinaryCost τ M :=
  integral_add_measure (integrable_ordinaryWorkKernel σ hM) (integrable_ordinaryWorkKernel τ hM)

end ThresholdHC.EntropyTailAssembly
