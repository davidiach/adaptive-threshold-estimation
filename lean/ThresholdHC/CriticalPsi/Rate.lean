import ThresholdHC.CriticalPsi.Formula

noncomputable section
namespace ThresholdHC.CriticalPsi
open MeasureTheory Set ThresholdHC.Tier3 ThresholdHC.CriticalEntropy
open ThresholdHC.CriticalUpper
open scoped ENNReal

theorem log_le_half (u : ℝ) (hu : 0 < u) : Real.log u ≤ u/2 := by
  have hs : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu
  have hl := Real.log_le_sub_one_of_pos hs
  rw [Real.log_sqrt hu.le] at hl
  nlinarith [Real.sq_sqrt hu.le,sq_nonneg (Real.sqrt u-2)]

theorem critical_cutoff_log (ρ t : ℝ) (ht : 0 < t) (htq : t < 1/4)
    (hm : ρ = 16*t^2*(1+2*Real.log (1/(4*t)))) :
    let u := 1+2*Real.log (1/(4*t))
    1 ≤ u ∧ (1+Real.log (1/ρ)) = u-Real.log u ∧
      (1+Real.log (1/ρ)) ≤ u ∧ u ≤ 2*(1+Real.log (1/ρ)) := by
  dsimp only
  let u := 1+2*Real.log (1/(4*t))
  have hx : 1 ≤ 1/(4*t) := (le_div_iff₀ (by positivity)).mpr (by linarith)
  have hl : 0 ≤ Real.log (1/(4*t)) := Real.log_nonneg hx
  have hu1 : 1 ≤ u := by dsimp [u]; linarith
  have hu : 0 < u := by linarith
  have hlog : Real.log (16*t^2) = -2*Real.log (1/(4*t)) := by
    have he : 1/(16*t^2) = (1/(4*t))^2 := by ring
    have hr := congrArg Real.log he
    rw [Real.log_pow] at hr
    simp only [one_div,Real.log_inv] at hr
    norm_num at hr
    simp only [one_div,Real.log_inv]
    linarith
  have hL : 1+Real.log (1/ρ) = u-Real.log u := by
    rw [hm]
    change 1+Real.log (1/(16*t^2*u)) = _
    rw [one_div,Real.log_inv,Real.log_mul (by positivity : (16*t^2 : ℝ) ≠ 0) hu.ne',hlog]
    dsimp [u]
    ring
  refine ⟨hu1,hL,?_,?_⟩
  · change 1+Real.log (1/ρ) ≤ u
    rw [hL]
    linarith [Real.log_nonneg hu1]
  · change u ≤ 2*(1+Real.log (1/ρ))
    rw [hL]
    linarith [log_le_half u hu]

theorem criticalPsi_le_rarity (ρ h t : ℝ) (hh : 0 < h) (ht : 0 < t)
    (hm : allocationMass criticalGapLaw id t = ρ) : criticalPsi ρ h ≤ ρ := by
  rw [criticalPsi_eq_optimizer ρ h t hh ht hm,← hm]
  have hf := allocation_feasible measurable_id hm
  exact integral_mono_ae
    (objective_integrable measurable_id critical_gap_positive hf.1 hf.2.1 hh.le)
    (integrable_allocation measurable_id t) (ae_of_all _ (fun d => min_le_left _ _))

theorem criticalPsi_rate (ρ h : ℝ) (hρ : 0 < ρ) (hρq : ρ ≤ 1/4) (hh : 0 < h) :
    min ρ (h*Real.sqrt (ρ*(1+Real.log (1/ρ)))) ≤ criticalPsi ρ h ∧
      criticalPsi ρ h ≤ 16*min ρ (h*Real.sqrt (ρ*(1+Real.log (1/ρ)))) := by
  obtain ⟨t,ht,htq,hm,hformula⟩ := criticalPsi_formula ρ hρ (by linarith)
  let u := 1+2*Real.log (1/(4*t))
  let L := 1+Real.log (1/ρ)
  obtain ⟨hu1,_,hLu,huL⟩ := critical_cutoff_log ρ t ht htq hm
  change 1 ≤ u at hu1
  change L ≤ u at hLu
  change u ≤ 2*L at huL
  change ρ = 16*t^2*u at hm
  have hu : 0 < u := by linarith
  have hL : 0 < L := by linarith
  have hm0 : 0 ≤ ρ*L := by positivity
  have hs0 : 0 ≤ Real.sqrt (ρ*L) := Real.sqrt_nonneg _
  have hsq := Real.sq_sqrt hm0
  have hsupper : Real.sqrt (ρ*L) ≤ 4*t*u := by
    have hmul := mul_le_mul_of_nonneg_left hLu (by positivity : 0 ≤ 16*t^2*u)
    have hx : ρ*L ≤ (4*t*u)^2 := by rw [hm]; nlinarith
    nlinarith [show 0 ≤ 4*t*u by positivity]
  have hslower : 2*t*u ≤ Real.sqrt (ρ*L) := by
    have hmul := mul_le_mul_of_nonneg_left huL (by positivity : 0 ≤ 8*t^2*u)
    have hx : (2*t*u)^2 ≤ ρ*L := by
      rw [hm]
      nlinarith [sq_nonneg (2*t*u)]
    nlinarith [show 0 ≤ 2*t*u by positivity]
  have hbounds : criticalPsi ρ h ≤ ρ ∧ criticalPsi ρ h ≤ 16*h*Real.sqrt (ρ*L) ∧
      min ρ (h*Real.sqrt (ρ*L)) ≤ criticalPsi ρ h := by
    by_cases hht : h < t
    · have hp : criticalPsi ρ h = 16*(h*t*(u+1)-h^2) := by
        rw [hformula h hh,ite_eq_left hht]
        dsimp [u]
        ring
      have htu : h ≤ t*u := hht.le.trans (le_mul_of_one_le_right ht.le hu1)
      have hprod := mul_nonneg (sub_nonneg.mpr hht.le) (sub_nonneg.mpr htu)
      have hρbound : criticalPsi ρ h ≤ ρ := by rw [hp,hm]; nlinarith
      have huplus := mul_le_mul_of_nonneg_left hu1 (by positivity : 0 ≤ h*t)
      have hψupper : criticalPsi ρ h ≤ 32*h*t*u := by rw [hp]; nlinarith [sq_nonneg h]
      have hlower := mul_le_mul_of_nonneg_left hslower (by positivity : 0 ≤ 16*h)
      have hψlower : 16*h*t*u ≤ criticalPsi ρ h := by
        rw [hp]
        nlinarith [mul_nonneg hh.le (sub_nonneg.mpr hht.le)]
      have hupper := mul_le_mul_of_nonneg_left hsupper hh.le
      refine ⟨hρbound,by nlinarith,?_⟩
      apply (min_le_right _ _).trans
      nlinarith [show 0 ≤ h*t*u by positivity]
    · have hp : criticalPsi ρ h = ρ := by rw [hformula h hh,ite_eq_right hht]
      have htH := mul_le_mul_of_nonneg_right (le_of_not_gt hht) (by positivity : 0 ≤ 32*t*u)
      have hsH := mul_le_mul_of_nonneg_left hslower (by positivity : 0 ≤ 16*h)
      rw [hp]
      refine ⟨le_rfl,?_,min_le_left _ _⟩
      nlinarith [show 0 ≤ t^2*u by positivity]
  refine ⟨hbounds.2.2,?_⟩
  change criticalPsi ρ h ≤ 16*min ρ (h*Real.sqrt (ρ*L))
  rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 16)]
  exact le_min (by nlinarith [hbounds.1]) (by nlinarith [hbounds.2.1])

end ThresholdHC.CriticalPsi
