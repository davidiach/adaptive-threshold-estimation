import ThresholdHC.CriticalPsi.Model
import ThresholdHC.Tier3.Optimizer
import ThresholdHC.CriticalUpper.CappedCost

noncomputable section
namespace ThresholdHC.CriticalPsi
open MeasureTheory Set ThresholdHC.Tier3 ThresholdHC.CriticalEntropy
open ThresholdHC.CriticalUpper
open scoped ENNReal

theorem critical_gap_positive : ∀ᵐ d ∂criticalGapLaw, 0 < id d :=
  criticalGap_ae_support.mono (fun _ hd => hd.1)

theorem criticalPsi_eq_optimizer (ρ h t : ℝ) (hh : 0 < h) (ht : 0 < t)
    (hm : allocationMass criticalGapLaw id t = ρ) :
    criticalPsi ρ h = rareObjective criticalGapLaw id h (fun d => allocation t d) := by
  have hf := allocation_feasible measurable_id hm
  have hmax (v : ℝ → ℝ) (hv : FeasibleAllocation criticalGapLaw ρ v) :
      rareObjective criticalGapLaw id h v ≤
        rareObjective criticalGapLaw id h (fun d => allocation t d) := by
    by_cases hht : h < t
    · exact optimizer_below_cutoff measurable_id critical_gap_positive hh hht hm hv
    · exact optimizer_above_cutoff measurable_id critical_gap_positive ht (not_lt.mp hht) hm hv
  have hmem : rareObjective criticalGapLaw id h (fun d => allocation t d) ∈
      {y : ℝ | ∃ v : ℝ → ℝ, FeasibleAllocation criticalGapLaw ρ v ∧
        y = rareObjective criticalGapLaw id h v} := ⟨_,hf,rfl⟩
  have hbound : BddAbove {y : ℝ | ∃ v : ℝ → ℝ, FeasibleAllocation criticalGapLaw ρ v ∧
      y = rareObjective criticalGapLaw id h v} := by
    refine ⟨rareObjective criticalGapLaw id h (fun d => allocation t d),?_⟩
    rintro y ⟨v,hv,rfl⟩
    exact hmax v hv
  apply le_antisymm
  · apply csSup_le ⟨_,hmem⟩
    rintro y ⟨v,hv,rfl⟩
    exact hmax v hv
  · exact le_csSup hbound hmem

theorem critical_allocation_mass (t : ℝ) (ht : 0 < t) (htq : t ≤ 1/4) :
    allocationMass criticalGapLaw id t = 16*t^2*(1+Real.log (1/(16*t^2))) := by
  have hmap : allocationMass criticalGapLaw id t =
      ∫ u, min (1 : ℝ) ((16*t^2)/u) ∂uniformUnitMeasure := by
    rw [← criticalGap_square_map,integral_map (by fun_prop) (by fun_prop)]
    unfold allocationMass
    apply integral_congr_ae
    filter_upwards [criticalGap_ae_support] with d hd
    dsimp only [id,allocation]
    congr 1
    field_simp
  rw [hmap,uniformUnitMeasure,integral_Icc_eq_integral_Ioc]
  have h := cappedReciprocal_integral_large 1 (16*t^2) 1 (by norm_num)
    (by positivity) (by nlinarith)
  simpa only [one_mul,div_one] using h

theorem criticalGap_integral_Ioc (f : ℝ → ℝ) (x y : ℝ) (hx : 0 ≤ x)
    (hy : y ≤ 1/4) :
    (∫ d in Ioc x y, f d ∂criticalGapLaw) = ∫ d in Ioc x y, (32*d)*f d := by
  rw [criticalGapLaw,setIntegral_withDensity_eq_setIntegral_toReal_smul
    (by fun_prop) (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)) f measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc]
  have he : Ioc x y ∩ Ioc (0 : ℝ) (1/4) = Ioc x y := by
    apply inter_eq_left.mpr
    intro d hd
    exact ⟨hx.trans_lt hd.1,hd.2.trans hy⟩
  rw [he]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with d hd
  have hd0 : 0 ≤ d := hx.trans hd.1.le
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ 32*d),smul_eq_mul]

theorem criticalGap_inv_integral (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y)
    (hy : y ≤ 1/4) :
    (∫ d in Ioc x y, d⁻¹ ∂criticalGapLaw) = 32*(y-x) := by
  rw [criticalGap_integral_Ioc _ x y hx.le hy]
  have he : (fun d : ℝ => (32*d)*d⁻¹) =ᵐ[volume.restrict (Ioc x y)] fun _ => (32 : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with d hd
    field_simp [(hx.trans hd.1).ne']
  rw [integral_congr_ae he,integral_const]
  simp only [Measure.real,Measure.restrict_apply_univ,Real.volume_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hxy),smul_eq_mul]
  ring

theorem criticalGap_inv_sq_integral (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y)
    (hy : y ≤ 1/4) :
    (∫ d in Ioc x y, (d⁻¹)^2 ∂criticalGapLaw) = 32*Real.log (y/x) := by
  rw [criticalGap_integral_Ioc _ x y hx.le hy]
  have he : (fun d : ℝ => (32*d)*(d⁻¹)^2) =ᵐ[volume.restrict (Ioc x y)]
      fun d => 32*d⁻¹ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with d hd
    field_simp [(hx.trans hd.1).ne']
  rw [integral_congr_ae he,← intervalIntegral.integral_of_le hxy,
    intervalIntegral.integral_const_mul,integral_inv_of_pos hx (hx.trans_le hxy)]

theorem criticalGap_Iic_mass (h : ℝ) (hh : 0 ≤ h) (hq : h ≤ 1/4) :
    criticalGapLaw.real {d | d ≤ h} = 16*h^2 := by
  have he : {d : ℝ | d ≤ h} =ᵐ[criticalGapLaw] Ioc 0 h := by
    filter_upwards [criticalGap_ae_support] with d hd
    simp only [mem_Ioc,hd.1,true_and]
  rw [measureReal_congr he,criticalGapLaw_real_Ioc 0 h (by norm_num) hh hq]
  ring

theorem criticalGap_tail_inv_sq (t : ℝ) (ht : 0 < t) (htq : t ≤ 1/4) :
    (∫ d in {d | t < d}, (d⁻¹)^2 ∂criticalGapLaw) = 32*Real.log (1/(4*t)) := by
  have he : {d : ℝ | t < d} =ᵐ[criticalGapLaw] Ioc t (1/4) := by
    filter_upwards [criticalGap_ae_support] with d hd
    simp only [mem_Ioc,hd.2,and_true]
  rw [setIntegral_congr_set he,criticalGap_inv_sq_integral t (1/4) ht htq le_rfl]
  congr 2
  ring

theorem critical_optimizer_formula (h t : ℝ) (hh : 0 < h) (hht : h < t)
    (htq : t ≤ 1/4) :
    rareObjective criticalGapLaw id h (fun d => allocation t d) =
      16*(2*h*t*(1+Real.log (1/(4*t)))-h^2) := by
  have hf := optimizer_formula measurable_id critical_gap_positive hh hht
  dsimp only [id] at hf
  rw [hf]
  rw [criticalGap_Iic_mass h hh.le (hht.le.trans htq),
    show {d : ℝ | h < d ∧ d ≤ t} = Ioc h t from rfl,
    criticalGap_inv_integral h t hh hht.le htq,criticalGap_tail_inv_sq t (hh.trans hht) htq]
  ring

theorem critical_cutoff_below_quarter (ρ t : ℝ) (hρ : ρ < 1) (_ht : 0 < t)
    (hm : allocationMass criticalGapLaw id t = ρ) : t < 1/4 := by
  by_contra h
  have he : (fun d => allocation t (id d)) =ᵐ[criticalGapLaw] fun _ => (1 : ℝ) := by
    filter_upwards [criticalGap_ae_support] with d hd
    exact allocation_eq_one hd.1 (hd.2.trans (le_of_not_gt h))
  have hone : allocationMass criticalGapLaw id t = 1 := by
    unfold allocationMass
    rw [integral_congr_ae he]
    simp
  linarith

theorem criticalPsi_formula (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ t : ℝ, 0 < t ∧ t < 1/4 ∧
      ρ = 16*t^2*(1+2*Real.log (1/(4*t))) ∧
      ∀ h : ℝ, 0 < h → criticalPsi ρ h =
        if h < t then 16*(2*h*t*(1+Real.log (1/(4*t)))-h^2) else ρ := by
  have hd : ∀ᵐ d ∂criticalGapLaw, 0 < id d ∧ id d ≤ 1/2 := by
    filter_upwards [criticalGap_ae_support] with d hd
    exact ⟨hd.1,hd.2.trans (by norm_num)⟩
  obtain ⟨t,ht,_,hm⟩ := cutoff_exists measurable_id hd hρ hρ1
  have htq := critical_cutoff_below_quarter ρ t hρ1 ht hm
  refine ⟨t,ht,htq,?_,?_⟩
  · rw [← hm,critical_allocation_mass t ht htq.le]
    have he : 1/(16*t^2) = (1/(4*t))^2 := by ring
    rw [he,Real.log_pow]
    norm_num
  · intro h hh
    rw [criticalPsi_eq_optimizer ρ h t hh ht hm]
    by_cases hht : h < t
    · rw [ite_eq_left hht]
      exact critical_optimizer_formula h t hh hht htq.le
    · rw [ite_eq_right hht]
      exact optimizer_saturation critical_gap_positive ht (le_of_not_gt hht) hm


end ThresholdHC.CriticalPsi
