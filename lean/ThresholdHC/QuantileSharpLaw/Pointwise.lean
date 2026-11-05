import ThresholdHC.QuantileSharpLaw.MeasureGeometry
import ThresholdHC.QuantileSharpLaw.Normalization

noncomputable section
open MeasureTheory Real Set
open scoped BigOperators ENNReal
namespace ThresholdHC.QuantileSharpLaw
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTailQuantile ThresholdHC.OptimalQuantile

theorem lowerCut_support (t r : ℝ) (σ : Measure Gap) :
    ∀ᵐ d : Gap ∂lowerCut t r σ, (d : ℝ) ≤ t := by
  rw [lowerCut,ae_add_measure_iff]
  constructor
  · exact (ae_restrict_mem (measurableSet_lt measurable_subtype_coe measurable_const)).mono
      (fun _ hd => hd.le)
  · apply Measure.ae_smul_measure
    exact (ae_restrict_mem (measurableSet_eq_fun measurable_subtype_coe measurable_const)).mono
      (fun _ hd => hd.le)

theorem sharp_comparison_pointwise (μ : Measure Gap) [IsProbabilityMeasure μ]
    {ρ B : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hB : 0 < B)
    (hht : budgetScale B < quantileThreshold μ ρ) (σ : Measure Gap) (hσ : σ ≤ μ) :
    closedQuantileValue μ ρ B ≤ ENNReal.ofReal scalarRoot*selectionCost μ σ ρ (budgetScale B) := by
  let t := quantileThreshold μ ρ
  let h := budgetScale B
  let r := quantileBoundaryFraction μ ρ
  have ht : 0 < t := (quantileThreshold_properties μ hρ hρ1).1
  have hh : 0 < h := budgetScale_pos hB
  have hk : 0 < scalarRoot := (sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).trans_le scalarRoot_spec.1.1
  have hr := quantileBoundaryFraction_properties μ hρ hρ1
  by_cases hinf : measureCostEntropy σ = ⊤
  · simp [selectionCost,hinf,ENNReal.mul_top,ENNReal.ofReal_eq_zero,
      not_le.mpr hk,not_le.mpr hρ,not_le.mpr (budgetScale_pos hB)]
  let L := lowerCut t r σ
  let V := upperCut t r σ
  let D := lowerCut t r (μ-σ)
  let Z := upperCut t r (μ-σ)
  have : IsFiniteMeasure σ := isFiniteMeasure_of_le μ hσ
  have : IsFiniteMeasure L := isFiniteMeasure_of_le σ (lowerCut_le t hr.1 hr.2.1 σ)
  have : IsFiniteMeasure V := isFiniteMeasure_of_le σ (upperCut_le t hr.1 hr.2.1 σ)
  have : IsFiniteMeasure D := isFiniteMeasure_of_le (μ-σ) (lowerCut_le t hr.1 hr.2.1 _)
  have : IsFiniteMeasure Z := isFiniteMeasure_of_le (μ-σ) (upperCut_le t hr.1 hr.2.1 _)
  have hsum : L+V=σ := lowerCut_add_upperCut t hr.1 hr.2.1 σ
  have hres : D+Z=μ-σ := lowerCut_add_upperCut t hr.1 hr.2.1 _
  have hsplit : σ+(μ-σ)=μ := (add_comm ..).trans (Measure.sub_add_cancel_of_le hσ)
  have htail : quantileTail μ ρ=L+D := by
    change lowerCut t r μ=_
    rw [← lowerCut_add,hsplit]
  have hcore : quantileCore μ ρ=V+Z := by
    rw [quantileCore_eq_upperCut μ hρ hρ1]
    exact (congrArg (upperCut t r) hsplit).symm.trans (upperCut_add t r _ _)
  have hLs := lowerCut_support t r σ
  have hVs := upperCut_support t r σ
  have hZs := upperCut_support t r (μ-σ)
  have hLfin := ne_top_of_le_ne_top hinf (measureCostEntropy_mono (lowerCut_le t hr.1 hr.2.1 σ))
  have hCfin := (measureCostEntropy_lt_top_of_support _ ht (quantileCore_support μ ρ)).ne
  obtain ⟨n,hnlow,hnhigh⟩ := exists_boundary_band ht (quantileThreshold_properties μ hρ hρ1).2.1
  let T := tailModulus (quantileTail μ ρ) h
  let a := tailModulus D h
  let c := tailModulus Z h
  let q := h^2*ρ
  let M := ∑' j, bandCost L j
  let v := outwardCosts n (bandCost V)
  let b := outwardCosts n (bandCost Z)
  let E := (measureCostEntropy σ).toReal
  have hv := outwardCosts_nonneg n (bandCost_nonneg V)
  have hb := outwardCosts_nonneg n (bandCost_nonneg Z)
  have hq : 0 ≤ q := mul_nonneg (sq_nonneg h) hρ.le
  have ha : 0 ≤ a := tailModulus_nonneg _ hh.le
  have hc : 0 ≤ c := tailModulus_nonneg _ hh.le
  have hthreshold : h*ρ/t ≤ T := quantileTail_threshold_lower μ hρ hρ1 hh.le hht
  have hT : 0 < T := (div_pos (mul_pos hh hρ) ht).trans_le hthreshold
  have hTa : T=tailModulus L h+a := by
    dsimp only [T,a]
    rw [htail,tailModulus_add _ _ hh.le]
  have haT : a ≤ T := by linarith only [hTa,tailModulus_nonneg L hh.le]
  have hmass : L univ ≤ ENNReal.ofReal ρ :=
    (lowerCut_mono t r hσ univ).trans (quantileTail_mass μ hρ hρ1).le
  have hM : (T-a)^2 ≤ q*M := by
    have hCauchy := tailModulus_le_sqrt_bandMoment L hLfin hρ.le hh.le hmass
    have hs : (T-a)^2 ≤ (h*sqrt (ρ*M))^2 :=
      (sq_le_sq₀ (sub_nonneg.mpr haT) (mul_nonneg hh.le (sqrt_nonneg _))).mpr (by
        change tailModulus L h ≤ h*sqrt (ρ*M) at hCauchy
        linarith only [hCauchy,hTa])
    rw [mul_pow,sq_sqrt (mul_nonneg hρ.le (tsum_nonneg (bandCost_nonneg L)))] at hs
    simpa only [q,mul_assoc] using hs
  have hentropy : costEntropy (fun i => v i+M*boundaryUnit i) ≤ E := by
    have hm := merged_measure_entropy L V (by rwa [hsum]) n hnlow hnhigh hLs hVs
    simpa only [hsum] using hm
  have hwork : q*fullCoreCost n b ≤ T*c := by
    let H := ∫ d : Gap, (d : ℝ)⁻¹ ∂Z
    have hw := outward_core_work Z ht n hnhigh hZs
    have hd : fullCoreCost n b ≤ H/t := (le_div_iff₀ ht).mpr (by
      change t*fullCoreCost n b ≤ H at hw
      nlinarith only [hw])
    have hceq : c=h*H := tailModulus_eq_inverseCost _ (hZs.mono (fun _ hd => hht.le.trans hd))
    calc
      _ ≤ q*(H/t) := mul_le_mul_of_nonneg_left hd hq
      _ = (h*ρ/t)*c := by rw [hceq]; dsimp [q]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hthreshold hc
  have hraw := unnormalized_selection_price hv hb hT hq ha haT ENNReal.toReal_nonneg hM hentropy hwork
  have hcoreE : (measureCostEntropy (quantileCore μ ρ)).toReal =
      costEntropy (fun i => v i+b i) := by
    rw [hcore,outward_measure_entropy (V+Z) n hnlow (ae_add_measure_iff.mpr ⟨hVs,hZs⟩)]
    have hcost : bandCost (V+Z) = (fun j => bandCost V j+bandCost Z j) :=
      funext (bandCost_add V Z)
    rw [hcost,outwardCosts_add]
  have hprice (ξ : Measure Gap) (hfin : measureCostEntropy ξ ≠ ⊤) :
      ENNReal.ofReal h*(ENNReal.ofReal ρ*measureCostEntropy ξ)^(1/(2 : ℝ)) =
        ENNReal.ofReal (sqrt (q*(measureCostEntropy ξ).toReal)) := by
    rw [entropy_root_eq_ofReal hfin hρ.le hh.le]
    dsimp only [q]
    rw [mul_assoc,sqrt_mul (sq_nonneg h),sqrt_sq hh.le]
  calc
    _ ≤ ENNReal.ofReal T+ENNReal.ofReal h*
        (ENNReal.ofReal ρ*measureCostEntropy (quantileCore μ ρ))^(1/(2 : ℝ)) := min_le_right _ _
    _ = ENNReal.ofReal (T+sqrt (q*costEntropy (fun i => v i+b i))) := by
      rw [hprice _ hCfin,hcoreE,ENNReal.ofReal_add hT.le (sqrt_nonneg _)]
    _ ≤ _ := by
      apply (ENNReal.ofReal_le_ofReal hraw).trans_eq
      rw [selectionCost,← hres,tailModulus_add _ _ hh.le,hprice σ hinf,
        ENNReal.ofReal_mul hk.le,add_assoc,
        ENNReal.ofReal_add (sqrt_nonneg _) (add_nonneg ha hc)]

end ThresholdHC.QuantileSharpLaw
