import ThresholdHC.ArbitraryLawAdaptation.LightContractionGeometry
import ThresholdHC.ArbitraryLawAdaptation.LightContractionConstants

/-! Actual product-measure cells for the light contraction entropy bound. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace ThresholdHC.ArbitraryLawAdaptation
open ThresholdHC.Tier6 (Gap)
open ThresholdHC.EntropyTail

theorem light_band_budget (ν : Measure Gap) [IsProbabilityMeasure ν]
    (hp : ∀ n : ℕ, 1 ≤ n → ν (band (n+1)) ≤
      ENNReal.ofReal (2*Real.exp (-((4 : ℝ)^(n+2)/2)))) (n : ℕ) :
    ENNReal.ofReal ((4 : ℝ)^(n+4))*ν (band (n+1)) ≤ ENNReal.ofReal (lightCostBound n) := by
  cases n with
  | zero =>
    norm_num [lightCostBound]
    exact (mul_le_mul_right (prob_le_one (μ := ν) (s := band 1)) 256).trans_eq (mul_one _)
  | succ n =>
    calc
      _ ≤ ENNReal.ofReal ((4 : ℝ)^(n+1+4))*
          ENNReal.ofReal (2*Real.exp (-((4 : ℝ)^(n+1+2)/2))) :=
        mul_le_mul_right (hp (n+1) (by omega)) _
      _ = ENNReal.ofReal ((4 : ℝ)^(n+1+4)*(2*Real.exp (-((4 : ℝ)^(n+1+2)/2)))) :=
        (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ _ := by
        simpa only [lightCostBound, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false]
          using ENNReal.ofReal_le_ofReal (light_exponential_cost (n+1))

theorem light_prod_support (σ ν : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure ν]
    (hv : ∀ᵐ (v : Gap) ∂ν, (v : ℝ) ≤ 1/4) : ∀ᵐ (z : Gap × Gap) ∂σ.prod ν, (z.2 : ℝ) ≤ 1/4 := by
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
  exact Filter.Eventually.of_forall fun _ => hv

theorem bandCost_index (σ : Measure Gap) (i : ℕ) :
    bandCost σ i = ∫⁻ d, if bandIndex d = i then inverseWeight d else 0 ∂σ := by
  simpa only [Measure.map_id, id_eq] using bandCost_map_index σ measurable_id i

theorem lintegral_bandIndex_indicator (ν : Measure Gap) (j : ℕ) :
    (∫⁻ v, if bandIndex v = j then (1 : ℝ≥0∞) else 0 ∂ν) = ν (band j) := by
  have he : (fun v : Gap => if bandIndex v = j then (1 : ℝ≥0∞) else 0) =
      (band j).indicator (fun _ => 1) := by
    funext v
    by_cases h : bandIndex v = j
    · rw [ite_eq_left h, Set.indicator_of_mem ((bandIndex_eq_iff v j).mp h)]
    · rw [ite_eq_right h, Set.indicator_of_notMem (fun hm => h ((bandIndex_eq_iff v j).mpr hm))]
  rw [he, lintegral_indicator (measurableSet_band j)]
  simp

theorem product_band_cost (σ ν : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure ν]
    (i j : ℕ) :
    (∫⁻ z, if bandIndex z.1 = i ∧ bandIndex z.2 = j then inverseWeight z.1 else 0 ∂σ.prod ν) =
      bandCost σ i*ν (band j) := by
  have he : (fun z : Gap × Gap => if bandIndex z.1 = i ∧ bandIndex z.2 = j then inverseWeight z.1 else 0) =
      fun z => (if bandIndex z.1 = i then inverseWeight z.1 else 0)*
        (if bandIndex z.2 = j then (1 : ℝ≥0∞) else 0) := by
    funext z
    by_cases h1 : bandIndex z.1 = i <;> by_cases h2 : bandIndex z.2 = j <;> simp [h1, h2]
  rw [he, lintegral_prod_mul
    (f := fun d => if bandIndex d = i then inverseWeight d else 0)
    (g := fun v => if bandIndex v = j then (1 : ℝ≥0∞) else 0),
    ← bandCost_index, lintegral_bandIndex_indicator]
  · exact (measurable_inverseWeight.ite
      (measurableSet_eq_fun measurable_bandIndex measurable_const) measurable_const).aemeasurable
  · exact (measurable_const.ite
      (measurableSet_eq_fun measurable_bandIndex measurable_const) measurable_const).aemeasurable

theorem light_cell_bound (σ ν : Measure Gap) [IsFiniteMeasure σ] [IsProbabilityMeasure ν]
    (hv : ∀ᵐ (v : Gap) ∂ν, (v : ℝ) ≤ 1/4)
    (hp : ∀ n : ℕ, 1 ≤ n → ν (band (n+1)) ≤
      ENNReal.ofReal (2*Real.exp (-((4 : ℝ)^(n+2)/2)))) (x : ℕ × ℕ) :
    cellCost (σ.prod ν) lightTag (fun z => inverseWeight (lightGap z)) x ≤
      bandCost σ x.1*ENNReal.ofReal (lightCostBound (x.2/2)) := by
  have hw : Measurable (fun z : Gap × Gap =>
      if bandIndex z.1 = x.1 ∧ bandIndex z.2 = x.2/2+1 then inverseWeight z.1 else 0) :=
    (measurable_inverseWeight.comp measurable_fst).ite
      ((measurableSet_eq_fun (measurable_bandIndex.comp measurable_fst) measurable_const).inter
        (measurableSet_eq_fun (measurable_bandIndex.comp measurable_snd) measurable_const)) measurable_const
  calc
    _ ≤ ENNReal.ofReal ((4 : ℝ)^(x.2/2+4))*
        (∫⁻ z, if bandIndex z.1 = x.1 ∧ bandIndex z.2 = x.2/2+1 then inverseWeight z.1 else 0 ∂σ.prod ν) := by
      rw [← lintegral_const_mul _ hw]
      apply lintegral_mono_ae
      filter_upwards [light_prod_support σ ν hv] with z hz
      by_cases ht : lightTag z = x
      · have h1 : bandIndex z.1 = x.1 := congrArg Prod.fst ht
        have h2 : bandIndex z.2 = x.2/2+1 := by rw [← ht]; exact (lightTag_multiplier hz).symm
        simp only [ht, ite_true, h1, h2, and_self]
        have hi := lightGap_inverseSquare z
        rw [h2] at hi
        exact (ENNReal.ofReal_le_ofReal hi).trans_eq (ENNReal.ofReal_mul (by positivity))
      · simp only [ht, ite_false]
        exact zero_le
    _ = bandCost σ x.1*(ENNReal.ofReal ((4 : ℝ)^(x.2/2+4))*ν (band (x.2/2+1))) := by
      rw [product_band_cost]
      ac_rfl
    _ ≤ _ := mul_le_mul_right (light_band_budget ν hp (x.2/2)) _

theorem light_column_cost (σ ν : Measure Gap) [IsFiniteMeasure σ] [IsFiniteMeasure ν]
    (hv : ∀ᵐ (v : Gap) ∂ν, (v : ℝ) ≤ 1/4) (j : ℕ) :
    (∑' x, if lightDest x = j then cellCost (σ.prod ν) lightTag (fun z => inverseWeight (lightGap z)) x else 0) =
      bandCost ((σ.prod ν).map lightGap) j := by
  rw [cellCost_merge (σ.prod ν) (w := fun z => inverseWeight (lightGap z))
      measurable_lightTag (measurable_inverseWeight.comp measurable_lightGap),
    bandCost_map_index _ measurable_lightGap]
  apply lintegral_congr_ae
  filter_upwards [light_prod_support σ ν hv] with z hz
  rw [lightTag_destination hz]

theorem gamma_light_contraction (σ ν : Measure Gap) [IsFiniteMeasure σ] [IsProbabilityMeasure ν]
    (hv : ∀ᵐ (v : Gap) ∂ν, (v : ℝ) ≤ 1/4)
    (hp : ∀ n : ℕ, 1 ≤ n → ν (band (n+1)) ≤
      ENNReal.ofReal (2*Real.exp (-((4 : ℝ)^(n+2)/2)))) :
    gamma ((σ.prod ν).map lightGap) ≤ 1024*gamma σ := by
  let b := cellCost (σ.prod ν) lightTag (fun z => inverseWeight (lightGap z))
  have hcol (j : ℕ) : (∑' x, if lightDest x = j then b x else 0) ≠ ∞ := by
    rw [light_column_cost σ ν hv]
    exact bandCost_ne_top _ _
  have hb (x : ℕ × ℕ) : b x ≠ ∞ := by
    apply ne_top_of_le_ne_top (hcol (lightDest x))
    simpa only [ite_true] using ENNReal.le_tsum
      (f := fun y => if lightDest y = lightDest x then b y else 0) x
  have hc (x : ℕ × ℕ) : (b x).toReal ≤ (bandCost σ x.1).toReal*lightCostBound (x.2/2) := by
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top (bandCost_ne_top _ _) ENNReal.ofReal_ne_top)
      (light_cell_bound σ ν hv hp x)
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (lightCostBound_nonneg _)] using h
  have he (j : ℕ) : (bandCost ((σ.prod ν).map lightGap) j).toReal =
      ∑' x, if lightDest x = j then (b x).toReal else 0 := by
    have h := ENNReal.tsum_toReal_eq (f := fun x => if lightDest x = j then b x else 0)
      (fun x => by split_ifs; exact hb x; exact ENNReal.zero_ne_top)
    rw [light_column_cost σ ν hv] at h
    simpa only [apply_ite ENNReal.toReal, ENNReal.toReal_zero] using h
  rw [← countableEntropy_bandCosts_eq_gamma, ← countableEntropy_bandCosts_eq_gamma σ]
  simp_rw [he]
  have h := countable_product_transport (fun _ => ENNReal.toReal_nonneg)
    (fun k => lightCostBound_nonneg (k/2)) (fun _ => ENNReal.toReal_nonneg)
    (fun k => lightReference_pos (k/2)) lightReference_duplicate_prefix
    lightReference_duplicate_code_prefix (by norm_num : (0 : ℝ) ≤ 1024) hc lightDest (fun j => by
      simpa only [apply_ite ENNReal.toReal, ENNReal.toReal_zero] using ENNReal.summable_toReal (hcol j))
  simpa only [ENNReal.ofReal_ofNat] using h

end ThresholdHC.ArbitraryLawAdaptation
