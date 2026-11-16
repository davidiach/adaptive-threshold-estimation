import ThresholdHC.PowerWindow.WindowBands
import ThresholdHC.PowerWindow.CoreCoordinates
import ThresholdHC.PowerWindow.BandCost
import ThresholdHC.PowerWindow.EntropyBounds
import ThresholdHC.PowerWindow.Quantile

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace ThresholdHC.PowerWindow
open ThresholdHC.Tier6 ThresholdHC.EntropyTailQuantile ThresholdHC.PsiGap
open ThresholdHC.RareAboveTwo (ExactPowerLaw)
open ThresholdHC.PsiClosedForm (quantileCore_le)

theorem power_core_cost_value (μ : Measure Gap) [IsProbabilityMeasure μ]
    {α a ρ : ℝ} (hα : 0 < α) (ha : 0 < a) (ha2 : a ≤ 1/2)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hm : ExactPowerLaw μ α a) :
    coreCost μ ρ = a⁻¹ ^ 2 * powerPhi α ρ := by
  calc
    _ = a⁻¹ ^ 2 * (a ^ 2 * coreCost μ ρ) := by field_simp
    _ = _ := by rw [power_core_cost μ hα ha ha2 hρ hρ1 hm]

theorem power_window_length {α a ρ : ℝ} (hα : 0 < α) (ha : 0 < a)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    0 < Real.logb 2 (1/ρ) / α ∧
    Real.log (a / (a * powerQuantileScale α ρ)) / Real.log 2 = Real.logb 2 (1/ρ) / α := by
  have hl : 0 < Real.log (1/ρ) := Real.log_pos ((one_lt_div hρ).2 hρ1)
  constructor
  · exact div_pos (div_pos hl (Real.log_pos (by norm_num))) hα
  · rw [Real.log_div ha.ne' (mul_pos ha (quantile_scale_pos hρ)).ne',
      Real.log_mul ha.ne' (quantile_scale_pos hρ).ne', powerQuantileScale,
      Real.log_rpow hρ, Real.logb, one_div ρ, Real.log_inv]
    ring

/-- The actual normalized band costs obey both entropy mechanisms: finite
window length and the geometric first-moment estimate. -/
theorem power_core_entropy_estimates (μ : Measure Gap) [IsProbabilityMeasure μ]
    {α a ρ : ℝ} (hα : 0 < α) (ha : 0 < a) (ha2 : a ≤ 1/2)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hm : ExactPowerLaw μ α a) :
    0 ≤ coreEntropy μ ρ ∧
    -Real.log (1 / (Real.logb 2 (1/ρ) / α) + |α - 2| * Real.log 2) ≤ coreEntropy μ ρ ∧
    coreEntropy μ ρ ≤ Real.log (Real.logb 2 (1/ρ) / α + 2) ∧
    (α ≠ 2 → coreEntropy μ ρ ≤ 1 + Real.log (2 + 2 / |α - 2|)) := by
  classical
  let σ := quantileCore μ ρ
  have : IsFiniteMeasure σ := isFiniteMeasure_of_le μ (quantileCore_le μ ρ)
  let A := a⁻¹ ^ 2 * powerPhi α ρ
  have hA : 0 < A := mul_pos (sq_pos_of_pos (inv_pos.2 ha)) (power_phi_pos hα hρ hρ1)
  have hAt : (∫ d : Gap, (d : ℝ)⁻¹ ^ 2 ∂σ) = A :=
    power_core_integral μ hα ha ha2 hρ hρ1 hm
  let aw : Gap := ⟨a, ha, ha2⟩
  have ht0 := mul_pos ha (quantile_scale_pos (α := α) hρ)
  have hta : a * powerQuantileScale α ρ ≤ a :=
    mul_le_of_le_one_right ha.le (quantile_scale_lt_one hα hρ hρ1).le
  let tw : Gap := ⟨a * powerQuantileScale α ρ, ht0, hta.trans ha2⟩
  obtain ⟨i, hi⟩ := ThresholdHC.EntropyTail.exists_band aw
  obtain ⟨j, hj⟩ := ThresholdHC.EntropyTail.exists_band tw
  rw [← ThresholdHC.EntropyTail.quantile_band_eq] at hi hj
  have hij : i ≤ j := band_index_antitone hj hi hta
  have hs : ∀ᵐ d : Gap ∂σ, (tw : ℝ) ≤ d ∧ (d : ℝ) ≤ aw :=
    power_core_window μ hα ha ha2 hρ hρ1 hm
  let S := Finset.Icc i j
  let p : S → ℝ := fun k => bandCost σ k / A
  have hp : ∀ k, 0 ≤ p k := fun k => div_nonneg (bandCost_nonneg σ k) hA.le
  obtain ⟨hpsum, hseries⟩ := window_entropy_normalization σ hi hj hs hA hAt
  have hsum : ∑ k, p k = 1 := hpsum
  have hE : coreEntropy μ ρ = ∑ k, Real.negMulLog (p k) := by
    rw [coreEntropy, power_core_cost_value μ hα ha ha2 hρ hρ1 hm]
    exact hseries
  have hM := (power_window_length hα ha hρ hρ1).1
  have hcard : (S.card : ℝ) ≤ Real.logb 2 (1/ρ) / α + 2 := by
    have hh := band_window_count hi hj hta
    rw [(power_window_length hα ha hρ hρ1).2] at hh
    exact hh
  have hcard0 : (0 : ℝ) < S.card := by
    exact_mod_cast (Finset.card_pos.2 ⟨i, Finset.mem_Icc.2 ⟨le_rfl, hij⟩⟩)
  have hbound (k : S) : p k ≤ 1 / (Real.logb 2 (1/ρ) / α) + |α - 2| * Real.log 2 := by
    apply (div_le_iff₀ hA).2
    rw [mul_comm _ A]
    exact power_core_band_bound μ hα ha ha2 hρ hρ1 hm k
  have hR : 0 < 1 / (Real.logb 2 (1/ρ) / α) + |α - 2| * Real.log 2 :=
    add_pos_of_pos_of_nonneg (one_div_pos.2 hM)
      (mul_nonneg (abs_nonneg _) (Real.log_nonneg (by norm_num)))
  rw [hE]
  refine ⟨finite_entropy_nonneg hp hsum, finite_entropy_lower_bound hp hsum hR hbound, ?_, ?_⟩
  · have hc := finite_entropy_card_bound hp hsum
    have he : Fintype.card S = S.card := Fintype.card_coe S
    rw [he] at hc
    exact hc.trans (Real.log_le_log hcard0 hcard)
  · intro hα2
    have hs0 : 0 < |α - 2| := abs_pos.2 (sub_ne_zero.2 hα2)
    have hm0 : 0 < 1 + 2 / |α - 2| := by positivity
    have hnormalize (k : ℕ → ℕ)
        (hb : (∑ l ∈ S, bandCost σ l * (k l : ℝ)) ≤ A * (1 + 2 / |α - 2|)) :
        (∑ l : S, p l * (k l : ℝ)) ≤ 1 + 2 / |α - 2| := by
      have he : (∑ l : S, p l * (k l : ℝ)) =
          (∑ l ∈ S, bandCost σ l * (k l : ℝ)) / A := by
        rw [← Finset.sum_coe_sort S (fun l => bandCost σ l * (k l : ℝ)), Finset.sum_div]
        apply Finset.sum_congr rfl
        intro l _
        dsimp [p]
        ring
      rw [he]
      exact (div_le_iff₀ hA).2 (by simpa only [mul_comm A] using hb)
    rcases lt_or_gt_of_ne hα2 with hlt | hgt
    · obtain ⟨hint, hmoment⟩ := power_core_lower_moment μ hα ha ha2 hρ hρ1 hm hlt
      let k : ℕ → ℕ := fun l => j - l
      have hb := window_label_mean σ hi hj hs k
        (fun d => 1 + Real.log ((d : ℝ) / (tw : ℝ)) / Real.log 2) hint
        (fun l _ => hs.mono fun d hd hdl => band_lower_label hdl hj hd.1)
      have hmean := hnormalize k (hb.trans hmoment)
      have hinj : Function.Injective (fun l : S => k l) := by
        intro x y hxy
        apply Subtype.ext
        have hx := (Finset.mem_Icc.1 x.2).2
        have hy := (Finset.mem_Icc.1 y.2).2
        dsimp [k] at hxy
        omega
      have hh := finite_entropy_mean_bound hp hsum (fun l : S => k l) hinj hm0 hmean
      rw [show 1 + 2 / |α - 2| + 1 = 2 + 2 / |α - 2| by ring] at hh
      simpa only [add_comm] using hh
    · obtain ⟨hint, hmoment⟩ := power_core_upper_moment μ hα ha ha2 hρ hρ1 hm hgt
      let k : ℕ → ℕ := fun l => l - i
      have hb := window_label_mean σ hi hj hs k
        (fun d => 1 + Real.log ((aw : ℝ) / (d : ℝ)) / Real.log 2) hint
        (fun l _ => hs.mono fun d hd hdl => band_upper_label hi hdl hd.2)
      have hmean := hnormalize k (hb.trans hmoment)
      have hinj : Function.Injective (fun l : S => k l) := by
        intro x y hxy
        apply Subtype.ext
        have hx := (Finset.mem_Icc.1 x.2).1
        have hy := (Finset.mem_Icc.1 y.2).1
        dsimp [k] at hxy
        omega
      have hh := finite_entropy_mean_bound hp hsum (fun l : S => k l) hinj hm0 hmean
      rw [show 1 + 2 / |α - 2| + 1 = 2 + 2 / |α - 2| by ring] at hh
      simpa only [add_comm] using hh

theorem effective_scales_window {α ρ : ℝ} :
    effectiveScales α ρ = if |α - 2| = 0 then 1 + Real.logb 2 (1/ρ) / α
      else min (1 + Real.logb 2 (1/ρ) / α) (max 1 (1/|α - 2|)) := by
  by_cases h : α = 2
  · simp [h, effectiveScales]
  · simp [effectiveScales, h, abs_eq_zero, sub_eq_zero]

/-- The frozen uniform core-cost and entropy target, including exponent two
and arbitrary dyadic alignment of the scale parameter. -/
theorem power_core : PowerCoreStatement := by
  intro μ _ α a ρ hα _ha4 ha ha2 hρ hρ1 hm
  obtain ⟨hE, hatom, hcount, hmoment⟩ := power_core_entropy_estimates μ hα ha ha2 hρ hρ1 hm
  have hM := (power_window_length hα ha hρ hρ1).1
  have hN := effective_scales_ge_one hα hρ hρ1
  have hNM : effectiveScales α ρ ≤ 1 + Real.logb 2 (1/ρ) / α := by
    rw [effective_scales_window]
    split_ifs
    · exact le_rfl
    · exact min_le_left _ _
  have hNs : 2 ≤ effectiveScales α ρ → effectiveScales α ρ * |α - 2| ≤ 1 := by
    intro h2
    by_cases hs : |α - 2| = 0
    · simp [hs]
    · have hs0 : 0 < |α - 2| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hs)
      have hn : effectiveScales α ρ ≤ max 1 (1/|α - 2|) := by
        rw [effective_scales_window, ite_eq_right hs]
        exact min_le_right _ _
      have hge : 1 ≤ 1/|α - 2| := by
        by_contra h
        rw [max_eq_left (not_le.1 h).le] at hn
        linarith
      rw [max_eq_right hge] at hn
      exact (le_div_iff₀ hs0).1 hn
  refine ⟨power_core_cost μ hα ha ha2 hρ hρ1 hm,
    entropy_window_lower hM (abs_nonneg _) hN hNM hNs hE hatom, ?_⟩
  rw [effective_scales_window]
  apply entropy_window_upper hM (abs_nonneg _) hcount
  intro hs
  exact hmoment (by intro h; simp [h] at hs)

end ThresholdHC.PowerWindow
