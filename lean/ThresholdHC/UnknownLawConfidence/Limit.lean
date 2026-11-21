import ThresholdHC.UnknownLawConfidence.Controller

/-! The stage bound tends to zero for every probability law of positive gaps.

`n_j >= j + 1` grows without bound and `m_j >= n_j`. Since
`H(k,e)/k <= sqrt(ceil(log2(1/e))/(2k)) + 1/k`, the radius `r_j`, the
sampling allowance `a_j` and `tau_j = 1/n_j` tend to zero, using only that
`log x / x` tends to zero. Then `P(D <= 2 r_j)` tends to zero by dominated
convergence because every gap is positive. On the success event the reported
half-width is at most half of the bound of every completed stage, so it tends
to zero as the budget grows. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Real Set
open scoped Topology
namespace ThresholdHC.UnknownLawConfidence
open ThresholdHC.Tier6 ThresholdHC.HardBudget

theorem itemCount_tendsto : Tendsto (fun j => (itemCount j : ℝ)) atTop atTop := by
  apply tendsto_atTop_mono _ tendsto_natCast_atTop_atTop
  intro j
  exact_mod_cast (Nat.le_succ j).trans (succ_le_itemCount j)

theorem tolerance_tendsto : Tendsto tolerance atTop (𝓝 0) := by
  have h := tendsto_inv_atTop_zero.comp itemCount_tendsto
  refine h.congr (fun j => ?_)
  simp [tolerance]

theorem log_bound_tendsto (A B : ℝ) :
    Tendsto (fun x : ℝ => Real.sqrt ((A + B * Real.log x) / (2 * x)) + 1 / x)
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hin : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hq : Tendsto (fun x : ℝ => (A + B * Real.log x) / (2 * x)) atTop (𝓝 0) := by
    have h := (hin.const_mul (A / 2)).add (hlog.const_mul (B / 2))
    rw [mul_zero, mul_zero, add_zero] at h
    refine h.congr (fun x => ?_)
    ring
  have hs : Tendsto (fun x : ℝ => Real.sqrt ((A + B * Real.log x) / (2 * x))) atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hq
    rwa [Real.sqrt_zero] at h
  have h := hs.add (hin.congr (fun x => (one_div x).symm))
  rwa [add_zero] at h

/-- `H(k,e)/k <= sqrt(ceil(log2(1/e))/(2k)) + 1/k`, in a form ready for limits. -/
theorem hoeffding_ratio_le {k : ℕ} {e x A B : ℝ} (hx1 : 1 ≤ x) (hk : x ≤ k)
    (he : 0 < e) (he1 : e ≤ 1) (hL : Real.logb 2 (1 / e) ≤ A + B * Real.log x) :
    (hoeffdingCount k e : ℝ) / k ≤
      Real.sqrt ((A + 1 + B * Real.log x) / (2 * x)) + 1 / x := by
  have hx0 : 0 < x := by linarith
  have hk0 : (0 : ℝ) < k := hx0.trans_le hk
  set L : ℝ := (⌈Real.logb 2 (1 / e)⌉₊ : ℝ) with hLdef
  have hl0 : 0 ≤ Real.logb 2 (1 / e) := by
    apply Real.logb_nonneg (by norm_num)
    rw [le_div_iff₀ he]
    linarith
  have hLlt : L < Real.logb 2 (1 / e) + 1 := Nat.ceil_lt_add_one hl0
  have hL0 : 0 ≤ L := Nat.cast_nonneg _
  have hH := hoeffdingCount_lt k e
  rw [← hLdef] at hH
  have hsq : Real.sqrt ((k : ℝ) * L / 2) / k = Real.sqrt (L / (2 * k)) := by
    calc Real.sqrt ((k : ℝ) * L / 2) / k
        = Real.sqrt ((k : ℝ) * L / 2) / Real.sqrt ((k : ℝ) ^ 2) := by
          rw [Real.sqrt_sq hk0.le]
      _ = Real.sqrt (((k : ℝ) * L / 2) / (k : ℝ) ^ 2) :=
          (Real.sqrt_div' _ (by positivity)).symm
      _ = Real.sqrt (L / (2 * k)) := by
          congr 1
          field_simp
  have h1 : (hoeffdingCount k e : ℝ) / k ≤ Real.sqrt (L / (2 * k)) + 1 / k := by
    rw [← hsq, ← add_div]
    exact div_le_div_of_nonneg_right hH.le hk0.le
  have h2 : L / (2 * k) ≤ (A + 1 + B * Real.log x) / (2 * x) := by
    calc L / (2 * k) ≤ L / (2 * x) :=
          div_le_div_of_nonneg_left hL0 (by positivity) (by linarith)
      _ ≤ (A + 1 + B * Real.log x) / (2 * x) :=
          div_le_div_of_nonneg_right (by linarith) (by positivity)
  have h3 : 1 / (k : ℝ) ≤ 1 / x := one_div_le_one_div_of_le hx0 hk
  have h4 := Real.sqrt_le_sqrt h2
  linarith

theorem hoeffding_ratio_tendsto (k : ℕ → ℕ) (e x : ℕ → ℝ) (A B : ℝ)
    (hx : Tendsto x atTop atTop) (hx1 : ∀ j, 1 ≤ x j) (hk : ∀ j, x j ≤ k j)
    (he : ∀ j, 0 < e j) (he1 : ∀ j, e j ≤ 1)
    (hL : ∀ j, Real.logb 2 (1 / e j) ≤ A + B * Real.log (x j)) :
    Tendsto (fun j => (hoeffdingCount (k j) (e j) : ℝ) / k j) atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    ((log_bound_tendsto (A + 1) B).comp hx) (fun j => by positivity)
    (fun j => hoeffding_ratio_le (hx1 j) (hk j) (he j) (he1 j) (hL j))

theorem radius_tendsto : Tendsto radius atTop (𝓝 0) := by
  apply hoeffding_ratio_tendsto flipCount tolerance (fun j => (itemCount j : ℝ)) 0
    (1 / Real.log 2) itemCount_tendsto
  · intro j
    exact_mod_cast (itemCount_pos j)
  · intro j
    exact_mod_cast itemCount_le_flipCount j
  · exact tolerance_pos
  · intro j
    exact (tolerance_le_half j).trans (by norm_num)
  · intro j
    rw [tolerance, one_div_one_div, Real.logb, zero_add]
    apply le_of_eq
    ring

theorem sampling_tendsto {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    Tendsto (sampling δ) atTop (𝓝 0) := by
  have hx : Tendsto (fun j : ℕ => (j : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  apply hoeffding_ratio_tendsto itemCount (fun j => Anytime.stageFailure δ j / 3)
    (fun j => (j : ℝ) + 1) (Real.log (12 / δ) / Real.log 2) (2 / Real.log 2) hx
  · intro j
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  · intro j
    exact_mod_cast succ_le_itemCount j
  · intro j
    have := Anytime.stageFailure_pos hδ j
    positivity
  · intro j
    have := Anytime.stageFailure_le hδ.le j
    linarith
  · intro j
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hy : 1 / (Anytime.stageFailure δ j / 3) = 3 * (((j : ℝ) + 1) * ((j : ℝ) + 2)) / δ := by
      unfold Anytime.stageFailure
      field_simp
    have hle : 3 * (((j : ℝ) + 1) * ((j : ℝ) + 2)) / δ ≤ 12 / δ * ((j : ℝ) + 1) ^ 2 := by
      rw [div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ hδ.le
      nlinarith
    have hlog : Real.log (3 * (((j : ℝ) + 1) * ((j : ℝ) + 2)) / δ) ≤
        Real.log (12 / δ) + 2 * Real.log ((j : ℝ) + 1) := by
      calc Real.log (3 * (((j : ℝ) + 1) * ((j : ℝ) + 2)) / δ)
          ≤ Real.log (12 / δ * ((j : ℝ) + 1) ^ 2) := Real.log_le_log (by positivity) hle
        _ = Real.log (12 / δ) + 2 * Real.log ((j : ℝ) + 1) := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
          push_cast
          ring
    rw [hy, Real.logb]
    calc Real.log (3 * (((j : ℝ) + 1) * ((j : ℝ) + 2)) / δ) / Real.log 2
        ≤ (Real.log (12 / δ) + 2 * Real.log ((j : ℝ) + 1)) / Real.log 2 :=
          div_le_div_of_nonneg_right hlog h2.le
      _ = Real.log (12 / δ) / Real.log 2 + 2 / Real.log 2 * Real.log ((j : ℝ) + 1) := by
          ring

/-- The mass of gaps below a null sequence tends to zero. -/
theorem smallGap_tendsto (μ : Measure Gap) [IsFiniteMeasure μ] {s : ℕ → ℝ}
    (hs : Tendsto s atTop (𝓝 0)) :
    Tendsto (fun j => μ.real {d : Gap | (d : ℝ) ≤ s j}) atTop (𝓝 0) := by
  let S (j : ℕ) := {d : Gap | (d : ℝ) ≤ s j}
  have hS (j : ℕ) : MeasurableSet (S j) := measurableSet_le measurable_subtype_coe measurable_const
  let F (j : ℕ) := (S j).indicator (fun _ : Gap => (1 : ℝ))
  have hm (j : ℕ) : Measurable (F j) := measurable_const.indicator (hS j)
  have hb (j : ℕ) : ∀ᵐ d ∂μ, ‖F j d‖ ≤ (1 : ℝ) := by
    apply ae_of_all
    intro d
    by_cases hd : d ∈ S j <;> simp [F, hd]
  have hl (d : Gap) : Tendsto (fun j => F j d) atTop (𝓝 (0 : ℝ)) := by
    have he := hs.eventually (gt_mem_nhds d.property.1)
    apply tendsto_congr' (he.mono (fun j hj => show F j d = (0 : ℝ) by
      exact indicator_of_notMem (show d ∉ S j from not_le_of_gt hj) _)) |>.mpr
    exact tendsto_const_nhds
  have ht := tendsto_integral_of_dominated_convergence (μ := μ) (fun _ : Gap => (1 : ℝ))
    (F := F) (f := fun _ => (0 : ℝ)) (fun j => (hm j).aestronglyMeasurable)
    (integrable_const 1) hb (ae_of_all _ hl)
  have hi (j : ℕ) : (∫ d, F j d ∂μ) = μ.real (S j) := by
    simpa only [smul_eq_mul, mul_one] using integral_indicator_const (μ := μ) (1 : ℝ) (hS j)
  simpa only [hi, integral_zero] using ht

theorem widthBound_tendsto (μ : Measure Gap) [IsProbabilityMeasure μ] {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) : Tendsto (widthBound μ δ) atTop (𝓝 0) := by
  have hr : Tendsto (fun j => 2 * radius j) atTop (𝓝 0) := by
    simpa using radius_tendsto.const_mul 2
  have h := ((smallGap_tendsto μ hr).add ((sampling_tendsto hδ hδ1).const_mul 3)).add
    (tolerance_tendsto.const_mul 3)
  simp only [mul_zero, add_zero] at h
  exact h

theorem le_stageCount {J B : ℕ} (h : paid J ≤ B) : J ≤ stageCount (B : ℝ) := by
  have hf : paid J ≤ ⌊(B : ℝ)⌋₊ := by simpa using h
  exact Nat.le_findGreatest ((index_le_paid J).trans hf) hf

theorem halfWidth_nonneg (I : ℝ × ℝ) : 0 ≤ Anytime.halfWidth I := by
  unfold Anytime.halfWidth
  exact div_nonneg (le_max_left _ _) (by norm_num)

/-- On the success event the reported half-width tends to zero. -/
theorem successEvent_halfWidth_tendsto (μ : Measure Gap) [IsProbabilityMeasure μ]
    (q : SignLaw) {δ u : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {z : Seed × Table}
    (hz : z ∈ successEvent μ q δ u) :
    Tendsto (fun B : ℕ => Anytime.halfWidth (interval δ u B z)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨J, hJ⟩ := ((widthBound_tendsto μ hδ hδ1).eventually (gt_mem_nhds hε)).exists
  refine ⟨paid (J + 1), fun B hB => ?_⟩
  have hc : J < stageCount (B : ℝ) := le_stageCount hB
  have hw := hz.2 B J hc
  have h0 := halfWidth_nonneg (interval δ u B z)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
  linarith

end ThresholdHC.UnknownLawConfidence
