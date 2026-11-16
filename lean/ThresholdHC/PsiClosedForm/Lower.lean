import ThresholdHC.PsiClosedForm.Order
import ThresholdHC.Tier3.Optimizer

/-! The lower half of (W2): `Q⁰ ≤ √2 Ψ`.

Let `c` be the cutoff of the checked optimizer, so that `v = min{1, c²/d²}` has
mass `ρ`, and write `a = √v = min{1, c/d}` and `k = min{1, h/d}`. The cutoff
lies strictly below the quantile threshold, so the core `κ` lives on `d > c`.

If `h ≥ c` the objective of `v` is `ρ`. If `h < c` its integrand is `a k`. On
the core `a k = (h/c) v` and `d^{-2} = v/c²`, so with `w = ∫ v dκ` the core
pays `(h/c) w` and `A_κ = w/c²`. On the tail `k ≥ (h/c) a`, with equality
where `a < 1`, hence `k (1 - √2 a) ≤ (h/c) a (1 - √2 a)` pointwise. The budget
identity is `∫ a² dν + w = ρ`, and the Cauchy–Schwarz inequality on the tail,
of mass `ρ`, gives `∫ a dν ≤ √(ρ ∫ a² dν)`. Since
`√(ρ x) + √(ρ (ρ - x)) ≤ √2 ρ`, the three facts combine to
`T_h + h √(ρ A_κ) ≤ √2 V`.

The paper's proof splits the tail at `c` and uses five integrals; this
arrangement uses the same allocation and the same two Cauchy–Schwarz steps
without the split. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ThresholdHC.PsiClosedForm
open ThresholdHC.Tier6 ThresholdHC.RareAboveTwo ThresholdHC.EntropyTail
open ThresholdHC.EntropyTailQuantile (quantileTail quantileCore quantileThreshold
  quantileTail_le quantileTail_mass quantileTail_add_core quantileTail_support
  quantileCore_support)

/-- The square root `min{1, c/d}` of the optimizer's allocation. -/
def rootAllocation (c : ℝ) (d : Gap) : ℝ := min 1 (c / (d : ℝ))

/-- The truncated inverse-gap kernel `min{1, h/d}`. -/
def tailKernel (h : ℝ) (d : Gap) : ℝ := min 1 (h / (d : ℝ))

theorem rootAllocation_pos {c : ℝ} (hc : 0 < c) (d : Gap) : 0 < rootAllocation c d :=
  lt_min one_pos (div_pos hc d.2.1)

theorem rootAllocation_le_one (c : ℝ) (d : Gap) : rootAllocation c d ≤ 1 := min_le_left _ _

theorem measurable_rootAllocation (c : ℝ) : Measurable (rootAllocation c) :=
  measurable_const.min (measurable_const.div measurable_subtype_coe)

theorem tailKernel_nonneg {h : ℝ} (hh : 0 ≤ h) (d : Gap) : 0 ≤ tailKernel h d :=
  le_min zero_le_one (div_nonneg hh d.2.1.le)

theorem tailKernel_le_one (h : ℝ) (d : Gap) : tailKernel h d ≤ 1 := min_le_left _ _

theorem measurable_tailKernel (h : ℝ) : Measurable (tailKernel h) :=
  measurable_const.min (measurable_const.div measurable_subtype_coe)

theorem measurable_gapAllocation (c : ℝ) :
    Measurable fun d : Gap => Tier3.allocation c (d : ℝ) :=
  measurable_const.min (measurable_const.div (measurable_subtype_coe.pow_const 2))

/-- A measurable function with values in `[0,1]` is integrable on a finite measure. -/
theorem integrable_unit (σ : Measure Gap) [IsFiniteMeasure σ] {f : Gap → ℝ}
    (hf : Measurable f) (h0 : ∀ d, 0 ≤ f d) (h1 : ∀ d, f d ≤ 1) : Integrable f σ :=
  (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun d => by
      rw [Real.norm_eq_abs, abs_of_nonneg (h0 d)]; exact h1 d)

theorem rootAllocation_sq {c : ℝ} (hc : 0 < c) (d : Gap) :
    rootAllocation c d ^ 2 = Tier3.allocation c (d : ℝ) := by
  have hd := d.2.1
  unfold rootAllocation Tier3.allocation
  rw [← div_pow]
  rcases le_total (c / (d : ℝ)) 1 with hle | hge
  · rw [min_eq_right hle, min_eq_right (pow_le_one₀ (div_pos hc hd).le hle)]
  · rw [min_eq_left hge, min_eq_left (one_le_pow₀ hge), one_pow]

/-- Below the cutoff the objective integrand of the allocation is `a k`. -/
theorem payoff_eq {c h : ℝ} (hc : 0 < c) (hhc : h < c) (d : Gap) :
    min (Tier3.allocation c (d : ℝ))
        (h * Real.sqrt (Tier3.allocation c (d : ℝ)) / (d : ℝ)) =
      rootAllocation c d * tailKernel h d := by
  have hd := d.2.1
  have ha := (rootAllocation_pos hc d).le
  rw [← rootAllocation_sq hc d, Real.sqrt_sq ha]
  have e : h * rootAllocation c d / (d : ℝ) = rootAllocation c d * (h / (d : ℝ)) := by ring
  rw [e, sq, ← mul_min_of_nonneg _ _ ha]
  congr 1
  unfold rootAllocation tailKernel
  rw [min_assoc, min_eq_right (div_le_div_of_nonneg_right hhc.le hd.le)]

/-- `k (1 - √2 a) ≤ (h/c) a (1 - √2 a)` at every gap. -/
theorem kernel_pointwise {c h : ℝ} (hh : 0 < h) (hhc : h < c) (d : Gap) :
    tailKernel h d - Real.sqrt 2 * (rootAllocation c d * tailKernel h d) ≤
      h / c * (rootAllocation c d - Real.sqrt 2 * rootAllocation c d ^ 2) := by
  have hd := d.2.1
  have hc : 0 < c := hh.trans hhc
  have h2 : 1 ≤ Real.sqrt 2 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by norm_num)
  unfold rootAllocation tailKernel
  rcases le_or_gt (d : ℝ) c with hdc | hcd
  · rw [min_eq_left ((one_le_div hd).2 hdc)]
    have hk : h / c ≤ min 1 (h / (d : ℝ)) :=
      le_min ((div_le_one hc).2 hhc.le) (div_le_div_of_nonneg_left hh.le hd hdc)
    nlinarith [mul_nonneg (sub_nonneg.2 hk) (sub_nonneg.2 h2)]
  · rw [min_eq_right ((div_le_one hd).2 hcd.le),
      min_eq_right ((div_le_one hd).2 (hhc.trans hcd).le)]
    apply le_of_eq
    field_simp

/-- Above the cutoff: `a k = (h/c) v` and `d^{-2} = v/c²`. -/
theorem above_cutoff {c h : ℝ} (hh : 0 < h) (hhc : h < c) (d : Gap) (hcd : c < (d : ℝ)) :
    rootAllocation c d * tailKernel h d = h / c * Tier3.allocation c (d : ℝ) ∧
    ((d : ℝ)⁻¹) ^ 2 = Tier3.allocation c (d : ℝ) / c ^ 2 := by
  have hd := d.2.1
  have hc : 0 < c := hh.trans hhc
  have hv : Tier3.allocation c (d : ℝ) = c ^ 2 / (d : ℝ) ^ 2 := by
    unfold Tier3.allocation
    exact min_eq_right ((div_le_one (pow_pos hd 2)).2 (pow_le_pow_left₀ hc.le hcd.le 2))
  rw [hv]
  unfold rootAllocation tailKernel
  rw [min_eq_right ((div_le_one hd).2 hcd.le),
    min_eq_right ((div_le_one hd).2 (hhc.trans hcd).le)]
  constructor <;> field_simp

/-- The optimizer's cutoff lies strictly below every threshold that carries a
submeasure of mass `ρ < 1` whose complement in `μ` is the rest of the law. -/
theorem cutoff_lt_threshold (μ ν κ : Measure Gap) [IsProbabilityMeasure μ]
    [IsFiniteMeasure ν] [IsFiniteMeasure κ] {ρ c t : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hc : 0 < c) (hadd : ν + κ = μ) (hmass : ν univ = ENNReal.ofReal ρ)
    (hνt : ∀ᵐ d : Gap ∂ν, (d : ℝ) ≤ t)
    (hm : ∫ d : Gap, Tier3.allocation c (d : ℝ) ∂μ = ρ) : c < t := by
  by_contra hnot
  have htc : t ≤ c := not_lt.1 hnot
  have hvi : ∀ (σ : Measure Gap) [IsFiniteMeasure σ],
      Integrable (fun d : Gap => Tier3.allocation c (d : ℝ)) σ := fun σ _ =>
    integrable_unit σ (measurable_gapAllocation c) (fun d => Tier3.allocation_nonneg c d)
      (fun d => Tier3.allocation_le_one c d)
  have hsplit : ∫ d : Gap, Tier3.allocation c (d : ℝ) ∂μ =
      ∫ d : Gap, Tier3.allocation c (d : ℝ) ∂ν + ∫ d : Gap, Tier3.allocation c (d : ℝ) ∂κ := by
    rw [← hadd]
    exact integral_add_measure (hvi ν) (hvi κ)
  have hνreal : ν.real univ = ρ := by
    rw [measureReal_def, hmass, ENNReal.toReal_ofReal hρ.le]
  have hν1 : ∫ d : Gap, Tier3.allocation c (d : ℝ) ∂ν = ρ := by
    have : ∫ d : Gap, Tier3.allocation c (d : ℝ) ∂ν = ∫ _d : Gap, (1 : ℝ) ∂ν :=
      integral_congr_ae (hνt.mono fun d hd => Tier3.allocation_eq_one d.2.1 (hd.trans htc))
    rw [this, integral_const, smul_eq_mul, mul_one, hνreal]
  have hκ0 : ∫ d : Gap, Tier3.allocation c (d : ℝ) ∂κ = 0 := by linarith
  have hae := (integral_eq_zero_iff_of_nonneg
    (fun d : Gap => Tier3.allocation_nonneg c (d : ℝ)) (hvi κ)).1 hκ0
  have hpos : ∀ d : Gap, 0 < Tier3.allocation c (d : ℝ) := fun d => by
    rw [← rootAllocation_sq hc d]
    exact pow_pos (rootAllocation_pos hc d) 2
  have hfalse : ∀ᵐ _d : Gap ∂κ, False := hae.mono fun d hd => (hpos d).ne' hd
  have hκ : κ = 0 := ae_eq_bot.1 (Filter.eventually_false_iff_eq_bot.1 hfalse)
  have h1 : μ univ = ENNReal.ofReal ρ := by rw [← hadd, hκ, add_zero, hmass]
  rw [measure_univ] at h1
  have h2 := congrArg ENNReal.toReal h1
  rw [ENNReal.toReal_one, ENNReal.toReal_ofReal hρ.le] at h2
  linarith

/-- `√(ρ x) + √(ρ (ρ - x)) ≤ √2 ρ`, in the form used below. -/
theorem root_sum_le {ρ s x w : ℝ} (hρ : 0 < ρ) (hs : 0 ≤ s) (hw : 0 ≤ w)
    (hsx : s ^ 2 ≤ ρ * x) (hxw : x + w = ρ) :
    s + Real.sqrt (ρ * w) ≤ Real.sqrt 2 * ρ := by
  have hr := Real.sqrt_nonneg (ρ * w)
  have hr2 : Real.sqrt (ρ * w) ^ 2 = ρ * w := Real.sq_sqrt (mul_nonneg hρ.le hw)
  have h22 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  by_contra hnot
  have hlt : Real.sqrt 2 * ρ < s + Real.sqrt (ρ * w) := not_le.1 hnot
  have hsq := pow_lt_pow_left₀ hlt (mul_nonneg (Real.sqrt_nonneg 2) hρ.le) two_ne_zero
  have hw' : w = ρ - x := by linarith
  subst hw'
  nlinarith [sq_nonneg (s - Real.sqrt (ρ * (ρ - x)))]

/-- The real inequality behind `Q⁰ ≤ √2 Ψ` below the cutoff, for any split
`μ = ν + κ` whose first part has mass `ρ` and whose second lives above `c`. -/
theorem closed_form_real (μ ν κ : Measure Gap) [IsProbabilityMeasure μ]
    [IsFiniteMeasure ν] [IsFiniteMeasure κ] {ρ c h : ℝ} (hρ : 0 < ρ)
    (hh : 0 < h) (hhc : h < c) (hadd : ν + κ = μ) (hmass : ν univ = ENNReal.ofReal ρ)
    (hκc : ∀ᵐ d : Gap ∂κ, c < (d : ℝ))
    (hm : ∫ d : Gap, Tier3.allocation c (d : ℝ) ∂μ = ρ) :
    ∃ w : ℝ, 0 ≤ w ∧ inverseSquareCost κ = ENNReal.ofReal (w / c ^ 2) ∧
      ∫ d, tailKernel h d ∂ν + h / c * Real.sqrt (ρ * w) ≤
        Real.sqrt 2 * Tier3.rareObjective μ (fun d : Gap => (d : ℝ)) h
          (fun d : Gap => Tier3.allocation c (d : ℝ)) := by
  have hc : 0 < c := hh.trans hhc
  have hvm := measurable_gapAllocation c
  have ham := measurable_rootAllocation c
  have hkm := measurable_tailKernel h
  have ha0 : ∀ d, 0 ≤ rootAllocation c d := fun d => (rootAllocation_pos hc d).le
  have ha1 := rootAllocation_le_one c
  have hk0 : ∀ d, 0 ≤ tailKernel h d := tailKernel_nonneg hh.le
  have hk1 := tailKernel_le_one h
  have hvi : ∀ (σ : Measure Gap) [IsFiniteMeasure σ],
      Integrable (fun d : Gap => Tier3.allocation c (d : ℝ)) σ := fun σ _ =>
    integrable_unit σ hvm (fun d => Tier3.allocation_nonneg c d)
      (fun d => Tier3.allocation_le_one c d)
  have hai : Integrable (fun d => rootAllocation c d) ν := integrable_unit ν ham ha0 ha1
  have hki : Integrable (fun d => tailKernel h d) ν := integrable_unit ν hkm hk0 hk1
  have haki : ∀ (σ : Measure Gap) [IsFiniteMeasure σ],
      Integrable (fun d => rootAllocation c d * tailKernel h d) σ := fun σ _ =>
    integrable_unit σ (ham.mul hkm) (fun d => mul_nonneg (ha0 d) (hk0 d))
      (fun d => mul_le_one₀ (ha1 d) (hk0 d) (hk1 d))
  have ha2i : Integrable (fun d => rootAllocation c d ^ 2) ν :=
    integrable_unit ν (ham.pow_const 2) (fun d => sq_nonneg _)
      (fun d => pow_le_one₀ (ha0 d) (ha1 d))
  refine ⟨∫ d : Gap, Tier3.allocation c (d : ℝ) ∂κ,
    integral_nonneg fun d => Tier3.allocation_nonneg c d, ?_, ?_⟩
  · unfold inverseSquareCost
    have hcongr : ∫⁻ d : Gap, ENNReal.ofReal (((d : ℝ)⁻¹) ^ 2) ∂κ =
        ∫⁻ d : Gap, ENNReal.ofReal (Tier3.allocation c (d : ℝ) / c ^ 2) ∂κ :=
      lintegral_congr_ae (hκc.mono fun d hd => by
        show ENNReal.ofReal (((d : ℝ)⁻¹) ^ 2) = ENNReal.ofReal (Tier3.allocation c (d : ℝ) / c ^ 2)
        rw [(above_cutoff hh hhc d hd).2])
    rw [hcongr, ← ofReal_integral_eq_lintegral_ofReal ((hvi κ).div_const _)
      (Filter.Eventually.of_forall fun d =>
        div_nonneg (Tier3.allocation_nonneg c d) (sq_nonneg c)), integral_div]
  · set w := ∫ d : Gap, Tier3.allocation c (d : ℝ) ∂κ with hw
    set s := ∫ d, rootAllocation c d ∂ν with hs
    set x := ∫ d, rootAllocation c d ^ 2 ∂ν with hx
    set T := ∫ d, tailKernel h d ∂ν with hT
    set AK := ∫ d, rootAllocation c d * tailKernel h d ∂ν with hAK
    have hw0 : 0 ≤ w := integral_nonneg fun d => Tier3.allocation_nonneg c d
    have hs0 : 0 ≤ s := integral_nonneg ha0
    have hνreal : ν.real univ = ρ := by
      rw [measureReal_def, hmass, ENNReal.toReal_ofReal hρ.le]
    -- The objective of the allocation.
    have hV : Tier3.rareObjective μ (fun d : Gap => (d : ℝ)) h
        (fun d : Gap => Tier3.allocation c (d : ℝ)) = AK + h / c * w := by
      have h1 : Tier3.rareObjective μ (fun d : Gap => (d : ℝ)) h
          (fun d : Gap => Tier3.allocation c (d : ℝ)) =
          ∫ d, rootAllocation c d * tailKernel h d ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall fun d => payoff_eq hc hhc d)
      have h2 : ∫ d, rootAllocation c d * tailKernel h d ∂μ =
          AK + ∫ d, rootAllocation c d * tailKernel h d ∂κ := by
        rw [← hadd]
        exact integral_add_measure (haki ν) (haki κ)
      have h3 : ∫ d, rootAllocation c d * tailKernel h d ∂κ = h / c * w := by
        rw [hw, ← integral_const_mul]
        exact integral_congr_ae (hκc.mono fun d hd => (above_cutoff hh hhc d hd).1)
      rw [h1, h2, h3]
    -- The budget identity.
    have hbudget : x + w = ρ := by
      have h1 : ∫ d : Gap, Tier3.allocation c (d : ℝ) ∂μ =
          ∫ d : Gap, Tier3.allocation c (d : ℝ) ∂ν + w := by
        rw [← hadd]
        exact integral_add_measure (hvi ν) (hvi κ)
      have h2 : ∫ d : Gap, Tier3.allocation c (d : ℝ) ∂ν = x :=
        integral_congr_ae (Filter.Eventually.of_forall fun d => (rootAllocation_sq hc d).symm)
      linarith
    -- Cauchy–Schwarz on the tail.
    have hcs : s ^ 2 ≤ ρ * x := by
      have hnn : 0 ≤ ∫ d, (ρ ^ 2 * rootAllocation c d ^ 2 - 2 * ρ * s * rootAllocation c d
          + s ^ 2) ∂ν :=
        integral_nonneg fun d => by
          have : ρ ^ 2 * rootAllocation c d ^ 2 - 2 * ρ * s * rootAllocation c d + s ^ 2 =
              (ρ * rootAllocation c d - s) ^ 2 := by ring
          rw [this]
          exact sq_nonneg _
      have hexp : ∫ d, (ρ ^ 2 * rootAllocation c d ^ 2 - 2 * ρ * s * rootAllocation c d
          + s ^ 2) ∂ν = ρ ^ 2 * x - 2 * ρ * s * s + ρ * s ^ 2 := by
        rw [integral_add ((ha2i.const_mul _).sub (hai.const_mul _)) (integrable_const _),
          integral_sub (ha2i.const_mul _) (hai.const_mul _), integral_const_mul,
          integral_const_mul, integral_const, smul_eq_mul, hνreal]
      rw [hexp] at hnn
      nlinarith
    -- The pointwise comparison, integrated over the tail.
    have hint : T - Real.sqrt 2 * AK ≤ h / c * (s - Real.sqrt 2 * x) := by
      have hmono : ∫ d, (tailKernel h d - Real.sqrt 2 * (rootAllocation c d * tailKernel h d)) ∂ν ≤
          ∫ d, h / c * (rootAllocation c d - Real.sqrt 2 * rootAllocation c d ^ 2) ∂ν :=
        integral_mono (hki.sub ((haki ν).const_mul _))
          ((hai.sub (ha2i.const_mul _)).const_mul _) (kernel_pointwise hh hhc)
      rw [integral_sub hki ((haki ν).const_mul _), integral_const_mul, integral_const_mul,
        integral_sub hai (ha2i.const_mul _), integral_const_mul] at hmono
      exact hmono
    have hroot := root_sum_le hρ hs0 hw0 hcs hbudget
    have hhc0 : 0 < h / c := div_pos hh hc
    rw [hV]
    have hx' : x = ρ - w := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hroot hhc0.le]

end ThresholdHC.PsiClosedForm
