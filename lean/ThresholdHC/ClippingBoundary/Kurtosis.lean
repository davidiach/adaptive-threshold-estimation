import ThresholdHC.ClippingBoundary.Pointwise

/-! The bounded-kurtosis transfer.

Put `X = F - θ` and `v = Var F = E X²`. Integrating `quartic_young` at
`s = √(Kv)` gives `v ≤ K (E|X|)²`. Since `E X = 0`, the positive and the
negative part of `X` both have mean `m = E|X|/2`, so `v ≤ 4Km²`. For the part
`Y` directed toward the farther endpoint of `[0,ρ]`, `clip_lower_pos` or
`clip_lower_neg` bounds the clipped squared error below by `min(Y,ρ/2)²`.
`one_sided_floor` integrates `truncation_lower` (with `t = 1` or
`t = 2cm/v`, `c = ρ/2`) and `tangent_lower`, and gives
`min(v,ρ²) ≤ 256K² E min(Y,ρ/2)²`. -/
noncomputable section
namespace ThresholdHC.ClippingBoundary
open MeasureTheory
open ThresholdHC.Tier6 ThresholdHC.HardBudget

section Real
variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The truncated second moment of one nonnegative part. -/
theorem one_sided_floor (Y : Ω → ℝ) (hY0 : ∀ ω, 0 ≤ Y ω) (hYi : Integrable Y P)
    (hY2 : Integrable (fun ω => Y ω ^ 2) P) {v K c : ℝ} (hK : 1 ≤ K) (hc : 0 ≤ c)
    (hv2 : ∫ ω, Y ω ^ 2 ∂P ≤ v) (hvm : v ≤ 4 * K * (∫ ω, Y ω ∂P) ^ 2) :
    Integrable (fun ω => min (Y ω) c ^ 2) P ∧
      min v ((2 * c) ^ 2) ≤ 256 * K ^ 2 * ∫ ω, min (Y ω) c ^ 2 ∂P := by
  have hmeas : AEStronglyMeasurable (fun ω => min (Y ω) c) P :=
    (continuous_id.min continuous_const).comp_aestronglyMeasurable hYi.aestronglyMeasurable
  have hmin0 : ∀ ω, 0 ≤ min (Y ω) c := fun ω => le_min (hY0 ω) hc
  have hminY : ∀ ω, min (Y ω) c ≤ Y ω := fun ω => min_le_left _ _
  have hZi : Integrable (fun ω => min (Y ω) c) P := by
    refine hYi.mono hmeas (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hmin0 ω), abs_of_nonneg (hY0 ω)]
    exact hminY ω
  have hZ2 : Integrable (fun ω => min (Y ω) c ^ 2) P := by
    refine hY2.mono (hmeas.pow 2) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
      abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (hmin0 ω) (hminY ω) 2
  refine ⟨hZ2, ?_⟩
  have hint0 : 0 ≤ ∫ ω, min (Y ω) c ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
  have hv0 : 0 ≤ v := (integral_nonneg fun ω => sq_nonneg (Y ω)).trans hv2
  rcases hc.eq_or_lt with hc0 | hcpos
  · rw [← hc0]
    simp only [mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, min_eq_right hv0]
    positivity
  set m := ∫ ω, Y ω ∂P with hm
  set L := ∫ ω, min (Y ω) c ∂P with hL
  have hm0 : 0 ≤ m := integral_nonneg hY0
  -- the truncated mean
  have key : ∀ t : ℝ, t ≤ 1 → 4 * c * t * m - t ^ 2 * v ≤ 4 * c * L := by
    intro t ht
    have h : ∫ ω, (4 * c * t * Y ω - t ^ 2 * Y ω ^ 2) ∂P ≤ ∫ ω, 4 * c * min (Y ω) c ∂P :=
      integral_mono ((hYi.const_mul (4 * c * t)).sub (hY2.const_mul (t ^ 2)))
        (hZi.const_mul (4 * c)) (fun ω => truncation_lower (Y ω) c t (hY0 ω) hcpos ht)
    rw [integral_sub (hYi.const_mul _) (hY2.const_mul _), integral_const_mul,
      integral_const_mul, integral_const_mul] at h
    have ht2 : t ^ 2 * ∫ ω, Y ω ^ 2 ∂P ≤ t ^ 2 * v :=
      mul_le_mul_of_nonneg_left hv2 (sq_nonneg t)
    linarith
  -- the truncated second moment
  have htan : L ^ 2 ≤ ∫ ω, min (Y ω) c ^ 2 ∂P := by
    have h : ∫ ω, (2 * L * min (Y ω) c - L ^ 2) ∂P ≤ ∫ ω, min (Y ω) c ^ 2 ∂P :=
      integral_mono ((hZi.const_mul (2 * L)).sub (integrable_const (L ^ 2))) hZ2
        (fun ω => tangent_lower L (min (Y ω) c))
    rw [integral_sub (hZi.const_mul _) (integrable_const _), integral_const_mul,
      integral_const] at h
    simp only [probReal_univ, smul_eq_mul, one_mul] at h
    linarith
  have hK0 : 0 < K := by linarith
  by_cases hcase : v ≤ 2 * c * m
  · have h1 := key 1 le_rfl
    have hLm : m ≤ 2 * L := by nlinarith
    have hL0 : 0 ≤ L := by linarith
    have hsq : m ^ 2 ≤ 4 * L ^ 2 := by nlinarith
    have hKK : 16 * K ≤ 256 * K ^ 2 := by nlinarith
    calc
      min v ((2 * c) ^ 2) ≤ v := min_le_left _ _
      _ ≤ 16 * K * L ^ 2 := by nlinarith
      _ ≤ 256 * K ^ 2 * L ^ 2 := mul_le_mul_of_nonneg_right hKK (sq_nonneg L)
      _ ≤ 256 * K ^ 2 * ∫ ω, min (Y ω) c ^ 2 ∂P :=
        mul_le_mul_of_nonneg_left htan (by positivity)
  · rw [not_le] at hcase
    have hvpos : 0 < v := lt_of_le_of_lt (by positivity) hcase
    set t := 2 * c * m / v with ht
    have ht1 : t ≤ 1 := by
      rw [ht, div_le_one hvpos]
      exact hcase.le
    have h1 := key t ht1
    have heq : 4 * c * t * m - t ^ 2 * v = 4 * c ^ 2 * m ^ 2 / v := by
      rw [ht]
      field_simp
      ring
    rw [heq, div_le_iff₀ hvpos] at h1
    -- `c m² ≤ L v`
    have h2 : c * m ^ 2 ≤ L * v := by nlinarith
    have h3 : c * v ≤ 4 * K * L * v := by nlinarith
    have h4 : c ≤ 4 * K * L := le_of_mul_le_mul_right (by linarith) hvpos
    have h5 : c ^ 2 ≤ 16 * K ^ 2 * L ^ 2 := by nlinarith
    calc
      min v ((2 * c) ^ 2) ≤ (2 * c) ^ 2 := min_le_right _ _
      _ ≤ 256 * K ^ 2 * L ^ 2 := by nlinarith
      _ ≤ 256 * K ^ 2 * ∫ ω, min (Y ω) c ^ 2 ∂P :=
        mul_le_mul_of_nonneg_left htan (by positivity)

/-- The real-valued form of the transfer: a nonnegative integrable minorant of
the clipped squared error whose integral carries the floor. -/
theorem kurtosis_floor_real (F : Ω → ℝ) (θ ρ K : ℝ) (hF : MemLp F 4 P)
    (hmean : (∫ ω, F ω ∂P) = θ) (hθ0 : 0 ≤ θ) (hθρ : θ ≤ ρ) (hK : 1 ≤ K)
    (h4 : (∫ ω, (F ω - θ) ^ 4 ∂P) ≤ K * ProbabilityTheory.variance F P ^ 2) :
    ∃ g : Ω → ℝ, Integrable g P ∧ (∀ ω, 0 ≤ g ω) ∧
      (∀ ω, g ω ≤ (clipEstimate ρ (F ω) - θ) ^ 2) ∧
      min (ProbabilityTheory.variance F P) (ρ ^ 2) ≤ 256 * K ^ 2 * ∫ ω, g ω ∂P := by
  set v := ProbabilityTheory.variance F P with hvdef
  have hρ : 0 ≤ ρ := hθ0.trans hθρ
  have hK0 : 0 < K := by linarith
  set X : Ω → ℝ := fun ω => F ω - θ with hXdef
  have hX : MemLp X 4 P := hF.sub (memLp_const θ)
  have hX2 : MemLp X 2 P := hX.mono_exponent (by norm_num)
  have hX1 : Integrable X P := hX.integrable (by norm_num)
  have hXsq : Integrable (fun ω => X ω ^ 2) P := hX2.integrable_sq
  have hX4 : Integrable (fun ω => X ω ^ 4) P := by
    have hX4' : MemLp X ((4 : ℕ) : ENNReal) P := by exact_mod_cast hX
    refine (hX4'.integrable_norm_pow (by norm_num)).congr (ae_of_all _ fun ω => ?_)
    simp only [Real.norm_eq_abs]
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
  have hXabs : Integrable (fun ω => |X ω|) P := hX1.abs
  have hv : v = ∫ ω, X ω ^ 2 ∂P := by
    rw [hvdef, ProbabilityTheory.variance_eq_integral hF.aestronglyMeasurable.aemeasurable, hmean]
  have hv0 : 0 ≤ v := ProbabilityTheory.variance_nonneg F P
  have hX0 : ∫ ω, X ω ∂P = 0 := by
    rw [hXdef, integral_sub (hF.integrable (by norm_num)) (integrable_const θ), hmean,
      integral_const]
    simp
  -- `v ≤ K (E|X|)²`
  set a := ∫ ω, |X ω| ∂P with ha
  have ha0 : 0 ≤ a := integral_nonneg fun ω => abs_nonneg _
  have hva : v ≤ K * a ^ 2 := by
    rcases hv0.eq_or_lt with hv00 | hvpos
    · rw [← hv00]; positivity
    set s := Real.sqrt (K * v) with hs
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hss : s ^ 2 = K * v := Real.sq_sqrt (by positivity)
    have h : ∫ ω, 3 * s ^ 2 * X ω ^ 2 ∂P ≤ ∫ ω, (2 * s ^ 3 * |X ω| + X ω ^ 4) ∂P :=
      integral_mono (hXsq.const_mul (3 * s ^ 2))
        ((hXabs.const_mul (2 * s ^ 3)).add hX4) (fun ω => quartic_young s (X ω) hs0)
    rw [integral_add (hXabs.const_mul _) hX4, integral_const_mul, integral_const_mul, ← hv,
      ← ha] at h
    have h4' : ∫ ω, X ω ^ 4 ∂P ≤ K * v ^ 2 := h4
    have hs3 : s ^ 3 = s * (K * v) := by rw [← hss]; ring
    rw [hss, hs3] at h
    have hKv : 0 < K * v := by positivity
    have hvsa : v ≤ s * a := by nlinarith
    have hvsa2 : v ^ 2 ≤ s ^ 2 * a ^ 2 := by
      have := pow_le_pow_left₀ hv0 hvsa 2
      rwa [mul_pow] at this
    rw [hss] at hvsa2
    nlinarith
  -- the two parts
  have hP : Integrable (fun ω => max (X ω) 0) P := hX1.pos_part
  have hN : Integrable (fun ω => max (-X ω) 0) P := hX1.neg_part
  have hsum : (∫ ω, max (X ω) 0 ∂P) + ∫ ω, max (-X ω) 0 ∂P = a := by
    rw [← integral_add hP hN]
    exact integral_congr_ae (ae_of_all _ fun ω => max_add_max_neg (X ω))
  have hdiff : (∫ ω, max (X ω) 0 ∂P) - ∫ ω, max (-X ω) 0 ∂P = 0 := by
    have hc : ∫ ω, (max (X ω) 0 - max (-X ω) 0) ∂P = ∫ ω, X ω ∂P :=
      integral_congr_ae (ae_of_all _ fun ω => max_sub_max_neg (X ω))
    rw [← integral_sub hP hN, hc, hX0]
  have hpart_sq : ∀ y : ℝ, max y 0 ^ 2 ≤ y ^ 2 := fun y => by
    rcases le_total 0 y with h | h
    · rw [max_eq_left h]
    · rw [max_eq_right h, zero_pow two_ne_zero]; exact sq_nonneg y
  have hside : ∀ Y : Ω → ℝ, Integrable Y P → (∀ ω, 0 ≤ Y ω) → (∀ ω, Y ω ^ 2 ≤ X ω ^ 2) →
      (∫ ω, Y ω ∂P) = a / 2 →
      Integrable (fun ω => min (Y ω) (ρ / 2) ^ 2) P ∧
        min v (ρ ^ 2) ≤ 256 * K ^ 2 * ∫ ω, min (Y ω) (ρ / 2) ^ 2 ∂P := by
    intro Y hYi hY0 hYX hYm
    have hY2 : Integrable (fun ω => Y ω ^ 2) P := by
      refine hXsq.mono (hYi.aestronglyMeasurable.pow 2) (ae_of_all _ fun ω => ?_)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
        abs_of_nonneg (sq_nonneg _)]
      exact hYX ω
    have hv2 : ∫ ω, Y ω ^ 2 ∂P ≤ v := by
      rw [hv]
      exact integral_mono hY2 hXsq hYX
    have hvm : v ≤ 4 * K * (∫ ω, Y ω ∂P) ^ 2 := by
      rw [hYm]
      nlinarith
    have h := one_sided_floor Y hY0 hYi hY2 hK (by linarith : (0 : ℝ) ≤ ρ / 2) hv2 hvm
    rwa [show 2 * (ρ / 2) = ρ by ring] at h
  rcases le_total θ (ρ / 2) with hθ | hθ
  · obtain ⟨hgi, hfl⟩ := hside (fun ω => max (X ω) 0) hP (fun ω => le_max_right _ _)
      (fun ω => hpart_sq (X ω)) (by linarith)
    refine ⟨fun ω => min (max (X ω) 0) (ρ / 2) ^ 2, hgi, fun ω => sq_nonneg _, fun ω => ?_, hfl⟩
    exact clip_lower_pos ρ θ (F ω) hθ0 hθ
  · obtain ⟨hgi, hfl⟩ := hside (fun ω => max (-X ω) 0) hN (fun ω => le_max_right _ _)
      (fun ω => by have := hpart_sq (-X ω); rwa [neg_sq] at this) (by linarith)
    refine ⟨fun ω => min (max (-X ω) 0) (ρ / 2) ^ 2, hgi, fun ω => sq_nonneg _, fun ω => ?_, hfl⟩
    have h := clip_lower_neg ρ θ (F ω) hθ hθρ
    rwa [show θ - F ω = -X ω by simp [hXdef]] at h

/-- Proposition (a bounded-kurtosis transfer), squared form. -/
theorem clipped_squared_floor (F : Ω → ℝ) (θ ρ K : ℝ) (hF : MemLp F 4 P)
    (hmean : (∫ ω, F ω ∂P) = θ) (hθ0 : 0 ≤ θ) (hθρ : θ ≤ ρ) (hK : 1 ≤ K)
    (h4 : (∫ ω, (F ω - θ) ^ 4 ∂P) ≤ K * ProbabilityTheory.variance F P ^ 2) :
    ENNReal.ofReal (min (ProbabilityTheory.variance F P) (ρ ^ 2) / (256 * K ^ 2)) ≤
      squaredRisk P (fun ω => clipEstimate ρ (F ω)) θ := by
  obtain ⟨g, hgi, hg0, hgle, hfl⟩ := kurtosis_floor_real F θ ρ K hF hmean hθ0 hθρ hK h4
  have hK0 : 0 < K := by linarith
  calc
    ENNReal.ofReal (min (ProbabilityTheory.variance F P) (ρ ^ 2) / (256 * K ^ 2)) ≤
        ENNReal.ofReal (∫ ω, g ω ∂P) := by
      apply ENNReal.ofReal_le_ofReal
      rw [div_le_iff₀ (by positivity)]
      linarith
    _ = ∫⁻ ω, ENNReal.ofReal (g ω) ∂P :=
      ofReal_integral_eq_lintegral_ofReal hgi (ae_of_all _ hg0)
    _ ≤ squaredRisk P (fun ω => clipEstimate ρ (F ω)) θ :=
      lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hgle ω)

/-- The square root of the squared floor is the RMS floor `min(ρ,σ)/(16K)`. -/
theorem sqrt_floor_eq {v ρ K : ℝ} (hρ : 0 ≤ ρ) (hK : 0 < K) :
    Real.sqrt (min v (ρ ^ 2) / (256 * K ^ 2)) = min ρ (Real.sqrt v) / (16 * K) := by
  have hmono : Monotone Real.sqrt := fun _ _ h => Real.sqrt_le_sqrt h
  rw [Real.sqrt_div' _ (by positivity), hmono.map_min, Real.sqrt_sq hρ,
    show (256 : ℝ) * K ^ 2 = (16 * K) ^ 2 by ring, Real.sqrt_sq (by positivity), min_comm]

/-- Proposition (a bounded-kurtosis transfer), RMS form `min(ρ,σ)/(16K)`. -/
theorem clipped_rms_floor (F : Ω → ℝ) (θ ρ K : ℝ) (hF : MemLp F 4 P)
    (hmean : (∫ ω, F ω ∂P) = θ) (hθ0 : 0 ≤ θ) (hθρ : θ ≤ ρ) (hK : 1 ≤ K)
    (h4 : (∫ ω, (F ω - θ) ^ 4 ∂P) ≤ K * ProbabilityTheory.variance F P ^ 2) :
    ENNReal.ofReal (min ρ (Real.sqrt (ProbabilityTheory.variance F P)) / (16 * K)) ≤
      rootMeanRisk P (fun ω => clipEstimate ρ (F ω)) θ := by
  have h := clipped_squared_floor F θ ρ K hF hmean hθ0 hθρ hK h4
  have hρ : 0 ≤ ρ := hθ0.trans hθρ
  have hK0 : 0 < K := by linarith
  have hv := ProbabilityTheory.variance_nonneg F P
  unfold rootMeanRisk
  calc
    ENNReal.ofReal (min ρ (Real.sqrt (ProbabilityTheory.variance F P)) / (16 * K)) =
        ENNReal.ofReal (min (ProbabilityTheory.variance F P) (ρ ^ 2) / (256 * K ^ 2)) ^
          (1 / 2 : ℝ) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.sqrt_eq_rpow,
        sqrt_floor_eq hρ hK0]
    _ ≤ _ := ENNReal.rpow_le_rpow h (by norm_num)

end Real

end ThresholdHC.ClippingBoundary
