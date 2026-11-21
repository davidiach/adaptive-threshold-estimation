import ThresholdHC.UnbiasedConverse.TwoPoint

/-! A one-sided information/mean inequality on arbitrary probability spaces.

Only the forward divergence `KL(P‖Q)` is assumed finite. With the comparison
densities `a = dP/d(P+Q)` and `b = dQ/d(P+Q)`, the pointwise bound
`(a-b)² ≤ 2(a·log(a/b) + b - a)` (valid also where `a = 0`) gives the
triangular-discrimination bound `∫(a-b)² d(P+Q) ≤ 2·KL(P‖Q)`, and
Cauchy--Schwarz against `f` gives the mean separation bound. -/
noncomputable section
namespace ThresholdHC.PsiNull
open MeasureTheory InformationTheory
open scoped ENNReal
open ThresholdHC.UnbiasedConverse

/-- Pointwise one-sided triangular-discrimination bound for two comparison
densities summing to one. The left density may vanish; `L` is only constrained
where it is positive. -/
theorem sq_sub_le_one_sided_log {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hs : a + b = 1)
    (L : ℝ) (hL : 0 < a → L = Real.log (a / b)) :
    (a - b)^2 ≤ 2 * (a * L + b - a) := by
  rcases ha.lt_or_eq with ha0 | ha0
  · rw [hL ha0]
    obtain ⟨s, hs0, rfl⟩ : ∃ s : ℝ, 0 < s ∧ s^2 = a :=
      ⟨Real.sqrt a, Real.sqrt_pos.mpr ha0, Real.sq_sqrt ha⟩
    obtain ⟨t, ht0, rfl⟩ : ∃ t : ℝ, 0 < t ∧ t^2 = b :=
      ⟨Real.sqrt b, Real.sqrt_pos.mpr hb, Real.sq_sqrt hb.le⟩
    have hlog : Real.log (s^2 / t^2) = 2 * Real.log (s / t) := by
      rw [← div_pow, Real.log_pow]
      push_cast
      ring
    have h1 : 1 - t / s ≤ Real.log (s / t) := by
      have h := Real.log_le_sub_one_of_pos (div_pos ht0 hs0)
      rw [show Real.log (t / s) = -Real.log (s / t) by rw [← Real.log_inv, inv_div]] at h
      linarith
    have h2 : s^2 * (1 - t / s) = s^2 - s * t := by
      field_simp
    have hA : 2 * (s^2 - s * t) ≤ s^2 * Real.log (s^2 / t^2) := by
      rw [hlog, ← h2]
      nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg s)]
    have hst : (s + t)^2 ≤ 2 := by
      nlinarith [sq_nonneg (s - t)]
    have hB : (s^2 - t^2)^2 ≤ 2 * (s^2 - 2 * (s * t) + t^2) := by
      have he : (s^2 - t^2)^2 = (s - t)^2 * (s + t)^2 := by ring
      rw [he]
      nlinarith [mul_le_mul_of_nonneg_left hst (sq_nonneg (s - t))]
    linarith
  · rw [← ha0] at hs ⊢
    have hb1 : b = 1 := by linarith
    rw [hb1]
    norm_num

/-- One-sided information/mean inequality: only `KL(P‖Q) < ∞` is assumed.
The separation of means of a square-integrable statistic is controlled by
the forward divergence times the sum of the two raw second moments. -/
theorem kl_mean_one_sided {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {f : Ω → ℝ} (hfP : MemLp f 2 P) (hfQ : MemLp f 2 Q) (hPQ : klDiv P Q ≠ ∞) :
    ((∫ x, f x ∂P) - (∫ x, f x ∂Q))^2 ≤
      2 * (klDiv P Q).toReal * ((∫ x, f x ^ 2 ∂P) + (∫ x, f x ^ 2 ∂Q)) := by
  have hpq := (klDiv_ne_top_iff.mp hPQ).1
  have hpint := (klDiv_ne_top_iff.mp hPQ).2
  have hp : P ≪ P+Q := Measure.AbsolutelyContinuous.rfl.add_right Q
  have hq : Q ≪ P+Q := Measure.AbsolutelyContinuous.rfl.add_right' P
  have hmq : P+Q ≪ Q := hpq.add_left Measure.AbsolutelyContinuous.rfl
  have hamem : MemLp (fun x => (P.rnDeriv (P+Q) x).toReal) 2 (P+Q) :=
    comparisonDensity_memLp P Q
  have hbmem : MemLp (fun x => (Q.rnDeriv (P+Q) x).toReal) 2 (P+Q) := by
    have h := comparisonDensity_memLp Q P
    change MemLp (fun x => (Q.rnDeriv (Q+P) x).toReal) 2 (Q+P) at h
    rwa [add_comm Q P] at h
  have hsmem : MemLp (fun x => (P.rnDeriv (P+Q) x).toReal - (Q.rnDeriv (P+Q) x).toReal)
      2 (P+Q) := hamem.sub hbmem
  have hf : MemLp f 2 (P+Q) := memLp_add_measure.mpr ⟨hfP, hfQ⟩
  have hiP := hfP.integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)
  have hiQ := hfQ.integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)
  have hmean : (∫ x, f x * ((P.rnDeriv (P+Q) x).toReal - (Q.rnDeriv (P+Q) x).toReal) ∂(P+Q)) =
      (∫ x, f x ∂P) - (∫ x, f x ∂Q) := by
    have he : (fun x => f x * ((P.rnDeriv (P+Q) x).toReal - (Q.rnDeriv (P+Q) x).toReal)) =
        fun x => (P.rnDeriv (P+Q) x).toReal * f x - (Q.rnDeriv (P+Q) x).toReal * f x := by
      funext x
      ring
    rw [he, integral_sub ((integrable_toReal_rnDeriv_mul_iff hp).mpr hiP)
      ((integrable_toReal_rnDeriv_mul_iff hq).mpr hiQ),
      integral_toReal_rnDeriv_mul hp, integral_toReal_rnDeriv_mul hq]
  have hsecond : (∫ x, f x ^ 2 ∂(P+Q)) = (∫ x, f x ^ 2 ∂P) + (∫ x, f x ^ 2 ∂Q) :=
    integral_add_measure hfP.integrable_sq hfQ.integrable_sq
  have hcs := integral_mul_sq_le (P+Q) hf hsmem
  rw [hmean, hsecond] at hcs
  have hsum : ∀ᵐ x ∂(P+Q), (P.rnDeriv (P+Q) x).toReal + (Q.rnDeriv (P+Q) x).toReal = 1 := by
    simpa only [comparisonDensity, add_comm Q P] using comparisonDensity_sum P Q
  have hpoint : ∀ᵐ x ∂(P+Q),
      ((P.rnDeriv (P+Q) x).toReal - (Q.rnDeriv (P+Q) x).toReal)^2 ≤
        2 * ((P.rnDeriv (P+Q) x).toReal * llr P Q x + (Q.rnDeriv (P+Q) x).toReal -
          (P.rnDeriv (P+Q) x).toReal) := by
    filter_upwards [hsum, Measure.rnDeriv_pos' hmq, Measure.rnDeriv_lt_top Q (P+Q),
      hmq (Measure.rnDeriv_eq_div hp hq)] with x hx hqq hqt hratio
    have hb0 : 0 < (Q.rnDeriv (P+Q) x).toReal := ENNReal.toReal_pos hqq.ne' hqt.ne
    apply sq_sub_le_one_sided_log ENNReal.toReal_nonneg hb0 hx
    intro _
    rw [llr, hratio, ENNReal.toReal_div]
  have hsqint := hsmem.integrable_sq
  have hpl : Integrable (fun x => (P.rnDeriv (P+Q) x).toReal * llr P Q x) (P+Q) :=
    (integrable_toReal_rnDeriv_mul_iff hp).mpr hpint
  have haint := hamem.integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)
  have hbint := hbmem.integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)
  have hplb : Integrable (fun x => (P.rnDeriv (P+Q) x).toReal * llr P Q x +
      (Q.rnDeriv (P+Q) x).toReal) (P+Q) := hpl.add hbint
  have htri : (∫ x, ((P.rnDeriv (P+Q) x).toReal - (Q.rnDeriv (P+Q) x).toReal)^2 ∂(P+Q)) ≤
      2 * (klDiv P Q).toReal := by
    calc (∫ x, ((P.rnDeriv (P+Q) x).toReal - (Q.rnDeriv (P+Q) x).toReal)^2 ∂(P+Q))
        ≤ ∫ x, 2 * ((P.rnDeriv (P+Q) x).toReal * llr P Q x + (Q.rnDeriv (P+Q) x).toReal -
          (P.rnDeriv (P+Q) x).toReal) ∂(P+Q) :=
          integral_mono_ae hsqint ((hplb.sub haint).const_mul 2) hpoint
      _ = 2 * ((∫ x, (P.rnDeriv (P+Q) x).toReal * llr P Q x ∂(P+Q)) +
          (∫ x, (Q.rnDeriv (P+Q) x).toReal ∂(P+Q)) -
          ∫ x, (P.rnDeriv (P+Q) x).toReal ∂(P+Q)) := by
          rw [integral_const_mul, integral_sub hplb haint, integral_add hpl hbint]
      _ = 2 * (klDiv P Q).toReal := by
          rw [integral_toReal_rnDeriv_mul hp, Measure.integral_toReal_rnDeriv hp,
            Measure.integral_toReal_rnDeriv hq, toReal_klDiv_of_measure_eq hpq (by simp)]
          simp
  have hnonneg : 0 ≤ (∫ x, f x ^ 2 ∂P) + (∫ x, f x ^ 2 ∂Q) :=
    add_nonneg (integral_nonneg (fun x => sq_nonneg _)) (integral_nonneg (fun x => sq_nonneg _))
  calc ((∫ x, f x ∂P) - (∫ x, f x ∂Q))^2
      ≤ ((∫ x, f x ^ 2 ∂P) + (∫ x, f x ^ 2 ∂Q)) *
        (∫ x, ((P.rnDeriv (P+Q) x).toReal - (Q.rnDeriv (P+Q) x).toReal)^2 ∂(P+Q)) := hcs
    _ ≤ ((∫ x, f x ^ 2 ∂P) + (∫ x, f x ^ 2 ∂Q)) * (2 * (klDiv P Q).toReal) :=
      mul_le_mul_of_nonneg_left htri hnonneg
    _ = 2 * (klDiv P Q).toReal * ((∫ x, f x ^ 2 ∂P) + (∫ x, f x ^ 2 ∂Q)) := by ring

end ThresholdHC.PsiNull
