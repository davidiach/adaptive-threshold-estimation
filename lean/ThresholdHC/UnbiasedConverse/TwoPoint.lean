import ThresholdHC.Proofs.Hellinger
import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
The symmetric information/variance inequality on arbitrary probability spaces.
The proof uses the densities with respect to P + Q and Cauchy--Schwarz. The
triangular-discrimination form gives the same sharp local coefficient as the
paper's Hellinger argument, without requiring positive densities everywhere.
-/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
namespace ThresholdHC.UnbiasedConverse

theorem integral_mul_sq_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, f x * g x ∂μ)^2 ≤ (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ) := by
  have inner_eq {u v : Ω → ℝ} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
      inner ℝ (hu.toLp u) (hv.toLp v) = ∫ x, u x * v x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp] with x hx hy
    change (hv.toLp v x) * (hu.toLp u x) = u x * v x
    rw [hx, hy, mul_comm]
  have h := real_inner_mul_inner_self_le (hf.toLp f) (hg.toLp g)
  simpa only [inner_eq, ← pow_two] using h

theorem triangle_le_symmetric_log {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hs : p + q = 1) : 2 * (p - q)^2 ≤ (p - q) * Real.log (p/q) := by
  have h := ThresholdHC.Proofs.sym_kl_hellinger_pointwise p q hp hq
  have hp2 := Real.sq_sqrt hp.le
  have hq2 := Real.sq_sqrt hq.le
  have hsum : (Real.sqrt p + Real.sqrt q)^2 ≤ 2 := by
    nlinarith [sq_nonneg (Real.sqrt p - Real.sqrt q)]
  have heq : (p-q)^2 = (Real.sqrt p - Real.sqrt q)^2 *
      (Real.sqrt p + Real.sqrt q)^2 := by
    calc
      _ = ((Real.sqrt p)^2 - (Real.sqrt q)^2)^2 := by rw [hp2,hq2]
      _ = _ := by ring
  have hb := mul_le_mul_of_nonneg_left hsum (sq_nonneg (Real.sqrt p - Real.sqrt q))
  rw [← heq] at hb
  linarith

def comparisonDensity {Ω : Type*} [MeasurableSpace Ω] (P Q : Measure Ω) (x : Ω) : ℝ :=
  (P.rnDeriv (P+Q) x).toReal

theorem comparisonDensity_sum {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    ∀ᵐ x ∂(P+Q), comparisonDensity P Q x + comparisonDensity Q P x = 1 := by
  filter_upwards [Measure.rnDeriv_add P Q (P+Q), Measure.rnDeriv_self (P+Q),
    Measure.rnDeriv_lt_top P (P+Q), Measure.rnDeriv_lt_top Q (P+Q)] with x ha hs hp hq
  dsimp [comparisonDensity]
  rw [add_comm Q P]
  simp only [Pi.add_apply] at ha
  rw [← ENNReal.toReal_add hp.ne hq.ne, ← ha, hs]
  simp

theorem comparisonDensity_memLp {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    MemLp (comparisonDensity P Q) 2 (P+Q) := by
  apply MemLp.of_bound (Measure.measurable_rnDeriv P (P+Q)).ennreal_toReal.aestronglyMeasurable 1
  filter_upwards [comparisonDensity_sum P Q] with x hx
  have hp : 0 ≤ comparisonDensity P Q x := ENNReal.toReal_nonneg
  have hq : 0 ≤ comparisonDensity Q P x := ENNReal.toReal_nonneg
  change ‖comparisonDensity P Q x‖ ≤ 1
  rw [Real.norm_of_nonneg hp]
  linarith

theorem triangle_integral_le_kl {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPQ : klDiv P Q ≠ ∞) (hQP : klDiv Q P ≠ ∞) :
    2 * (∫ x, (comparisonDensity P Q x - comparisonDensity Q P x)^2 ∂(P+Q)) ≤
      (klDiv P Q).toReal + (klDiv Q P).toReal := by
  have hpq := (klDiv_ne_top_iff.mp hPQ).1
  have hqp := (klDiv_ne_top_iff.mp hQP).1
  have hpint := (klDiv_ne_top_iff.mp hPQ).2
  have hqint := (klDiv_ne_top_iff.mp hQP).2
  have hp : P ≪ P+Q := Measure.AbsolutelyContinuous.rfl.add_right Q
  have hq : Q ≪ P+Q := Measure.AbsolutelyContinuous.rfl.add_right' P
  have hmp : P+Q ≪ P := Measure.AbsolutelyContinuous.rfl.add_left hqp
  have hmq : P+Q ≪ Q := hpq.add_left Measure.AbsolutelyContinuous.rfl
  have hpl := (integrable_toReal_rnDeriv_mul_iff hp).mpr hpint
  have hql := (integrable_toReal_rnDeriv_mul_iff hq).mpr hqint
  have hqmem : MemLp (comparisonDensity Q P) 2 (P+Q) := by
    simpa only [add_comm Q P] using comparisonDensity_memLp Q P
  have hsq := ((comparisonDensity_memLp P Q).sub hqmem).integrable_sq
  have hpoint : ∀ᵐ x ∂(P+Q),
      2 * (comparisonDensity P Q x - comparisonDensity Q P x)^2 ≤
      (P.rnDeriv (P+Q) x).toReal * llr P Q x +
        (Q.rnDeriv (P+Q) x).toReal * llr Q P x := by
    filter_upwards [comparisonDensity_sum P Q, Measure.rnDeriv_pos' hmp,
      Measure.rnDeriv_pos' hmq, Measure.rnDeriv_lt_top P (P+Q),
      Measure.rnDeriv_lt_top Q (P+Q),
      hmq (Measure.rnDeriv_eq_div hp hq), hmp (Measure.rnDeriv_eq_div hq hp)]
      with x hsum hpp hqq hpt hqt hratioP hratioQ
    have hp0 : 0 < (P.rnDeriv (P+Q) x).toReal := ENNReal.toReal_pos hpp.ne' hpt.ne
    have hq0 : 0 < (Q.rnDeriv (P+Q) x).toReal := ENNReal.toReal_pos hqq.ne' hqt.ne
    have h := triangle_le_symmetric_log hp0 hq0 (by
      simpa only [comparisonDensity, add_comm Q P] using hsum)
    dsimp [comparisonDensity]
    rw [add_comm Q P]
    simp only [llr, hratioP, hratioQ, ENNReal.toReal_div]
    rw [Real.log_div hp0.ne' hq0.ne', Real.log_div hq0.ne' hp0.ne']
    rw [Real.log_div hp0.ne' hq0.ne'] at h
    nlinarith
  calc
    _ = ∫ x, 2 * (comparisonDensity P Q x - comparisonDensity Q P x)^2 ∂(P+Q) :=
      (integral_const_mul _ _).symm
    _ ≤ ∫ x, (P.rnDeriv (P+Q) x).toReal * llr P Q x +
        (Q.rnDeriv (P+Q) x).toReal * llr Q P x ∂(P+Q) :=
      integral_mono_ae (hsq.const_mul 2) (hpl.add hql) hpoint
    _ = _ := by
      rw [integral_add hpl hql, integral_toReal_rnDeriv_mul hp,
        integral_toReal_rnDeriv_mul hq,
        toReal_klDiv_of_measure_eq hpq (by simp),
        toReal_klDiv_of_measure_eq hqp (by simp)]

theorem centered_second_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {f : Ω → ℝ}
    (hf : MemLp f 2 P) (c : ℝ) :
    (∫ x, (f x-c)^2 ∂P) = variance f P + ((∫ x, f x ∂P)-c)^2 := by
  have hi := hf.integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)
  rw [variance_eq_integral hf.aestronglyMeasurable.aemeasurable]
  have heq : (fun x => (f x-c)^2) = fun x =>
      (f x-(∫ y, f y ∂P))^2 + 2*((∫ y, f y ∂P)-c)*f x +
        (c^2-(∫ y, f y ∂P)^2) := by funext x; ring
  have hs : Integrable (fun x => (f x-(∫ y, f y ∂P))^2) P :=
    (hf.sub (memLp_const _)).integrable_sq
  have hl : Integrable (fun x => 2*((∫ y, f y ∂P)-c)*f x) P := hi.const_mul _
  have hsum : Integrable (fun x => (f x-(∫ y, f y ∂P))^2 +
      2*((∫ y, f y ∂P)-c)*f x) P := hs.add hl
  have hc : Integrable (fun _ : Ω => c^2-(∫ y, f y ∂P)^2) P := integrable_const _
  rw [heq, integral_add hsum hc,
    integral_add hs hl,
    integral_const_mul, integral_const]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  ring

/-- Symmetric KL controls the separation of expectations of an arbitrary
square-integrable statistic. All quantities refer to the actual measures. -/
theorem two_point_variance_kl {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {f : Ω → ℝ} (hfP : MemLp f 2 P) (hfQ : MemLp f 2 Q)
    (hPQ : klDiv P Q ≠ ∞) (hQP : klDiv Q P ≠ ∞) :
    ((∫ x, f x ∂P) - (∫ x, f x ∂Q))^2 *
        (1-((klDiv P Q).toReal+(klDiv Q P).toReal)/4) ≤
      ((klDiv P Q).toReal+(klDiv Q P).toReal)/2 * (variance f P + variance f Q) := by
  let c := ((∫ x, f x ∂P) + (∫ x, f x ∂Q))/2
  let g := fun x => f x-c
  let s := fun x => comparisonDensity P Q x - comparisonDensity Q P x
  have hgP : MemLp g 2 P := hfP.sub (memLp_const c)
  have hgQ : MemLp g 2 Q := hfQ.sub (memLp_const c)
  have hg : MemLp g 2 (P+Q) := memLp_add_measure.mpr ⟨hgP,hgQ⟩
  have hqmem : MemLp (comparisonDensity Q P) 2 (P+Q) := by
    simpa only [add_comm Q P] using comparisonDensity_memLp Q P
  have hs : MemLp s 2 (P+Q) := (comparisonDensity_memLp P Q).sub hqmem
  have hp : P ≪ P+Q := Measure.AbsolutelyContinuous.rfl.add_right Q
  have hq : Q ≪ P+Q := Measure.AbsolutelyContinuous.rfl.add_right' P
  have hiP := hfP.integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)
  have hiQ := hfQ.integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)
  have hgp : Integrable g P := hgP.integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)
  have hgq : Integrable g Q := hgQ.integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)
  have hmean : (∫ x, g x*s x ∂(P+Q)) = (∫ x, f x ∂P) - (∫ x, f x ∂Q) := by
    have he : (fun x => g x*s x) = fun x =>
        (P.rnDeriv (P+Q) x).toReal*g x - (Q.rnDeriv (P+Q) x).toReal*g x := by
      funext x
      simp only [s, comparisonDensity, add_comm Q P]
      ring
    rw [he, integral_sub ((integrable_toReal_rnDeriv_mul_iff hp).mpr hgp)
      ((integrable_toReal_rnDeriv_mul_iff hq).mpr hgq),
      integral_toReal_rnDeriv_mul hp, integral_toReal_rnDeriv_mul hq]
    simp only [g, integral_sub hiP (integrable_const c),
      integral_sub hiQ (integrable_const c), integral_const, probReal_univ, smul_eq_mul, one_mul]
    ring
  have hsecond : (∫ x, g x^2 ∂(P+Q)) = variance f P + variance f Q +
      ((∫ x, f x ∂P) - (∫ x, f x ∂Q))^2/2 := by
    rw [integral_add_measure hgP.integrable_sq hgQ.integrable_sq]
    dsimp only [g]
    rw [centered_second_moment P hfP c, centered_second_moment Q hfQ c]
    dsimp only [c]
    ring
  have hcs := integral_mul_sq_le (P+Q) hg hs
  rw [hmean] at hcs
  have hk := triangle_integral_le_kl P Q hPQ hQP
  have hnonneg : 0 ≤ ∫ x, g x^2 ∂(P+Q) := integral_nonneg (fun x => sq_nonneg _)
  have hb := mul_le_mul_of_nonneg_left hk hnonneg
  change _ ≤ (∫ x, g x^2 ∂(P+Q))*_ at hcs
  dsimp only [s] at hcs
  rw [hsecond] at hcs hb
  nlinarith

theorem two_point_uniform_variance {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {f : Ω → ℝ} (hfP : MemLp f 2 P) (hfQ : MemLp f 2 Q)
    {V k : ℝ} (hV : 0 ≤ V) (hk : 0 ≤ k)
    (hvP : variance f P ≤ V) (hvQ : variance f Q ≤ V)
    (hklP : klDiv P Q ≤ ENNReal.ofReal k) (hklQ : klDiv Q P ≤ ENNReal.ofReal k) :
    ((∫ x, f x ∂P)-(∫ x, f x ∂Q))^2 ≤
      k*(2*V+((∫ x, f x ∂P)-(∫ x, f x ∂Q))^2/2) := by
  have hp : klDiv P Q ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hklP
  have hq : klDiv Q P ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hklQ
  have h := two_point_variance_kl P Q hfP hfQ hp hq
  have hpk : (klDiv P Q).toReal ≤ k := by
    simpa only [ENNReal.toReal_ofReal hk] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hklP
  have hqk : (klDiv Q P).toReal ≤ k := by
    simpa only [ENNReal.toReal_ofReal hk] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hklQ
  have hscale := mul_le_mul_of_nonneg_left (show variance f P + variance f Q ≤ 2*V by linarith)
    (show 0 ≤ ((klDiv P Q).toReal+(klDiv Q P).toReal)/2 by positivity)
  have hscale2 := mul_le_mul_of_nonneg_right (show (klDiv P Q).toReal+(klDiv Q P).toReal ≤ 2*k by linarith)
    (show 0 ≤ V+((∫ x, f x ∂P)-(∫ x, f x ∂Q))^2/4 by positivity)
  nlinarith

end ThresholdHC.UnbiasedConverse
