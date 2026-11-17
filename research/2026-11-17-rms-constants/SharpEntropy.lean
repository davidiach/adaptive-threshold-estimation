import ThresholdHC.Tier6.AlgorithmModel
import Mathlib.InformationTheory.KullbackLeibler.Basic

/-! The three-bias testing inequality used in the sharp RMS lower bound. -/

noncomputable section
open MeasureTheory InformationTheory Real
open scoped ENNReal

namespace ThresholdHC.SharpRMS

private def test (t x : ℝ) := 1 + 8 * ((x - t)^2 - 1/9)

private theorem test_pos (t x : ℝ) : 0 < test t x := by
  unfold test
  nlinarith [sq_nonneg (x-t)]

-- Homogenize G(y) times the degree-five Taylor lower bound for exp(5y),
-- minus 15. A positive-coefficient expansion on each cone proves its sign.
private def poly (u v : ℝ) :=
  ((907/225*v + 8*u)^2 - 256*(49/100)*u*v) *
    (v^5 + 5*u*v^4 + (5*u)^2*v^3/2 + (5*u)^3*v^2/6 +
      (5*u)^4*v/24 + (5*u)^5/120) - 15*v^7

private theorem poly_nonneg (y : ℝ) (hy : 0 ≤ y) : 0 ≤ poly y 1 := by
  by_cases h₁ : y ≤ 3/8
  · have cone (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
        0 ≤ poly (3/8*u) (u+v) := by unfold poly; ring_nf; positivity
    convert cone (8*y/3) (1-8*y/3) (by positivity) (by linarith) using 2 <;> ring
  by_cases h₂ : y ≤ 1/2
  · have cone (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
        0 ≤ poly (1/2*u+3/8*v) (u+v) := by unfold poly; ring_nf; positivity
    convert cone (8*y-3) (4-8*y) (by linarith) (by linarith) using 2 <;> ring
  have cone (u : ℝ) (hu : 0 ≤ u) : 0 ≤ poly (u+1/2) 1 := by
    unfold poly; ring_nf; positivity
  convert cone (y-1/2) (by linarith) using 2
  ring

/-- Pointwise logarithmic minorant. It holds for every real output. -/
theorem entropy_minorant (x : ℝ) :
    (8/3 : ℝ) ≤ log (1+8*((x-7/10)^2-1/9)) +
      log (1+8*((x+7/10)^2-1/9)) + 5*x^2 := by
  let y := x^2
  let G := test (7/10) x * test (-7/10) x
  have hy : 0 ≤ y := sq_nonneg _
  have hG : 0 < G := mul_pos (test_pos _ _) (test_pos _ _)
  have he := Real.sum_le_exp_of_nonneg (x := 5*y) (by positivity) 6
  norm_num [Finset.sum_range_succ, Nat.factorial] at he
  have hpoly := poly_nonneg y hy
  unfold poly at hpoly
  have hprod : 15 ≤ G * exp (5*y) := by
    apply le_trans _ (mul_le_mul_of_nonneg_left he hG.le)
    dsimp [G, test, y] at *
    linarith only [hpoly]
  have he8 : exp (8/3 : ℝ) ≤ 15 := by
    have hh := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 8
    have hcube : exp (8/3 : ℝ)^3 ≤ 15^3 := by
      rw [← Real.exp_nat_mul, show ((3:ℕ):ℝ)*(8/3) = ((8:ℕ):ℝ)*(1:ℝ) by norm_num,
        Real.exp_nat_mul]
      exact hh.trans (by norm_num)
    exact le_of_pow_le_pow_left₀ (by norm_num) (by norm_num) hcube
  have hlog := (Real.le_log_iff_exp_le (mul_pos hG (exp_pos _))).2 (he8.trans hprod)
  rw [Real.log_mul hG.ne' (exp_pos _).ne', Real.log_exp,
    show log G = log (test (7/10) x) + log (test (-7/10) x) from
      Real.log_mul (test_pos _ _).ne' (test_pos _ _).ne'] at hlog
  rw [show (-7/10 : ℝ) = -(7/10) by ring] at hlog
  simpa only [Pi.add_apply, test, sub_neg_eq_add] using hlog

/-- Variational testing bound with a positive test of Q-expectation at most one.
The KL is Mathlib's divergence on measures, including its infinite case. -/
theorem entropy_test_bound {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (g : Ω → ℝ) (hg : ∀ x, 0 < g x) (hQ : Integrable g Q)
    (hP : Integrable (fun x => log (g x)) P) (hmean : ∫ x, g x ∂Q ≤ 1) :
    ENNReal.ofReal (∫ x, log (g x) ∂P) ≤ klDiv P Q := by
  by_cases hfin : klDiv P Q = ∞
  · simp [hfin]
  obtain ⟨hac, hint⟩ := klDiv_ne_top_iff.mp hfin
  let r := fun x => (P.rnDeriv Q x).toReal
  have hr : Integrable r Q := by
    simpa [r] using (integrable_toReal_rnDeriv_mul_iff
      (f := fun _ => (1:ℝ)) hac).2 (integrable_const _)
  have hmass : ∫ x, r x ∂Q = 1 := by
    simpa [r] using (integral_toReal_rnDeriv_mul (f := fun _ => (1:ℝ)) hac)
  have hgibbs (x : Ω) : r x * log (g x) ≤ r x * llr P Q x + g x - r x := by
    by_cases hz : r x = 0
    · simp [hz, (hg x).le]
    have hp : 0 < r x := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hz)
    have h := Real.log_le_sub_one_of_pos (div_pos (hg x) hp)
    rw [Real.log_div (hg x).ne' hz] at h
    change r x * log (g x) ≤ r x * log (r x) + g x - r x
    have hm := mul_le_mul_of_nonneg_right h hp.le
    field_simp [hz] at hm
    linarith
  have h₁ := (integrable_toReal_rnDeriv_mul_iff hac).2 hP
  have h₂ := (integrable_toReal_rnDeriv_mul_iff hac).2 hint
  have h := integral_mono h₁ ((h₂.add hQ).sub hr) hgibbs
  change (∫ x, r x * log (g x) ∂Q) ≤ ∫ x, (r x * llr P Q x + g x - r x) ∂Q at h
  have hsplit := integral_sub (h₂.add hQ) hr
  simp only [Pi.add_apply] at hsplit
  dsimp only [r] at h hmass
  rw [hsplit, integral_add h₂ hQ, hmass,
    integral_toReal_rnDeriv_mul hac, integral_toReal_rnDeriv_mul hac] at h
  rw [klDiv_of_ac_of_integrable hac hint]
  apply ENNReal.ofReal_le_ofReal
  simpa using (show (∫ x, log (g x) ∂P) ≤ ∫ x, llr P Q x ∂P by linarith)

private theorem integrable_on_output {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {X : Ω → ℝ} (hm : Measurable X)
    (hb : ∀ w, X w ∈ Set.Icc (-1:ℝ) 1) {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable (fun w => f (X w)) P := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Set.Icc (-1:ℝ) 1) hf.continuousOn
  exact (integrable_const C).mono' (hf.measurable.comp hm).aestronglyMeasurable
    (ae_of_all _ fun w => hC _ (hb w))

open Tier6 in
/-- If the fair law is sufficiently close in *summed reverse KL* to the two
alternative laws, every measurable estimator incurs MSE at least 1/9 at
one of the three sign means. Risk and KL may be infinite. -/
theorem three_bias_risk {Ω : Type} [MeasurableSpace Ω]
    (P Qp Qm : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Qp]
    [IsProbabilityMeasure Qm] (X : Ω → ℝ) (hm : Measurable X)
    (hk : klDiv P Qp + klDiv P Qm ≤ ENNReal.ofReal (2*3283/3150 : ℝ)) :
    ENNReal.ofReal (1/9:ℝ) ≤ max (squaredRisk P X 0)
      (max (squaredRisk Qp X (7/10)) (squaredRisk Qm X (-(7/10)))) := by
  by_contra! h
  obtain ⟨hzero, hp, hn⟩ := (max_lt_iff.mp h).imp_right max_lt_iff.mp
  let Y := fun w => max (-1:ℝ) (min 1 (X w))
  have hYm : Measurable Y := by dsimp [Y]; fun_prop
  have hYb (w) : Y w ∈ Set.Icc (-1:ℝ) 1 :=
    ⟨le_max_left .., max_le (by norm_num) (min_le_left ..)⟩
  have mse (M : Measure Ω) [IsProbabilityMeasure M] (t : ℝ) (ht : t ∈ Set.Icc (-1:ℝ) 1)
      (hM : squaredRisk M X t < ENNReal.ofReal (1/9:ℝ)) :
      (∫ w, (Y w-t)^2 ∂M) ≤ 1/9 := by
    have hi := integrable_on_output M hYm hYb (f := fun z => (z-t)^2) (by fun_prop)
    have hb : ENNReal.ofReal (∫ w, (Y w-t)^2 ∂M) ≤ squaredRisk M X t := by
      rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ => sq_nonneg _)]
      apply lintegral_mono
      intro w
      apply ENNReal.ofReal_le_ofReal
      obtain ⟨hl, hu⟩ := ht
      dsimp [Y]
      rcases le_total (X w) (-1) with hw | hw
      · rw [min_eq_right (by linarith), max_eq_left hw]
        nlinarith [mul_nonneg (show 0 ≤ -1-X w by linarith) (show 0 ≤ 2*t+1-X w by linarith)]
      · rcases le_total (X w) 1 with hw' | hw'
        · rw [min_eq_right hw', max_eq_right hw]
        · rw [min_eq_left hw', max_eq_right (by norm_num)]
          nlinarith [mul_nonneg (show 0 ≤ X w-1 by linarith) (show 0 ≤ X w+1-2*t by linarith)]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (integral_nonneg fun _ => sq_nonneg _)).mp (hb.trans_lt hM) |>.le
  have testKL (Q : Measure Ω) [IsProbabilityMeasure Q] (t : ℝ)
      (ht : t ∈ Set.Icc (-1:ℝ) 1) (hq : squaredRisk Q X t < ENNReal.ofReal (1/9:ℝ)) :
      ENNReal.ofReal (∫ w, log (test t (Y w)) ∂P) ≤ klDiv P Q := by
    have hs := integrable_on_output Q hYm hYb (f := fun z => (z-t)^2) (by fun_prop)
    have htest : Continuous (test t) := by unfold test; fun_prop
    apply entropy_test_bound P Q _ (fun _ => test_pos ..)
      (integrable_on_output Q hYm hYb htest)
      (integrable_on_output P hYm hYb (htest.log (fun z => (test_pos t z).ne')))
    unfold test
    have ha := integral_add (integrable_const (1:ℝ) (μ := Q))
      ((hs.sub (integrable_const (1/9:ℝ))).const_mul 8)
    simp only [Pi.sub_apply] at ha
    rw [ha, integral_const_mul, integral_sub hs (integrable_const (1/9:ℝ))]
    simp only [integral_const, probReal_univ, one_smul]
    linarith [mse Q t ht hq]
  have hsum := (add_le_add (testKL Qp (7/10) (by constructor <;> norm_num) hp)
    (testKL Qm (-(7/10)) (by constructor <;> norm_num) hn)).trans hk
  have upper := ENNReal.ofReal_add_le.trans hsum
  have upper' := (ENNReal.ofReal_le_ofReal_iff (by norm_num : 0 ≤ (2*3283/3150:ℝ))).mp upper
  have logInt (t : ℝ) : Integrable (fun w => log (test t (Y w))) P := by
    apply integrable_on_output P hYm hYb (f := fun z => log (test t z))
    apply Continuous.log _ (fun z => (test_pos t z).ne')
    unfold test
    fun_prop
  have hi := integrable_on_output P hYm hYb (f := fun z => z^2) (by fun_prop)
  have lower := integral_mono (μ := P) (integrable_const (8/3:ℝ))
    (((logInt (7/10)).add (logInt (-(7/10)))).add (hi.const_mul 5))
    (fun w => by
      change (8/3:ℝ) ≤ log (test (7/10) (Y w)) + log (test (-(7/10)) (Y w)) + 5*(Y w)^2
      simpa only [test, sub_neg_eq_add] using entropy_minorant (Y w))
  simp only [Pi.add_apply] at lower
  have hadd := integral_add ((logInt (7/10)).add (logInt (-(7/10)))) (hi.const_mul 5)
  simp only [Pi.add_apply] at hadd
  rw [hadd,
    integral_add (logInt _) (logInt _), integral_const_mul] at lower
  simp only [integral_const, probReal_univ, one_smul] at lower
  have hz := mse P 0 (by constructor <;> norm_num) hzero
  simp only [sub_zero] at hz
  linarith

end ThresholdHC.SharpRMS
