import ThresholdHC.RareAboveTwo.ConditionalWork
import ThresholdHC.RareAboveTwo.WeightedMoment

/-! Uniform population work. Hölder's inequality absorbs the positive
log-rarity overhead under the global prior-mass constraint. -/
noncomputable section
open MeasureTheory
namespace ThresholdHC.RareAboveTwo
open ThresholdHC.Tier6 ThresholdHC.Uniform713 ThresholdHC.ObservableSimulation

theorem log_weighted_inverse_bound (μ : Measure Gap) [IsProbabilityMeasure μ]
    (α a s r ρ p C : ℝ) (ha : 0 < a) (hs : 0 < s) (hsr : s < r) (hrα : r < α)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (_hp : 0 < p)
    (hm : PowerMargin μ α a) (q : SignLaw) (hq : RarePrior μ ρ q)
    (hC : ρ^(1-s/r)*(1+Real.log (1/ρ))^p ≤ C) :
    (1+Real.log (1/ρ))^p*(∫ d : Gap, q.val d*(a/(d : ℝ))^s ∂μ) ≤
      (1+1/(α/r-1))^(s/r)*C := by
  have hr : 0 < r := hs.trans hsr
  have hM : 0 < 1+1/(α/r-1) := by have h := (one_lt_div hr).2 hrα; positivity
  have hℓ : 0 ≤ (1+Real.log (1/ρ))^p := Real.rpow_nonneg (by linarith [Real.log_nonneg ((one_le_div hρ).2 hρ1)]) _
  have hw := weighted_inverse_moment μ α a s r ρ ha hs hsr hrα hm q hq
  have he : (fun d : Gap => (a/(d : ℝ))^s*q.val d) =
      fun d : Gap => q.val d*(a/(d : ℝ))^s := funext (fun d => mul_comm _ _)
  rw [he] at hw
  have h₁ := mul_le_mul_of_nonneg_left hw hℓ
  have h₂ := mul_le_mul_of_nonneg_left hC (Real.rpow_nonneg hM.le (s/r))
  nlinarith only [h₁,h₂]

theorem population_work_moment_bound (μ : Measure Gap) [IsProbabilityMeasure μ]
    (α a ρ p : ℝ) (hα : 2*p < α) (ha : 0 < a) (ha' : a ≤ 1/2)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hp : 1 < p) (hm : PowerMargin μ α a)
    (q : SignLaw) (j : ℕ) :
    (∫ ω, (calibratedCost a ρ j ω : ℝ) ∂originalPopulationTapeLaw μ q) ≤
      cap (initialLevel a)*(1+workCoefficient p*(5*((j : ℝ)+1))^p*
        ((∫ d : Gap, (a/(d : ℝ))^(2*p) ∂μ)+
          (1+Real.log (1/ρ))^p*(∫ d : Gap, q.val d*(a/(d : ℝ))^(2*p) ∂μ))) := by
  let f : Gap → ℝ := fun d => (a/(d : ℝ))^(2*p)
  let D := workCoefficient p*(5*((j : ℝ)+1))^p
  let ℓ := (1+Real.log (1/ρ))^p
  let N := cap (initialLevel a)
  have hf : Integrable f μ := margin_inverse_integrable μ α a (2*p) ha (by linarith) hα hm
  have hqf : Integrable (fun d => q.val d*f d) μ := hf.bdd_mul q.property.1.aestronglyMeasurable
    (ae_of_all _ (fun d => by rw [Real.norm_of_nonneg (q.property.2 d).1]; exact (q.property.2 d).2))
  have hD : 0 ≤ D := mul_nonneg (workCoefficient_pos p hp).le (by positivity)
  have hℓ : 0 ≤ ℓ := Real.rpow_nonneg (by linarith [Real.log_nonneg ((one_le_div hρ).2 hρ1)]) _
  have hN : 0 ≤ N := (cap_pos _).le
  have hi : Integrable (fun d => N*(1+D*(f d+ℓ*(q.val d*f d)))) μ :=
    ((integrable_const (1 : ℝ)).add ((hf.add (hqf.const_mul ℓ)).const_mul D)).const_mul N
  have hmix := originalTape_integral_mixture μ q (fun ω => (calibratedCost a ρ j ω : ℝ))
    ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp (measurable_calibratedCost a ρ j))
    (cap (initialLevel a+terminalLevel ρ j)) (fun ω => by
      rw [abs_of_nonneg (Nat.cast_nonneg _)]
      have h := (Nat.cast_le (α := ℝ)).2 (bandCost_le (initialLevel a) (negativeThreshold j) (positiveThreshold ρ j) (terminalLevel ρ j) ω)
      simpa only [calibratedCost,cap,Nat.cast_pow,Nat.cast_ofNat] using h)
  rw [hmix]
  calc
    _ ≤ ∫ d : Gap, N*(1+D*(f d+ℓ*(q.val d*f d))) ∂μ := by
      apply integral_mono_of_nonneg ?_ hi ?_
      · exact ae_of_all _ (fun d => add_nonneg
          (mul_nonneg (q.property.2 d).1 (integral_nonneg (fun _ => Nat.cast_nonneg _)))
          (mul_nonneg (sub_nonneg.mpr (q.property.2 d).2) (integral_nonneg (fun _ => Nat.cast_nonneg _))))
      · refine ae_of_all _ (fun d => ?_)
        have hpos := mul_le_mul_of_nonneg_left (calibratedCost_conditional_bound a ρ p ha ha' hρ hρ1 hp j d true) (q.property.2 d).1
        have hneg := mul_le_mul_of_nonneg_left (calibratedCost_conditional_bound a ρ p ha ha' hρ hρ1 hp j d false) (sub_nonneg.mpr (q.property.2 d).2)
        simp only [ite_true,Bool.false_eq_true,ite_false,mul_one] at hpos hneg
        change q.val d*_ ≤ q.val d*(N*(1+D*ℓ*f d)) at hpos
        change (1-q.val d)*_ ≤ (1-q.val d)*(N*(1+D*f d)) at hneg
        have hterm : 0 ≤ N*D*q.val d*f d := mul_nonneg (mul_nonneg (mul_nonneg hN hD) (q.property.2 d).1) (Real.rpow_nonneg (div_pos ha d.property.1).le (2*p))
        nlinarith only [hpos,hneg,hterm]
    _ = _ := by
      have he := integral_add (integrable_const (μ := μ) (1 : ℝ)) ((hf.add (hqf.const_mul ℓ)).const_mul D)
      simp only [Pi.add_apply] at he
      rw [integral_const_mul,he,integral_const_mul,integral_add hf (hqf.const_mul ℓ),integral_const_mul]
      simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
      rfl

end ThresholdHC.RareAboveTwo
