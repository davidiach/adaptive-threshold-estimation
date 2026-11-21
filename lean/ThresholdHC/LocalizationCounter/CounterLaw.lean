import ThresholdHC.LocalizationCounter.Specification

/-! The two-atom law of Theorem `loc:thm:counter`: it is a probability law,
integrals against it are two-term sums, and the heuristic at `h = B^{-1/2} = ρ²`
is `ρ² + 4(1-ρ)ρ²√ρ ≤ 3ρ²`. At `h/√ρ = ρ^{3/2}` the atom `d = ρ²` is saturated
and the atom `1/4` is not, because `4ρ^{3/2} ≤ 1/2`. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ThresholdHC.LocalizationCounter
open ThresholdHC.Tier6

theorem counterLaw_probability_proof : CounterLawProbabilityStatement := by
  intro ρ d h0 h1
  constructor
  simp only [counterLaw, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add h0 (by linarith)]
  simp

theorem integral_counterLaw (ρ : ℝ) (d : Gap) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (f : Gap → ℝ) :
    ∫ x, f x ∂counterLaw ρ d = ρ * f d + (1 - ρ) * f quarterGap := by
  have h₁ : Integrable f (Measure.dirac d) := integrable_dirac (by simp)
  have h₂ : Integrable f (Measure.dirac quarterGap) := integrable_dirac (by simp)
  rw [counterLaw, integral_add_measure (h₁.smul_measure ENNReal.ofReal_ne_top)
    (h₂.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    integral_dirac, integral_dirac, ENNReal.toReal_ofReal h0,
    ENNReal.toReal_ofReal (by linarith), smul_eq_mul, smul_eq_mul]

theorem quarterGap_val : ((quarterGap : Gap) : ℝ) = 1/4 := rfl

theorem counter_heuristic_eq (ρ : ℝ) (d : Gap) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4)
    (hd : (d : ℝ) = ρ^2) :
    heuristic (counterLaw ρ d) ρ (1 / Real.sqrt (1/ρ^4)) =
      ρ^2 + 4*(1-ρ)*ρ^2*Real.sqrt ρ := by
  unfold heuristic modulus
  rw [integral_counterLaw ρ d hρ.le (by linarith)]
  simp only [clippedGap, hd, quarterGap_val]
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 < s ∧ ρ = s^2 :=
    ⟨Real.sqrt ρ, Real.sqrt_pos.mpr hρ, (Real.sq_sqrt hρ.le).symm⟩
  have hs1 : s ≤ 1/2 := by nlinarith
  have hsq4 : Real.sqrt (1/(s^2)^4) = 1/s^4 := by
    rw [show (1:ℝ)/(s^2)^4 = (1/s^4)^2 by ring]
    exact Real.sqrt_sq (by positivity)
  rw [hsq4, Real.sqrt_sq hs.le]
  have hx : 1 / (1/s^4) / s = s^3 := by field_simp
  rw [hx]
  have m1 : min 1 (s^3 / (s^2)^2) = 1 := by
    apply min_eq_left
    rw [show s^3/(s^2)^2 = 1/s by field_simp, le_div_iff₀ hs]
    linarith
  have hs3 : s^3 ≤ 1/8 := by
    have := pow_le_pow_left₀ hs.le hs1 3
    norm_num at this
    linarith
  have m2 : min 1 (s^3 / (1/4)) = 4*s^3 := by
    rw [min_eq_right (by linarith [show s^3/(1/4) = 4*s^3 by ring])]
    ring
  rw [m1, m2]
  ring

theorem counter_heuristic_le (ρ : ℝ) (d : Gap) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1/4)
    (hd : (d : ℝ) = ρ^2) :
    heuristic (counterLaw ρ d) ρ (1 / Real.sqrt (1/ρ^4)) ≤ 3*ρ^2 := by
  rw [counter_heuristic_eq ρ d hρ hρ1 hd]
  have hs : Real.sqrt ρ ≤ 1/2 := by
    rw [show (1/2 : ℝ) = Real.sqrt (1/4) by
      rw [show (1/4 : ℝ) = (1/2)^2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hρ1
  have hs0 := Real.sqrt_nonneg ρ
  have h2 : 0 ≤ ρ^2 := sq_nonneg ρ
  have hk : 4*(1-ρ)*Real.sqrt ρ ≤ 2 := by nlinarith
  nlinarith

end ThresholdHC.LocalizationCounter
