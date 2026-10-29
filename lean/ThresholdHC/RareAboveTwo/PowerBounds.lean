import ThresholdHC.RareAboveTwo.Parameters
import Mathlib.Analysis.SpecificLimits.Normed

/-! Analytic envelopes used in the stage-survival work sum. -/
noncomputable section
open scoped BigOperators
namespace ThresholdHC.RareAboveTwo

theorem exp_neg_le_rpow (x p : ℝ) (hx : 0 < x) (hp : 0 < p) :
    Real.exp (-x) ≤ (p/x)^p := by
  rw [Real.rpow_def_of_pos (div_pos hp hx)]
  apply Real.exp_le_exp.mpr
  have hl := Real.log_le_sub_one_of_pos (div_pos hx hp)
  have hm := mul_le_mul_of_nonneg_left hl hp.le
  have he : p*(x/p-1) = x-p := by field_simp
  rw [he] at hm
  rw [Real.log_div hp.ne' hx.ne',Real.log_div hx.ne' hp.ne'] at *
  nlinarith

theorem indicator_power_bound (x A p : ℝ) (hx : 0 < x) (hA : 0 ≤ A) (hp : 0 < p) :
    (if x ≤ 2*A then (1 : ℝ) else 0) ≤ (2*A/x)^p := by
  split_ifs with h
  · have hb : 1 ≤ 2*A/x := (one_le_div hx).2 h
    simpa using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hb hp.le
  · exact Real.rpow_nonneg (by positivity) _

theorem survival_power_bound (x A p : ℝ) (hx : 0 < x) (hA : 0 ≤ A) (hp : 0 < p) :
    (if x ≤ 2*A then (1 : ℝ) else 0)+Real.exp (-(x/2)) ≤
      ((2*A)^p+(2*p)^p)/(x^p) := by
  have h := add_le_add (indicator_power_bound x A p hx hA hp)
    (exp_neg_le_rpow (x/2) p (by positivity) hp)
  apply h.trans_eq
  rw [show p/(x/2) = (2*p)/x by ring,Real.div_rpow (by positivity) hx.le,
    Real.div_rpow (by positivity) hx.le]
  ring

/-- Every fixed real polynomial is summable against a strictly decaying geometric law. -/
theorem summable_real_power_geometric (p r : ℝ) (hp : 0 ≤ p) (hr : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun k : ℕ => ((k : ℝ)+1)^p*r^k) := by
  obtain ⟨M,hM⟩ := exists_nat_ge p
  have hs : Summable (fun k : ℕ => ((k : ℝ)+1)^M*r^k) := by
    have h := summable_pow_mul_geometric_of_norm_lt_one M (r := r) (by simpa [Real.norm_of_nonneg hr] using hr1)
    have h' := h.comp_injective (i := fun k : ℕ => k+1) (fun a b h => Nat.add_right_cancel h)
    by_cases hr0 : r = 0
    · subst r
      have he : (fun k : ℕ => ((k : ℝ)+1)^M*(0 : ℝ)^k) = fun k : ℕ => (0 : ℝ)^k := by
        funext k
        cases k <;> simp
      rw [he]
      exact summable_geometric_of_norm_lt_one (by norm_num)
    · have he : (fun k : ℕ => ((k : ℝ)+1)^M*r^k) =
          fun k => ((k+1 : ℕ) : ℝ)^M*r^(k+1)/r := by
        funext k
        push_cast
        rw [pow_succ]
        field_simp
      rw [he]
      exact h'.div_const r
  apply hs.of_nonneg_of_le (fun k => by positivity)
  intro k
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg hr k)
  simpa only [Real.rpow_natCast] using
    Real.rpow_le_rpow_of_exponent_le (by have := Nat.cast_nonneg (α := ℝ) k; linarith) hM

/-- The rarity factor controls every fixed power of the asymmetric log threshold. -/
theorem rarity_log_power_bound (β p : ℝ) (hβ : 0 < β) (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      ρ^β*(1+Real.log (1/ρ))^p ≤ C := by
  let ε := β/p
  have hε : 0 < ε := div_pos hβ hp
  refine ⟨(1+1/ε)^p,Real.rpow_pos_of_pos (by positivity) _,?_⟩
  intro ρ hρ hρ1
  have harg : 1 ≤ 1/ρ := (one_le_div hρ).2 hρ1
  have hrpow : 1 ≤ (1/ρ)^ε := by
    simpa using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) harg hε.le
  have hl := Real.log_le_rpow_div (by positivity : 0 ≤ 1/ρ) hε
  have hl0 : 0 ≤ Real.log (1/ρ) := Real.log_nonneg harg
  have hmajor : 1+Real.log (1/ρ) ≤ (1+1/ε)*(1/ρ)^ε := by
    have he : (1+1/ε)*(1/ρ)^ε = (1/ρ)^ε+(1/ρ)^ε/ε := by ring
    rw [he]
    linarith
  have hpow := Real.rpow_le_rpow (by linarith : 0 ≤ 1+Real.log (1/ρ)) hmajor hp.le
  have he : ρ^β*((1+1/ε)*(1/ρ)^ε)^p = (1+1/ε)^p := by
    rw [Real.mul_rpow (by positivity) (by positivity),← Real.rpow_mul (by positivity)]
    have hep : ε*p = β := by dsimp [ε]; field_simp
    rw [hep]
    simp only [one_div,Real.inv_rpow hρ.le]
    field_simp
  exact (mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hρ.le _)).trans_eq he

end ThresholdHC.RareAboveTwo
