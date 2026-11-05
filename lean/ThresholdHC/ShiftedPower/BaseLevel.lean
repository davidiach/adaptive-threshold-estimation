import ThresholdHC.ShiftedPower.Geometric

noncomputable section
open Real
namespace ThresholdHC.ShiftedPower

/-- A dyadic starting cap is chosen using the known envelope and rarity.
Its error scale lies between rho and twice rho. -/
theorem base_level {α a ρ : ℝ} (hα : 0 < α) (hu : α < 2) (ha : 0 < a) (ha' : a ≤ 1)
    (hr : 0 < ρ) (hr' : ρ ≤ 1) :
    ∃ k : ℕ, ρ ≤ massBound α a k ∧ massBound α a k ≤ 2*ρ := by
  let A := massBound α a 0
  let q := decay α
  have hA : 1 ≤ A := by
    change 1 ≤ (resolution 0/a)^α
    have he : resolution 0 = 1 := by simp [resolution]
    rw [he]
    exact Real.one_le_rpow ((one_le_div ha).mpr ha') hα.le
  have hq0 : 0 < q := by have h := (decay_bounds hα hu).1; dsimp [q]; linarith
  have hq1 : q < 1 := (decay_bounds hα hu).2
  have hx : 1 ≤ A/ρ := (one_le_div hr).mpr (hr'.trans hA)
  have hy : 1 < q⁻¹ := one_lt_inv₀ hq0 |>.mpr hq1
  obtain ⟨k,hk,hk'⟩ := exists_nat_pow_near hx hy
  have he : massBound α a k = A/(q⁻¹)^k := by
    have h := mass_add (α := α) ha 0 k
    simpa only [Nat.zero_add,A,q,inv_pow,div_inv_eq_mul] using h
  have hkpos : 0 < (q⁻¹)^k := pow_pos (inv_pos.mpr hq0) k
  have hlo : ρ*(q⁻¹)^k ≤ A := by
    have h := (le_div_iff₀ hr).mp hk
    nlinarith only [h]
  have hhi : A < (ρ/q)*(q⁻¹)^k := by
    have h := (div_lt_iff₀ hr).mp hk'
    rw [pow_succ] at h
    convert h using 1; ring
  have hqhalf : 1/2 < q := (decay_bounds hα hu).1
  refine ⟨k,?_,?_⟩
  · rw [he]
    exact (le_div_iff₀ hkpos).mpr hlo
  · rw [he]
    apply ((div_lt_iff₀ hkpos).mpr hhi).le.trans
    apply (div_le_iff₀ hq0).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hqhalf.le hr.le]

theorem finite_bias_level {α a ε : ℝ} (hα : 0 < α) (hu : α < 2) (ha : 0 < a)
    (hε : 0 < ε) (k : ℕ) : ∃ J : ℕ, errorBound α a (k+J) ≤ ε := by
  have hm := mass_positive (α := α) ha k
  obtain ⟨J,hJ⟩ := exists_pow_lt_of_lt_one (x := ε/(2*massBound α a k)) (y := decay α)
    (by positivity) (decay_bounds hα hu).2
  refine ⟨J,(error_le_mass ha hα hu (k+J)).trans ?_⟩
  rw [mass_add ha]
  have h := (lt_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<2) hm)).mp hJ
  nlinarith only [h]

theorem amplitude_identity {α a : ℝ} (hα : 0 < α) (ha : 0 < a) (k : ℕ) :
    sqrt ((2:ℝ)^k)*massBound α a k = (massBound α a k)^(1-1/α)/a := by
  let x := resolution k/a
  have hx : 0 < x := div_pos (resolution_pos k) ha
  have he : (massBound α a k)^(1-1/α) = x^α/x := by
    change (x^α)^(1-1/α) = _
    rw [← Real.rpow_mul hx.le,show α*(1-1/α) = α-1 by field_simp,Real.rpow_sub hx,Real.rpow_one]
  rw [he]
  change sqrt ((2:ℝ)^k)*x^α = (x^α/x)/a
  dsimp [x,resolution]
  field_simp

end ThresholdHC.ShiftedPower
