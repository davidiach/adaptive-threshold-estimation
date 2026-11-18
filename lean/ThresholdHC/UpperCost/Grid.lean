import ThresholdHC.UpperCost.Offset
import ThresholdHC.UpperWork.LevelSum

/-! The survival sum along one dyadic grid.

Fix a threshold scale `v ≥ 1` and a gap `d` with `d^2 < v`. The checks with
`k` flips at scale `y = cap k*d^2` survive with probability at most
`gridSurvival v y`: one below the scale, and `exp(-2*(sqrt y - sqrt v)^2)` from
it on. With `s` in `[1, 2]` the first grid ratio `y/v` at or above one, the
checks below the scale add a geometric sum, which with the extra term
`d*(1 + sqrt 2)` is exactly `(1 + sqrt 2)*sqrt (s*v)`, and the checks from
the scale on add `sqrt v*tailTerm v (2^i*s)`. An offset bound `C` for
`tailTerm v` then bounds the whole sum by `sqrt v*C` (`grid_sum_le`). -/
noncomputable section
namespace ThresholdHC.UpperCost
open Real Finset ThresholdHC.Uniform713 ThresholdHC.UpperWork

/-- The survival factor of a check at scale `y` with threshold scale `v`. -/
def gridSurvival (v y : ℝ) : ℝ :=
  if v ≤ y then Real.exp (-2 * (Real.sqrt y - Real.sqrt v) ^ 2) else 1

theorem gridSurvival_nonneg (v y : ℝ) : 0 ≤ gridSurvival v y := by
  unfold gridSurvival
  split_ifs
  · exact (Real.exp_pos _).le
  · exact zero_le_one

theorem sqrt_cap_mul_sq (k : ℕ) {d : ℝ} (hd : 0 ≤ d) :
    Real.sqrt (cap k * d ^ 2) = Real.sqrt 2 ^ k * d := by
  rw [Real.sqrt_mul (cap_pos k).le, Real.sqrt_sq hd, sqrt_cap]

/-- Below the first grid point: `∑_{k<n} sqrt 2^k*d + d*(1 + sqrt 2)` equals
`(1 + sqrt 2)*sqrt 2^n*d`. -/
theorem geom_below (d : ℝ) (n : ℕ) :
    ∑ k ∈ range n, Real.sqrt 2 ^ k * d + d * (1 + Real.sqrt 2) =
      (1 + Real.sqrt 2) * (Real.sqrt 2 ^ n * d) := by
  have hσ : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  induction n with
  | zero => simp; ring
  | succ n ih =>
    rw [sum_range_succ, pow_succ]
    linear_combination ih - (Real.sqrt 2 ^ n * d) * hσ

/-- The survival sum along one grid, with the geometric extension below `k = 0`. -/
theorem grid_sum_le {v d C : ℝ} (hv : 1 ≤ v) (hd : 0 < d) (hdv : d ^ 2 < v)
    (hoff : ∀ s, 1 ≤ s → s ≤ 2 → ∀ I : ℕ,
      (1 + Real.sqrt 2) * Real.sqrt s + ∑ i ∈ range I, tailTerm v (2 ^ i * s) ≤ C)
    (K : ℕ) :
    ∑ k ∈ range K, Real.sqrt (cap k * d ^ 2) * gridSurvival v (cap k * d ^ 2) +
        d * (1 + Real.sqrt 2) ≤ Real.sqrt v * C := by
  classical
  set f : ℕ → ℝ := fun k => Real.sqrt (cap k * d ^ 2) * gridSurvival v (cap k * d ^ 2) with hf
  have hf0 : ∀ k, 0 ≤ f k := fun k => mul_nonneg (Real.sqrt_nonneg _) (gridSurvival_nonneg _ _)
  have hd2 : 0 < d ^ 2 := by positivity
  have hv0 : 0 < v := by linarith
  have hex : ∃ k, v ≤ cap k * d ^ 2 := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (v / d ^ 2) (by norm_num : (1 : ℝ) < 2)
    exact ⟨n, by have := (div_lt_iff₀ hd2).1 hn; simp only [cap]; linarith⟩
  set M := Nat.find hex with hM
  have hMspec : v ≤ cap M * d ^ 2 := Nat.find_spec hex
  have hMmin : ∀ k < M, cap k * d ^ 2 < v := fun k hk => not_le.1 (Nat.find_min hex hk)
  have hM0 : M ≠ 0 := by
    intro h0
    rw [h0, cap_zero, one_mul] at hMspec
    linarith
  obtain ⟨M', hM'⟩ := Nat.exists_eq_succ_of_ne_zero hM0
  have hMle : cap M * d ^ 2 ≤ 2 * v := by
    have h := hMmin M' (by omega)
    rw [hM', cap_succ]
    nlinarith
  set s := cap M * d ^ 2 / v with hs_def
  have hs1 : 1 ≤ s := (one_le_div hv0).2 hMspec
  have hs2 : s ≤ 2 := (div_le_iff₀ hv0).2 (by linarith)
  have hext : ∑ k ∈ range K, f k ≤ ∑ k ∈ range (M + K), f k :=
    sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) (fun k _ _ => hf0 k)
  rw [sum_range_add] at hext
  have hpre : ∀ k ∈ range M, f k = Real.sqrt 2 ^ k * d := by
    intro k hk
    have hlt := hMmin k (mem_range.1 hk)
    simp only [hf, gridSurvival]
    rw [ite_eq_right (not_le.2 hlt), mul_one]
    exact sqrt_cap_mul_sq k hd.le
  have hsv : cap M * d ^ 2 = s * v := by rw [hs_def]; field_simp
  have hsqrtM : Real.sqrt 2 ^ M * d = Real.sqrt v * Real.sqrt s := by
    rw [← sqrt_cap_mul_sq M hd.le, hsv, Real.sqrt_mul (by linarith) v]
    ring
  have hpost : ∀ i, f (M + i) = Real.sqrt v * tailTerm v (2 ^ i * s) := by
    intro i
    have hcap : cap (M + i) * d ^ 2 = (2 ^ i * s) * v := by
      rw [show cap (M + i) = 2 ^ i * cap M by simp only [cap]; ring, mul_assoc, hsv]
      ring
    have hge : v ≤ cap (M + i) * d ^ 2 := by
      rw [hcap]
      have : (1 : ℝ) ≤ 2 ^ i * s := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hs1
      nlinarith
    have ht0 : 0 ≤ 2 ^ i * s := by positivity
    have hroot : Real.sqrt (cap (M + i) * d ^ 2) = Real.sqrt (2 ^ i * s) * Real.sqrt v := by
      rw [hcap, Real.sqrt_mul ht0]
    simp only [hf, gridSurvival, tailTerm]
    rw [ite_eq_left hge]
    rw [hroot]
    have hv' : Real.sqrt v ^ 2 = v := Real.sq_sqrt hv0.le
    have he : -2 * (Real.sqrt (2 ^ i * s) * Real.sqrt v - Real.sqrt v) ^ 2 =
        -2 * v * (Real.sqrt (2 ^ i * s) - 1) ^ 2 := by
      have hsq : (Real.sqrt (2 ^ i * s) * Real.sqrt v - Real.sqrt v) ^ 2 =
          Real.sqrt v ^ 2 * (Real.sqrt (2 ^ i * s) - 1) ^ 2 := by ring
      rw [hsq, hv']
      ring
    rw [he]
    ring
  rw [sum_congr rfl hpre, sum_congr rfl (fun i _ => hpost i), ← mul_sum] at hext
  have hgeo := geom_below d M
  rw [hsqrtM] at hgeo
  have hb := hoff s hs1 hs2 K
  have hsv0 : 0 ≤ Real.sqrt v := Real.sqrt_nonneg v
  calc
    _ ≤ ∑ k ∈ range M, Real.sqrt 2 ^ k * d +
          Real.sqrt v * ∑ i ∈ range K, tailTerm v (2 ^ i * s) + d * (1 + Real.sqrt 2) := by
      linarith
    _ = Real.sqrt v * ((1 + Real.sqrt 2) * Real.sqrt s +
          ∑ i ∈ range K, tailTerm v (2 ^ i * s)) := by
      linear_combination hgeo
    _ ≤ Real.sqrt v * C := mul_le_mul_of_nonneg_left hb hsv0

end ThresholdHC.UpperCost
