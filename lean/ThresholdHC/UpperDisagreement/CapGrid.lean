import ThresholdHC.UpperDisagreement.CapOffset
import ThresholdHC.UpperCost.Grid

/-! The cap part of the disagreement along the dyadic grid of levels.

At scale `x = cap l*d^2`, the cap part of the disagreement of the classifiers at
caps `2^l` and `2^(l-1)` is at most `capWeight x`: one below `12/25`, and
`exp(-2*x) + exp(-x)` from there on. Weighted by `sqrt x`, the sum over the
levels is at most `321/100` for every gap (`cap_grid_le`): the levels below
`12/25` add a geometric sum, at most `(1 + sqrt 2)*sqrt s` for the first grid
point `s` in `[12/25, 24/25]`, and the rest are the doubled cap terms. -/
noncomputable section
namespace ThresholdHC.UpperDisagreement
open Real Finset ThresholdHC.Uniform713 ThresholdHC.UpperWork

/-- The cap part of the disagreement at scale `x`, with the trivial bound one below
`12/25`. -/
def capWeight (x : ℝ) : ℝ := if 12 / 25 ≤ x then Real.exp (-2 * x) + Real.exp (-x) else 1

theorem capWeight_nonneg (x : ℝ) : 0 ≤ capWeight x := by
  unfold capWeight
  split_ifs
  · exact add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  · exact zero_le_one

/-- The cap part of the disagreement along the grid, for every gap. -/
theorem cap_grid_le {d : ℝ} (hd : 0 < d) (hd2 : d ^ 2 < 12 / 25) (K : ℕ) :
    ∑ l ∈ range K, Real.sqrt (cap l * d ^ 2) * capWeight (cap l * d ^ 2) ≤ 321 / 100 := by
  classical
  set f : ℕ → ℝ := fun l => Real.sqrt (cap l * d ^ 2) * capWeight (cap l * d ^ 2) with hf
  have hf0 : ∀ l, 0 ≤ f l := fun l => mul_nonneg (Real.sqrt_nonneg _) (capWeight_nonneg _)
  have hdd : 0 < d ^ 2 := by positivity
  have hex : ∃ l, 12 / 25 ≤ cap l * d ^ 2 := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((12 / 25) / d ^ 2) (by norm_num : (1 : ℝ) < 2)
    exact ⟨n, by have := (div_lt_iff₀ hdd).1 hn; simp only [cap]; linarith⟩
  set M := Nat.find hex with hM
  have hMspec : 12 / 25 ≤ cap M * d ^ 2 := Nat.find_spec hex
  have hMmin : ∀ l < M, cap l * d ^ 2 < 12 / 25 := fun l hl => not_le.1 (Nat.find_min hex hl)
  have hM0 : M ≠ 0 := by
    intro h0
    rw [h0, cap_zero, one_mul] at hMspec
    linarith
  obtain ⟨M', hM'⟩ := Nat.exists_eq_succ_of_ne_zero hM0
  set s := cap M * d ^ 2 with hs_def
  have hs2 : s ≤ 24 / 25 := by
    have h := hMmin M' (by omega)
    rw [hs_def, hM', cap_succ]
    nlinarith
  have hext : ∑ l ∈ range K, f l ≤ ∑ l ∈ range (M + K), f l :=
    sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) (fun l _ _ => hf0 l)
  rw [sum_range_add] at hext
  have hpre : ∀ l ∈ range M, f l = Real.sqrt 2 ^ l * d := by
    intro l hl
    have hlt := hMmin l (mem_range.1 hl)
    simp only [hf, capWeight]
    rw [ite_eq_right (not_le.2 hlt), mul_one]
    exact UpperCost.sqrt_cap_mul_sq l hd.le
  have hpost : ∀ i, f (M + i) = capTerm (2 ^ i * s) := by
    intro i
    have hcap : cap (M + i) * d ^ 2 = 2 ^ i * s := by
      rw [hs_def, show cap (M + i) = 2 ^ i * cap M by simp only [cap]; ring]
      ring
    have hge : 12 / 25 ≤ cap (M + i) * d ^ 2 := by
      rw [hcap]
      have : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
      nlinarith
    simp only [hf, capWeight, capTerm]
    rw [ite_eq_left hge, hcap]
  rw [sum_congr rfl hpre, sum_congr rfl (fun i _ => hpost i)] at hext
  have hgeo := UpperCost.geom_below d M
  have hsqrtM : Real.sqrt 2 ^ M * d = Real.sqrt s := by
    rw [hs_def, UpperCost.sqrt_cap_mul_sq M hd.le]
  rw [hsqrtM] at hgeo
  have hb := cap_offset_le s hMspec hs2 K
  have hd0 : 0 ≤ d * (1 + Real.sqrt 2) := by positivity
  linarith

end ThresholdHC.UpperDisagreement
