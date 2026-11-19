import ThresholdHC.UpperSign.Drift

/-! The drift bounds below the split, for scales up to one half.

The drift terms of `UpperSign.Drift` are bounded there for scales `Y ≤ 3/8`.
The split at `19/20` needs scales up to `19/40`, so this module repeats the
tail bound, the split of the series and the link to the drift bounds of a
classifier for `Y ≤ 1/2`. The numerical tables are in `DriftTable`. -/
noncomputable section
namespace ThresholdHC.UpperQuarter
open MeasureTheory ProbabilityTheory Finset ThresholdHC.Tier2 ThresholdHC.UpperSign

section Drift
open Real Uniform713

/-- Far drift terms decay geometrically, for scales up to one half. -/
theorem driftTerm_tail_half {J : ℕ} (hJ : 7 ≤ J) {Y : ℝ} (hY : Y ≤ 1 / 2) :
    driftTerm J Y ≤ (31 / 100) ^ J := by
  have hl := Real.log_two_gt_d9
  have hJr : (7 : ℝ) ≤ J := by exact_mod_cast hJ
  set v := 1 + (J : ℝ) * Real.log 2 with hv
  have hv1 : 1 ≤ v := by simp only [hv]; nlinarith
  have hsv : 1 ≤ Real.sqrt v := Real.one_le_sqrt.2 hv1
  have hpow : (128 : ℝ) ≤ 2 ^ J := by
    have := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hJ
    norm_num at this ⊢
    linarith
  have hy : Y / 2 ^ J ≤ (1 / 16) ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hsy : Real.sqrt (Y / 2 ^ J) ≤ 1 / 16 := (Real.sqrt_le_left (by norm_num)).2 hy
  have hgap : (15 / 16) * Real.sqrt v ≤ Real.sqrt v - Real.sqrt (Y / 2 ^ J) := by nlinarith
  have hsq : (15 / 16) ^ 2 * v ≤ (Real.sqrt v - Real.sqrt (Y / 2 ^ J)) ^ 2 := by
    have h := pow_le_pow_left₀ (by positivity) hgap 2
    rw [mul_pow, Real.sq_sqrt (by linarith)] at h
    exact h
  have he : Real.exp (-(6 / 5 : ℝ)) ≤ 31 / 100 :=
    UpperWork.exp_neg_le_of_taylor (by norm_num) 8
      (by norm_num [Finset.sum_range_succ, Nat.factorial])
  unfold driftTerm
  calc
    _ ≤ Real.exp (-(6 / 5 : ℝ) * J) := by
      apply Real.exp_le_exp.2
      nlinarith
    _ = Real.exp (-(6 / 5 : ℝ)) ^ J := by rw [mul_comm, Real.exp_nat_mul]
    _ ≤ (31 / 100) ^ J := pow_le_pow_left₀ (Real.exp_pos _).le he J


/-- Keep the first six drift terms; the rest add at most `1/2000`. -/
theorem driftSeries_split_half (L : ℕ) (Y : ℝ) (hY : Y ≤ 1 / 2) :
    ∑ J ∈ range L, driftTerm (J + 1) Y ≤
      driftTerm 1 Y + driftTerm 2 Y + driftTerm 3 Y + driftTerm 4 Y + driftTerm 5 Y +
        driftTerm 6 Y + 1 / 2000 := by
  have hsplit : ∑ J ∈ range L, driftTerm (J + 1) Y ≤
      ∑ J ∈ range 6, driftTerm (J + 1) Y + ∑ J ∈ range L, driftTerm (6 + J + 1) Y := by
    rw [← Finset.sum_range_add]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      (fun J _ _ => driftTerm_nonneg _ _)
  have htail : ∑ J ∈ range L, driftTerm (6 + J + 1) Y ≤ 1 / 2000 := by
    calc
      _ ≤ ∑ J ∈ range L, (31 / 100 : ℝ) ^ 7 * (31 / 100) ^ J := by
        apply sum_le_sum
        intro J _
        refine (driftTerm_tail_half (by omega) hY).trans (le_of_eq ?_)
        rw [← pow_add]
        ring_nf
      _ = (31 / 100 : ℝ) ^ 7 * ∑ J ∈ range L, (31 / 100 : ℝ) ^ J := by rw [mul_sum]
      _ ≤ (31 / 100 : ℝ) ^ 7 * (100 / 69) := by
        gcongr
        have hs := sum_le_hasSum (range L) (fun J _ => pow_nonneg (by norm_num : (0 : ℝ) ≤ 31 / 100) J)
          (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 31 / 100) (by norm_num))
        refine hs.trans (le_of_eq ?_)
        norm_num
      _ ≤ 1 / 2000 := by norm_num
  have h6 : ∑ J ∈ range 6, driftTerm (J + 1) Y = driftTerm 1 Y + driftTerm 2 Y + driftTerm 3 Y +
      driftTerm 4 Y + driftTerm 5 Y + driftTerm 6 Y := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  rw [h6] at hsplit
  linarith

end Drift


section Link
open Real Uniform713

/-- The drift bounds of the cap-`2^L` classifier are at most the drift series at any
scale `Y ≥ cap L*d^2`. -/
theorem driftSum_le_half (L : ℕ) {d Y : ℝ} (hd : 0 < d) (hx : cap L * d ^ 2 ≤ Y) (hY : Y ≤ 1 / 2) :
    ∑ k ∈ range L, driftBound L k d ≤ ∑ J ∈ range L, driftTerm (J + 1) Y := by
  rw [← sum_range_reflect (fun k => driftBound L k d) L]
  apply sum_le_sum
  intro J hJ
  have hJL := mem_range.1 hJ
  set k := L - 1 - J with hk
  have hkL : k + (J + 1) = L := by omega
  have hc := cap_pos k
  have hratio : cap (k + (J + 1)) / cap k = 2 ^ (J + 1) := by
    simp only [cap, pow_add]
    field_simp
  set v := 1 + ((J + 1 : ℕ) : ℝ) * Real.log 2 with hv
  have hl := Real.log_two_gt_d9
  have hv1 : 1 ≤ v := by simp only [hv]; push_cast; nlinarith
  have ht : Tier2.Model.threshold1 (cap k) (cap L) = Real.sqrt (v / cap k) := by
    rw [← hkL]
    unfold Tier2.Model.threshold1
    rw [hratio, Real.log_pow]
  have hcapL : cap L = cap k * 2 ^ (J + 1) := by rw [← hkL]; simp only [cap, pow_add]
  have hyk : cap k * d ^ 2 ≤ Y / 2 ^ (J + 1) := by
    rw [le_div_iff₀ (by positivity)]
    rw [hcapL] at hx
    linarith
  have hY2 : Y / 2 ^ (J + 1) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity)]
    have : (2 : ℝ) ≤ 2 ^ (J + 1) := by
      have := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show 1 ≤ J + 1 by omega)
      simpa using this
    nlinarith
  have hdt : d ≤ Tier2.Model.threshold1 (cap k) (cap L) := by
    rw [ht]
    apply Real.le_sqrt_of_sq_le
    rw [le_div_iff₀ hc]
    nlinarith
  have hexp : cap k * (Real.sqrt (v / cap k) - d) ^ 2 =
      (Real.sqrt v - Real.sqrt (cap k * d ^ 2)) ^ 2 := by
    have hs : Real.sqrt v = Real.sqrt (cap k) * Real.sqrt (v / cap k) := by
      rw [← Real.sqrt_mul hc.le, mul_div_cancel₀ _ hc.ne']
    rw [Real.sqrt_mul hc.le, Real.sqrt_sq hd.le, hs]
    have hc' : Real.sqrt (cap k) ^ 2 = cap k := Real.sq_sqrt hc.le
    rw [show (Real.sqrt (cap k) * Real.sqrt (v / cap k) - Real.sqrt (cap k) * d) ^ 2 =
      Real.sqrt (cap k) ^ 2 * (Real.sqrt (v / cap k) - d) ^ 2 by ring, hc']
  have hsy : Real.sqrt (cap k * d ^ 2) ≤ Real.sqrt (Y / 2 ^ (J + 1)) := Real.sqrt_le_sqrt hyk
  have hsY : Real.sqrt (Y / 2 ^ (J + 1)) ≤ Real.sqrt v := Real.sqrt_le_sqrt (by linarith)
  unfold driftBound driftTerm
  rw [ite_eq_left hdt, ht, mul_assoc, hexp]
  apply Real.exp_le_exp.2
  have h1 : (Real.sqrt v - Real.sqrt (Y / 2 ^ (J + 1))) ^ 2 ≤
      (Real.sqrt v - Real.sqrt (cap k * d ^ 2)) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  rw [hv] at h1 ⊢
  push_cast at h1 ⊢
  linarith

end Link


end ThresholdHC.UpperQuarter
