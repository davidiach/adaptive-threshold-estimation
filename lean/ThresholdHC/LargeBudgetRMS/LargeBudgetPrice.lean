import ThresholdHC.LargeBudgetRMS.LargeBudgetTest

/-! At the critical gap, the symmetric information cost decreases with the budget. -/
noncomputable section
namespace ThresholdHC.SharpRMS.LargeBudget
open Real Set

/-- The largest total price for B≥N occurs at N. -/
theorem log_price_mono (c : ℝ) (hc : 0<c) :
    MonotoneOn (fun B : ℝ => B*log (1-c/B)) (Ioi c) := by
  have der (B : ℝ) (hb : B∈Ioi c) : HasDerivAt (fun x : ℝ => x*log (1-c/x))
      (log (1-c/B)+(1-c/B)⁻¹-1) B := by
    have bp : 0<B := hc.trans hb
    have pos : 0<1-c/B := sub_pos.mpr ((div_lt_one bp).2 hb)
    have q := ((hasDerivAt_const B c).div (hasDerivAt_id B) bp.ne').const_sub 1
    convert (hasDerivAt_id B).mul (q.log pos.ne') using 1
    · rfl
    dsimp
    field_simp [bp.ne',pos.ne',show B-c≠0 by exact (sub_pos.mpr hb).ne']
    ring
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioi c)
    (fun B hb => (der B hb).continuousAt.continuousWithinAt)
    (fun B hb => (der B (interior_subset hb)).hasDerivWithinAt)
  intro B hb
  have lt : c<B := interior_subset hb
  have pos : 0<1-c/B := sub_pos.mpr ((div_lt_one (hc.trans lt)).2 lt)
  have h := log_le_sub_one_of_pos (inv_pos.mpr pos)
  rw [log_inv] at h
  linarith only [h]

/-- A finite positive Taylor sum certifies the logarithmic price at the cutoff. -/
theorem rational_log_price (N a : ℝ) (hn : 4*bias^2<N) (ha : 0≤a) (k : ℕ)
    (cert : (1-4*bias^2/N)⁻¹ ≤ ∑ i ∈ Finset.range k, a^i/(i.factorial:ℝ)) :
    -a ≤ log (1-4*bias^2/N) := by
  have np : 0<N := lt_trans (by norm_num) hn
  have pos : 0<1-4*bias^2/N := sub_pos.mpr ((div_lt_one np).2 hn)
  have h := log_le_log (inv_pos.mpr pos) (cert.trans (sum_le_exp_of_nonneg ha k))
  rw [log_inv,log_exp] at h
  linarith only [h]

end ThresholdHC.SharpRMS.LargeBudget
