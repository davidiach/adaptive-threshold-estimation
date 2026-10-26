import ThresholdHC.Statements2
import ThresholdHC.Proofs.KL

/-!
Finite information inequalities for the Tier 2 targets.

The log-sum proof permits zero masses under absolute continuity. Pinsker follows
by reducing to the event where the first mass exceeds the second, then proving
the binary inequality by convexity. The testing helper uses a supporting line
at the separated pair and therefore also covers a test with power exactly one.
-/

noncomputable section
namespace ThresholdHC.Proofs
open ThresholdHC Real MeasureTheory

theorem bounded_ratio_log : ThresholdHC.Targets.bounded_ratio_log := by
  intro κ hκ0 hκ1
  refine ⟨1 + 2 / (1 - κ), ?_⟩
  intro x hxmin hxmax
  have ha : 0 < 1 - κ := sub_pos.mpr hκ1
  have hx : 0 < x := ha.trans_le hxmin
  have hy : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hysq := Real.sq_sqrt hx.le
  have hya : 1 - κ ≤ Real.sqrt x := by
    nlinarith [Real.sqrt_nonneg x]
  have hlog := Real.one_sub_inv_le_log_of_pos hy
  have hlogx := Real.log_sqrt hx.le
  have hinv : (Real.sqrt x)⁻¹ ≤ (1 - κ)⁻¹ := inv_anti₀ ha hya
  have hmain : -Real.log x + (x - 1) ≤
      (1 + 2 * (Real.sqrt x)⁻¹) * (Real.sqrt x - 1) ^ 2 := by
    have hcancel : Real.sqrt x * (Real.sqrt x)⁻¹ = 1 := mul_inv_cancel₀ hy.ne'
    nlinarith [hcancel]
  apply hmain.trans
  have hc : 1 + 2 * (Real.sqrt x)⁻¹ ≤ 1 + 2 / (1 - κ) := by
    rw [div_eq_mul_inv]
    linarith
  exact mul_le_mul_of_nonneg_right hc (sq_nonneg _)

private theorem sum_min_eq_one_sub_tv {α : Type} [Fintype α] (P Q : α → ℝ)
    (hP : ∑ x, P x = 1) (hQ : ∑ x, Q x = 1) :
    ∑ x, min (P x) (Q x) = 1 - tvFT P Q := by
  have heq (x : α) : min (P x) (Q x) = (P x + Q x - |P x - Q x|) / 2 := by
    rcases le_total (P x) (Q x) with h | h
    · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
      ring
    · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
      ring
  simp_rw [heq]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_add_distrib, hP, hQ]
  unfold tvFT
  ring

theorem two_point_rms_lower : ThresholdHC.Targets.two_point_rms_lower := by
  intro α _ P Q θ a b R hP hQ hP1 hQ1 hab hRa hRb
  have hp (x : α) : (b - a)^2 * min (P x) (Q x) ≤
      2 * (P x * (θ x - a)^2 + Q x * (θ x - b)^2) := by
    have hmin0 : 0 ≤ min (P x) (Q x) := le_min (hP x) (hQ x)
    have hm : (b-a)^2 ≤ 2 * ((θ x-a)^2 + (θ x-b)^2) := by nlinarith [sq_nonneg (2*θ x-a-b)]
    have hs := mul_le_mul_of_nonneg_right hm hmin0
    have hleft := mul_le_mul_of_nonneg_right (min_le_left (P x) (Q x)) (sq_nonneg (θ x-a))
    have hright := mul_le_mul_of_nonneg_right (min_le_right (P x) (Q x)) (sq_nonneg (θ x-b))
    nlinarith
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun x _ => hp x)
  simp only [← Finset.mul_sum, Finset.sum_add_distrib] at hs
  rw [sum_min_eq_one_sub_tv P Q hP1 hQ1] at hs
  nlinarith [sq_nonneg R]

namespace Tier2Information

theorem kl_supporting_line (a b u v : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : b = 0 → a = 0) (hu : 0 < u) (hv : 0 < v) :
    a * Real.log (u/v) + a - (u/v)*b ≤ a * Real.log (a/b) := by
  by_cases ha0 : a = 0
  · simp only [ha0, zero_mul, zero_add, zero_div, Real.log_zero]
    simpa using neg_nonpos.mpr (mul_nonneg (div_nonneg hu.le hv.le) hb)
  have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hb' : 0 < b := lt_of_le_of_ne hb (Ne.symm (mt hab ha0))
  have hlog : Real.log (b*u/(a*v)) = Real.log (u/v) - Real.log (a/b) := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul hb'.ne' hu.ne',
      Real.log_mul ha'.ne' hv.ne', Real.log_div hu.ne' hv.ne', Real.log_div ha'.ne' hb'.ne']
    ring
  have hl' := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (show 0 < b*u/(a*v) by positivity)) ha
  rw [hlog] at hl'
  have heq : a * (b*u/(a*v)-1) = (u/v)*b-a := by field_simp
  rw [heq] at hl'
  nlinarith

theorem log_sum_finite {α : Type} [Fintype α] (P Q : α → ℝ) (s : Finset α)
    (hP : ∀ a, 0 ≤ P a) (hQ : ∀ a, 0 ≤ Q a) (hPQ : ∀ a, Q a = 0 → P a = 0) :
    (∑ a ∈ s, P a) * Real.log ((∑ a ∈ s, P a) / (∑ a ∈ s, Q a)) ≤
      ∑ a ∈ s, P a * Real.log (P a / Q a) := by
  have hp : 0 ≤ ∑ a ∈ s, P a := Finset.sum_nonneg (fun a _ => hP a)
  have hq : 0 ≤ ∑ a ∈ s, Q a := Finset.sum_nonneg (fun a _ => hQ a)
  by_cases hp0 : ∑ a ∈ s, P a = 0
  · have hz : ∀ a ∈ s, P a = 0 := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => hP a)).mp hp0
    simp only [hp0, zero_mul]
    exact le_of_eq (Finset.sum_eq_zero (fun a ha => by rw [hz a ha, zero_mul])).symm
  have hp' : 0 < ∑ a ∈ s, P a := lt_of_le_of_ne hp (Ne.symm hp0)
  have hq' : 0 < ∑ a ∈ s, Q a := by
    by_contra hn
    have hq0 : ∑ a ∈ s, Q a = 0 := le_antisymm (not_lt.mp hn) hq
    have hz : ∀ a ∈ s, Q a = 0 := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => hQ a)).mp hq0
    exact hp0 (Finset.sum_eq_zero (fun a ha => hPQ a (hz a ha)))
  have hs := Finset.sum_le_sum (s := s) (fun a _ =>
    kl_supporting_line (P a) (Q a) _ _ (hP a) (hQ a) (hPQ a) hp' hq')
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum] at hs
  simpa only [div_mul_cancel₀ _ hq'.ne', add_sub_cancel_right] using hs

end Tier2Information

theorem kl_data_processing_finite : ThresholdHC.Targets.kl_data_processing_finite := by
  intro α _ P Q A hP hQ hPQ hP1 hQ1
  classical
  have hsumP := Finset.sum_add_sum_compl A P
  have hsumQ := Finset.sum_add_sum_compl A Q
  rw [hP1] at hsumP
  rw [hQ1] at hsumQ
  have hcp : 1 - ∑ a ∈ A, P a = ∑ a ∈ Aᶜ, P a := by linarith
  have hcq : 1 - ∑ a ∈ A, Q a = ∑ a ∈ Aᶜ, Q a := by linarith
  unfold klB
  rw [hcp, hcq]
  calc
    _ ≤ (∑ a ∈ A, P a * Real.log (P a / Q a)) +
        (∑ a ∈ Aᶜ, P a * Real.log (P a / Q a)) :=
      add_le_add (Tier2Information.log_sum_finite P Q A hP hQ hPQ)
        (Tier2Information.log_sum_finite P Q Aᶜ hP hQ hPQ)
    _ = klFT P Q := Finset.sum_add_sum_compl A _

namespace Tier2Information

theorem kl_test_separation (δ u v : ℝ) (hδ : 0 < δ) (hδhalf : δ < 1/2)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv : 0 < v) (hvδ : v ≤ δ)
    (hδu : 1-δ ≤ u) : klB (1-δ) δ ≤ klB u v := by
  have hδ1 : 0 < 1-δ := by linarith
  have hv1 : 0 < 1-v := by linarith
  have hC : 1 ≤ (1-δ)/δ := (one_le_div hδ).2 (by linarith)
  have hD : δ/(1-δ) ≤ 1 := (div_le_one hδ1).2 (by linarith)
  have hCD : 0 ≤ (1-δ)/δ - δ/(1-δ) := by linarith
  have hlog : 0 ≤ Real.log ((1-δ)/δ) - Real.log (δ/(1-δ)) := by
    apply sub_nonneg.mpr
    apply Real.log_le_log (div_pos hδ hδ1)
    linarith
  have hfirst := kl_supporting_line u v (1-δ) δ hu0 hv.le
    (fun h => False.elim (hv.ne' h)) hδ1 hδ
  have hsecond := kl_supporting_line (1-u) (1-v) δ (1-δ) (sub_nonneg.mpr hu1) hv1.le
    (fun h => False.elim (hv1.ne' h)) hδ hδ1
  have hUp := mul_nonneg (sub_nonneg.mpr hδu) hlog
  have hDown := mul_nonneg (sub_nonneg.mpr hvδ) hCD
  have hcancelC : ((1-δ)/δ)*δ = 1-δ := div_mul_cancel₀ _ hδ.ne'
  have hcancelD : (δ/(1-δ))*(1-δ) = δ := div_mul_cancel₀ _ hδ1.ne'
  have hδcomp : 1-(1-δ) = δ := by ring
  unfold klB
  rw [hδcomp]
  nlinarith

theorem binary_pinsker (u v : ℝ) (hu : 0 < u) (hu1 : u < 1)
    (hv : 0 < v) (hv1 : v < 1) : 2 * (u-v)^2 ≤ klB u v := by
  let f := fun t : ℝ => klB t v - 2*(t-v)^2
  let f' := fun t : ℝ => (Real.log (t/v)-Real.log ((1-t)/(1-v))) - 4*(t-v)
  let f'' := fun t : ℝ => 1/(t*(1-t)) - 4
  have hmem : ∀ x ∈ Set.uIcc u v, 0 < x ∧ x < 1 := by
    intro x hx
    exact ⟨lt_of_lt_of_le (lt_min hu hv) hx.1,
      lt_of_le_of_lt hx.2 (max_lt hu1 hv1)⟩
  have hd : ∀ x ∈ Set.uIcc u v, HasDerivAt f (f' x) x := by
    intro x hx
    obtain ⟨hx0,hx1⟩ := hmem x hx
    convert (kl_hasDerivAt hx0 hx1 hv hv1).sub
      ((((hasDerivAt_id x).sub_const v).pow 2).const_mul 2) using 1
    · rfl
    · dsimp [f']; ring
  have hd' : ∀ x ∈ Set.uIcc u v, HasDerivAt f' (f'' x) x := by
    intro x hx
    obtain ⟨hx0,hx1⟩ := hmem x hx
    convert (kl_logdiff_hasDerivAt hx0 hx1 hv hv1).sub
      (((hasDerivAt_id x).sub_const v).const_mul 4) using 1
    · rfl
    · simp [f'']
  have hconv : ConvexOn ℝ (Set.uIcc u v) f := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_uIcc u v)
      (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt)
      (fun x hx => (hd' x (interior_subset hx)).hasDerivWithinAt)
    intro x hx
    have hxm := hmem x (interior_subset hx)
    have hp : 0 < x*(1-x) := mul_pos hxm.1 (sub_pos.mpr hxm.2)
    apply sub_nonneg.mpr
    apply (le_div_iff₀ hp).2
    nlinarith [sq_nonneg (2*x-1)]
  have hvf : f v = 0 := by
    simp [f, klB, ne_of_gt hv, ne_of_gt (sub_pos.mpr hv1)]
  have hvf' : f' v = 0 := by
    simp [f', ne_of_gt hv, ne_of_gt (sub_pos.mpr hv1)]
  have hdv : HasDerivAt f 0 v := by simpa [hvf'] using hd v Set.right_mem_uIcc
  have hnonneg : 0 ≤ f u := by
    rcases lt_trichotomy v u with h | h | h
    · have hs := hconv.le_slope_of_hasDerivAt Set.right_mem_uIcc Set.left_mem_uIcc h hdv
      rw [slope_def_field, hvf] at hs
      have := (le_div_iff₀ (sub_pos.mpr h)).mp hs
      simpa using this
    · simp [← h, hvf]
    · have hs := hconv.slope_le_of_hasDerivAt Set.left_mem_uIcc Set.right_mem_uIcc h hdv
      rw [slope_def_field, hvf] at hs
      have := (div_le_iff₀ (sub_pos.mpr h)).mp hs
      linarith
  exact sub_nonneg.mp hnonneg

end Tier2Information

theorem pinsker_finite : ThresholdHC.Targets.pinsker_finite := by
  intro α _ P Q hP hQ hP1 hQ1
  classical
  let A : Finset α := Finset.univ.filter (fun a => Q a < P a)
  have hsumP := Finset.sum_add_sum_compl A P
  have hsumQ := Finset.sum_add_sum_compl A Q
  rw [hP1] at hsumP
  rw [hQ1] at hsumQ
  have habs : (∑ a, |P a-Q a|) =
      (∑ a ∈ A, (P a-Q a)) + (∑ a ∈ Aᶜ, (Q a-P a)) := by
    rw [← Finset.sum_add_sum_compl A]
    congr 1
    · apply Finset.sum_congr rfl
      intro a ha
      exact abs_of_nonneg (sub_nonneg.mpr ((Finset.mem_filter.mp ha).2.le))
    · apply Finset.sum_congr rfl
      intro a ha
      have hn : ¬Q a < P a := by
        simpa only [A, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and] using ha
      rw [abs_of_nonpos (sub_nonpos.mpr (not_lt.mp hn))]
      ring
  have htv : tvFT P Q = (∑ a ∈ A, P a) - ∑ a ∈ A, Q a := by
    unfold tvFT
    rw [habs, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    linarith
  by_cases hA : A.Nonempty
  · by_cases hAc : Aᶜ.Nonempty
    · have pA : 0 < ∑ a ∈ A, P a := Finset.sum_pos (fun a _ => hP a) hA
      have qA : 0 < ∑ a ∈ A, Q a := Finset.sum_pos (fun a _ => hQ a) hA
      have pAc : 0 < ∑ a ∈ Aᶜ, P a := Finset.sum_pos (fun a _ => hP a) hAc
      have qAc : 0 < ∑ a ∈ Aᶜ, Q a := Finset.sum_pos (fun a _ => hQ a) hAc
      have hbin := Tier2Information.binary_pinsker _ _ pA (by linarith) qA (by linarith)
      have hdp := kl_data_processing_finite α P Q A (fun a => (hP a).le)
        (fun a => (hQ a).le) (fun a ha => False.elim ((hQ a).ne' ha)) hP1 hQ1
      apply Real.le_sqrt_of_sq_le
      rw [htv]
      linarith
    · have hempty : Aᶜ = ∅ := Finset.not_nonempty_iff_eq_empty.mp hAc
      simp only [hempty, Finset.sum_empty, add_zero] at hsumP hsumQ
      rw [htv, hsumP, hsumQ, sub_self]
      exact Real.sqrt_nonneg _
  · have hempty : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    rw [htv, hempty]
    simp only [Finset.sum_empty, sub_self]
    exact Real.sqrt_nonneg _

end ThresholdHC.Proofs

