import ThresholdHC.FiniteSelectionApproximation.States

noncomputable section
open scoped Classical BigOperators
namespace ThresholdHC.FiniteSelectionApproximation
open ThresholdHC.BandCostSelection ThresholdHC.SelectionApproximation
open ThresholdHC.EntropyTailQuantile

variable {α : Type*}

/-- The approximate solver retains an actual feasible trace whose original cost
entropy, rather than its rounded summary, has the required relative error. -/
theorem retained_entropy (a saving : α → ℝ) (ha : ∀ x, 0 ≤ a x)
    (menus : List (Finset α)) (hm : 0 < menus.length)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hR : 1 ≤ maxCost a menus/minCost a menus)
    {xs : List α} (hx : xs ∈ enumerate menus) :
    let r := minCost a menus
    let M := cellCount menus.length (maxCost a menus/r) ε
    ∃ ys ∈ trimSolve (binKey r M) a (summary a r ε) saving menus,
      ys ∈ enumerate menus ∧ traceSaved saving xs ≤ traceSaved saving ys ∧
      multisetEntropy (traceKey a ys) ≤ (1+ε/2)*multisetEntropy (traceKey a xs) := by
  dsimp
  let r := minCost a menus
  let U := maxCost a menus
  let L := logScale (U/r)
  let M := cellCount menus.length (U/r) ε
  let η := (1+1/(M:ℝ))^menus.length-1
  have hr : 0 < r := minCost_pos a menus
  have hM : 0 < M := cellCount_pos hm hε
  have hMr : (0:ℝ)<M := Nat.cast_pos.mpr hM
  have hc : 1 ≤ 1+1/(M:ℝ) := by
    have : 0 ≤ 1/(M:ℝ) := by positivity
    linarith
  obtain ⟨ys,hy,hyfeas,hs,hA,hH⟩ := compression_invariant (binKey r M) a
    (summary a r ε) saving (1+1/(M:ℝ)) hc ha (summary_nonneg ha hε.le) (binKey_valid hr hM) menus xs hx
  refine ⟨ys,hy,hyfeas,hs,?_⟩
  rw [← traceEntropy a ys,← traceEntropy a xs]
  let v := fun i : Fin xs.length => a (xs.get i)
  let w := fun i : Fin ys.length => a (ys.get i)
  have hav : ∀ i, 0 ≤ v i := fun _ => ha _
  have haw : ∀ i, 0 ≤ w i := fun _ => ha _
  have hAc : Close (1+η) (costTotal v) (costTotal w) := by
    rw [traceTotal,traceTotal]
    simpa only [η,add_sub_cancel] using hA
  rcases trace_zero_or_lower ha hx with hz | hlo
  · have hzv : costTotal v = 0 := (traceTotal a xs).trans hz
    obtain ⟨hv,hw⟩ := entropy_zero_of_close hav haw hzv hAc
    change costEntropy w ≤ (1+ε/2)*costEntropy v
    rw [hv,hw,mul_zero]
  · have hlow : r ≤ traceSaved a ys := by
      rcases trace_zero_or_lower ha hyfeas with hz | h
      · have hp := hA.1
        rw [hz,mul_zero] at hp
        linarith
      · exact h
    obtain ⟨hη0,hη1,hsmall⟩ := compression_error hm (le_refl menus.length) hε hε1 (R := U/r)
    have hbv := trace_summary_bounds ha hx hε hε1 hR
    have hbw := trace_summary_bounds ha hyfeas hε hε1 hR
    change costEntropy w ≤ (1+ε/2)*costEntropy v
    apply entropy_relative v w hav haw hr (by have := logScale_ge_four (U/r); linarith)
      hε.le hη0 hη1 hsmall
      (by simpa only [v,traceTotal] using hlo) (by simpa only [v,traceTotal] using trace_le_maxCost (a := a) hx)
      (by simpa only [w,traceTotal] using hlow) (by simpa only [w,traceTotal] using trace_le_maxCost (a := a) hyfeas)
      (logScale_derivative hR) hbv.1 (by simpa only [v,traceTotal] using hbv.2.1)
      hbw.1 (by simpa only [w,traceTotal] using hbw.2.1)
      (trace_nonneg (summary_nonneg ha hε.le) xs)
      (by simpa only [v,traceTotal] using hbv.2.2.2) hAc
      (by simpa only [η,add_sub_cancel] using hH)

/-- Entropy error and improved saving imply a `β` comparison for the original
capped objective. No rounded entropy is evaluated in this conclusion. -/
theorem capped_objective_comparison {ρ B ε G H T V : ℝ}
    (hρ : 0 ≤ ρ) (hB : 0 < B) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hG : 0 ≤ G) (hH : H ≤ (1+ε/2)*G) (hT : 0 ≤ T) (hV : V ≤ T) :
    min ρ (1/Real.sqrt B * Real.sqrt (ρ*H)+V) ≤
      beta ε * min ρ (1/Real.sqrt B * Real.sqrt (ρ*G)+T) := by
  obtain ⟨hb,hb2,hbG⟩ := beta_bounds hε hε1
  have hs : Real.sqrt (ρ*H) ≤ beta ε * Real.sqrt (ρ*G) := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨mul_nonneg (by linarith) (Real.sqrt_nonneg _),?_⟩
    rw [mul_pow,Real.sq_sqrt (mul_nonneg hρ hG)]
    have hHG := mul_le_mul_of_nonneg_right hbG hG
    nlinarith [mul_le_mul_of_nonneg_left (hH.trans hHG) hρ]
  have hprice := mul_le_mul_of_nonneg_left hs (show 0 ≤ 1/Real.sqrt B by positivity)
  have htail : V ≤ beta ε*T := hV.trans (by nlinarith [mul_nonneg (sub_nonneg.mpr hb.le) hT])
  have hsum : 1/Real.sqrt B*Real.sqrt (ρ*H)+V ≤
      beta ε*(1/Real.sqrt B*Real.sqrt (ρ*G)+T) := by nlinarith only [hprice,htail]
  by_cases hc : ρ ≤ 1/Real.sqrt B*Real.sqrt (ρ*G)+T
  · rw [min_eq_left hc]
    exact (min_le_left _ _).trans (by nlinarith [mul_nonneg (sub_nonneg.mpr hb.le) hρ])
  · rw [min_eq_right (le_of_not_ge hc)]
    exact (min_le_right _ _).trans hsum

end ThresholdHC.FiniteSelectionApproximation
