import ThresholdHC.SharpRMS.GridArithmetic

namespace ThresholdHC.SharpRMS.Window

/-- The executable kernel computation and the algebraic rectangle definitions
give exactly the same sum, without any rounding performed in the reals. -/
theorem upperSum_rectangles (u : ℕ) :
    upperSum u = (List.range bins).foldl (fun acc i => acc+rectangleHeight (i+1) u biasDenominator) 0 := by
  rfl

private theorem fold_range (N : ℕ) (f : ℕ → ℕ) :
    (List.range N).foldl (fun acc i => acc+f i) 0 = ∑ i : Fin N, f i.val := by
  induction N with
  | zero => simp
  | succ N ih => simp [List.range_succ,List.foldl_append,ih,Fin.sum_univ_castSucc]

theorem upperSum_real (u : ℕ) :
    (∑ i : Fin bins, (rectangleHeight (i.val+1) u biasDenominator:ℝ)/(scale:ℝ))/(bins:ℝ) =
      (upperSum u:ℝ)/((bins:ℝ)*(scale:ℝ)) := by
  rw [upperSum_rectangles,fold_range,← Finset.sum_div,Nat.cast_sum]
  ring

end ThresholdHC.SharpRMS.Window
