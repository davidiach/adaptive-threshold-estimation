import ThresholdHC.BandCostSelection.Compression

noncomputable section
open scoped Classical
namespace ThresholdHC.BandCostSelection

/-- Separated endpoint bounds certify the actual minimizer, including ties. -/
theorem interval_certificate {α : Type*} (F : Finset α) (value lower upper : α → ℝ)
    (hb : ∀ x ∈ F, lower x ≤ value x ∧ value x ≤ upper x)
    {chosen : α} (hc : chosen ∈ F)
    (hsep : ∀ x ∈ F, x ≠ chosen → upper chosen ≤ lower x) :
    ∀ x ∈ F, value chosen ≤ value x := by
  intro x hx
  by_cases he : x = chosen
  · simp [he]
  · exact (hb chosen hc).2.trans ((hsep x hx he).trans (hb x hx).1)

/-- Even when competing intervals overlap, the smallest lower and upper endpoints
enclose the true minimum, and the upper-endpoint witness remains feasible. -/
theorem interval_enclosure {α : Type*} (F : Finset α) (value lower upper : α → ℝ)
    (hb : ∀ x ∈ F, lower x ≤ value x ∧ value x ≤ upper x)
    {lo chosen optimum : α} (hc : chosen ∈ F) (ho : optimum ∈ F)
    (hlo : ∀ x ∈ F, lower lo ≤ lower x)
    (hopt : ∀ x ∈ F, value optimum ≤ value x) :
    lower lo ≤ value optimum ∧ value optimum ≤ upper chosen := by
  exact ⟨(hlo optimum ho).trans (hb optimum ho).1,
    (hopt chosen hc).trans (hb chosen hc).2⟩

end ThresholdHC.BandCostSelection

