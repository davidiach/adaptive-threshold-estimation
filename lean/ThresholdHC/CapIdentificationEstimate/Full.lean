import ThresholdHC.CapIdentificationEstimate.Estimate

/-! The explicit lower estimate after Theorem `thm:cap-identifiability`
(paper/v6/appendix-identifiability.tex): when `1 ∉ V_L`, the residual
`h = 1 - proj_{V_L} 1` gives `Δ_N/2 ≥ ρ‖h‖²_{L²(μ)} / (4‖h‖_{L^∞(μ)})`.
This is a statement about the fixed-cap moment-matching diameter, not a floor
on unrestricted adaptive estimation with a growing cap. -/

noncomputable section
namespace ThresholdHC.CapIdentificationEstimate

/-- The explicit fixed-cap lower estimate `ExplicitCapEstimateStatement`. -/
theorem explicit_cap_estimate : ExplicitCapEstimateStatement := by
  intro μ _ ρ hρ hρ1 N hnot
  exact explicit_cap_estimate_of_not_mem μ ρ hρ hρ1 N hnot

end ThresholdHC.CapIdentificationEstimate
