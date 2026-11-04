import ThresholdHC.GenieRate.Full
noncomputable section
open MeasureTheory ThresholdHC.Tier6 ThresholdHC.StoppingProgram ThresholdHC.Genie ThresholdHC.GenieRate
open scoped ENNReal
variable (μ : Measure Gap) [IsProbabilityMeasure μ] {ρ B : ℝ}
variable (hr : 0 < ρ) (hu : ρ ≤ 1/2) (hb : 0 < B) (N : ℕ)
example (k : ℝ) (hk : 1 < k) (hn : B ≤ N*(1-1/k)^2*(k^2-1)) :
    programValue μ ρ B N ≤ ENNReal.ofReal k * genieValue μ ρ B N :=
  optimized_cap_factor μ hr hu hb hk N hn
example (hn : 4*B/3 ≤ N) :
    programValue μ ρ B N ≤ 2*genieValue μ ρ B N ∧
    ThresholdHC.RareAboveTwo.rareMinimaxRisk μ ρ B ≤ programValue μ ρ B N ∧
    programValue μ ρ B N ≤ 16*ThresholdHC.RareAboveTwo.rareMinimaxRisk μ ρ B :=
  linear_cap_risk_certificate μ hr hu hb N hn
example (t : ℝ) (ht : 0 < t) (ht' : t ≤ 1) (hn : B ≤ N*t^3) :
    programValue μ ρ B N ≤ ENNReal.ofReal (1+2*t)*genieValue μ ρ B N :=
  cubic_cap_factor μ hr hu hb ht ht' N hn
#print axioms ThresholdHC.Genie.genie_stopping_certificate
#print axioms ThresholdHC.GenieRate.cubic_cap_factor
#print axioms ThresholdHC.GenieRate.linear_cap_risk_certificate
#print axioms ThresholdHC.GenieRate.mixedReferences
#print axioms ThresholdHC.GenieRate.mixedReferences_admissible
#print axioms ThresholdHC.GenieRate.mixed_genie_price
#print axioms ThresholdHC.GenieRate.optimized_cap_factor
#print axioms ThresholdHC.GenieRate.regularized_reveal_word
#print axioms ThresholdHC.GenieRate.terminal_mass_work
#print axioms ThresholdHC.StoppingProgram.strong_four_prior_duality
