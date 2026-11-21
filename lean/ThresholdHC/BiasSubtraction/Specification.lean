import ThresholdHC.ConfidenceLocalization.Obstruction
import ThresholdHC.ObservableSimulation.OriginalExperiment
import ThresholdHC.RareAboveTwo.Model

/-! Target statement for the remark "The bias subtraction cannot be uniformly
reduced" after Proposition prop:psi-null (v6, appendix on transfer foundations).

Proposition prop:psi-null bounds `J₀(b) ≥ sup_h (Ψ_{μ,ρ}(h) - 4b)_+² / (192h²)` for
`0 ≤ b ≤ ρ/64`. Here `J₀(b) ≥ J` is `NullVarianceObstruction μ p₀ p₁ ρ b J` with the
original coin parameters `1/2 ∓ d`, and `Ψ_{μ,ρ}(h)` is `rarePsi μ ρ h`. The remark
takes `ρ = 1/8`, `ε = 2^{-10}`, `μ = (1-ε)δ_{1/2} + εδ_d` and `b = ε(1-2d)/4`. With
`4b` replaced by `cb` for any fixed `c < 4`, and `192` by any `K > 0`, the bound
already fails at the single resolution `h = d` for every small enough gap `d`.
The proof is in `Witness.lean`. -/
noncomputable section
namespace ThresholdHC.BiasSubtraction
open MeasureTheory
open ThresholdHC.Tier6 ThresholdHC.ConfidenceLocalization ThresholdHC.ObservableSimulation
  ThresholdHC.RareAboveTwo

/-- The remark's law `(1-ε)δ_{1/2} + εδ_d` with `ε = 2^{-10}`. -/
def remarkLaw (d : Gap) : Measure Gap :=
  ENNReal.ofReal (1 - 1/2^10) • Measure.dirac ⟨1/2, by norm_num⟩ +
    ENNReal.ofReal (1/2^10) • Measure.dirac d

/-- The remark's bias level `b = ε(1-2d)/4` with `ε = 2^{-10}`. -/
def remarkBias (d : Gap) : ℝ := (1/2^10)*(1 - 2*(d : ℝ))/4

/-- Every bias level `b_d` lies in the range `0 ≤ b ≤ ρ/64` of Proposition
prop:psi-null at `ρ = 1/8`. For every `c < 4` and `K > 0`, once `d` is small
enough, `J₀(b_d) ≥ (Ψ(d) - c b_d)_+² / (K d²)` fails on the remark's law. -/
def BiasSubtractionStatement : Prop :=
  (∀ d : Gap, 0 ≤ remarkBias d ∧ remarkBias d ≤ (1/8)/64) ∧
  ∀ c : ℝ, c < 4 → ∀ K : ℝ, 0 < K → ∃ δ : ℝ, 0 < δ ∧ ∀ d : Gap, (d : ℝ) < δ →
    ¬ NullVarianceObstruction (remarkLaw d) (gapParameter false) (gapParameter true) (1/8)
      (remarkBias d)
      ((max ((rarePsi (remarkLaw d) (1/8) d).toReal - c*remarkBias d) 0)^2 /
        (K*(d : ℝ)^2))

end ThresholdHC.BiasSubtraction
